// ============================================================
// RFID DEPLOYMENT SIMULATION — Full Factory 3D Engine
// 15 Readers • 11 Tanks • 3 Zones • Process Flow Animation
// All measurements in FEET (1 unit = 1 foot)
// ============================================================
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { CSS2DRenderer, CSS2DObject } from 'three/addons/renderers/CSS2DRenderer.js';

// ============================================================
//  CONFIGURATION
// ============================================================
const FT = 1; // 1 unit = 1 foot
const M_TO_FT = 3.28084;
const TANK_W = 4.92 * FT;   // 1.5 m width
const TANK_L = 49.21 * FT;  // 15 m length
const TANK_H = 4.0 * FT;    // height
const TANK_THICK = 0.2;
const LIQUID_LEVEL = 0.82;

// Layout origin: x=0 is left edge of Area 1
const LAYOUT = {
    // Area 1: Wall-mounted readers on stands
    area1_readers: [
        { id: 1, x: 0 },
        { id: 2, x: 3.5 },
        { id: 3, x: 7.0 },
        { id: 4, x: 10.5 }
    ],
    area1_standH: 7,
    area1_wallZ: -58.6,    // 1 ft behind readers (back wall)
    area1_readerZ: -57.6,  // 10 ft from jig back tag (which is at -47.6)

    // Degrease tank + Reader 5
    degrease: { id: 'degrease', label: 'DEGREASE', x: 18, readerId: 5, liqColor: 0x8899aa, tankColor: 0x6a7a7e },

    // Enclosure tanks + Readers 6-11 (5 ft gap from degrease)
    enclosure: {
        startX: 25.5,
        gap: 0.5,
        deviceToTank: 2.5,
        tanks: [
            { id: 'acid1',  label: 'ACID 1',  readerId: 6,  liqColor: 0x22cc55 },
            { id: 'acid2',  label: 'ACID 2',  readerId: 7,  liqColor: 0x22cc55 },
            { id: 'acid3',  label: 'ACID 3',  readerId: 8,  liqColor: 0x22cc55 },
            { id: 'rinse1', label: 'RINSE 1', readerId: 9,  liqColor: 0x4499dd },
            { id: 'rinse2', label: 'RINSE 2', readerId: 10, liqColor: 0x4499dd },
            { id: 'flux',   label: 'FLUX',    readerId: 11, liqColor: 0xcc9933 }
        ]
    },

    // Area 3 tanks + Readers 12-15 (gaps: 10, 7, 5, 4 ft)
    area3: [
        { id: 'dryer',     label: 'DRYER',     readerId: 12, liqColor: 0xaa7744, gapBefore: 10 },
        { id: 'zinc',      label: 'ZINC',      readerId: 13, liqColor: 0x88aacc, gapBefore: 7 },
        { id: 'quenching', label: 'QUENCHING', readerId: 14, liqColor: 0x55bb88, gapBefore: 5 },
        { id: 'dichrom',   label: 'DICHROM',   readerId: 15, liqColor: 0xaa55aa, gapBefore: 4 }
    ],
    area3_deviceToTank: 3.5
};

// Process sequence for simulation
const PROCESS_STEPS = [
    { name: 'Jig Detection', tank: null, readers: [1,2,3,4], dipTime: 0, type: 'detect' },
    { name: 'Degrease',  tank: 'degrease',  readers: [5],  dipTime: 30, type: 'dip' },
    { name: 'Acid 1',    tank: 'acid1',     readers: [6],  dipTime: 45, type: 'dip' },
    { name: 'Acid 2',    tank: 'acid2',     readers: [7],  dipTime: 45, type: 'dip' },
    { name: 'Acid 3',    tank: 'acid3',     readers: [8],  dipTime: 45, type: 'dip' },
    { name: 'Rinse 1',   tank: 'rinse1',    readers: [9],  dipTime: 20, type: 'dip' },
    { name: 'Rinse 2',   tank: 'rinse2',    readers: [10], dipTime: 20, type: 'dip' },
    { name: 'Flux',      tank: 'flux',      readers: [11], dipTime: 30, type: 'dip' },
    { name: 'Dryer',     tank: 'dryer',     readers: [12], dipTime: 60, type: 'dip' },
    { name: 'Zinc',      tank: 'zinc',      readers: [13], dipTime: 90, type: 'dip' },
    { name: 'Quenching', tank: 'quenching', readers: [14], dipTime: 15, type: 'dip' },
    { name: 'Dichrom',   tank: 'dichrom',   readers: [15], dipTime: 30, type: 'dip' }
];

// ============================================================
//  GLOBALS
// ============================================================
let scene, camera, renderer, labelRenderer, controls, clock;
let rfSignalGroup, measureGroup, labelGroup;
let tankMeshes = {};   // id -> Group
let readerMeshes = {}; // id -> Group
let readerLEDs = {};   // id -> Mesh
let tankPositions = {};// id -> {x, z}
let enclosureGroup;
let jigGroup, jigRod, jigTag, jigChain1, jigChain2;
let overheadRail;

// UI state
let isMetric = false;
let showSignal = true, showMeasurements = true, showLabels = true, xrayMode = false;
let zone1LabelGroup, zone2LabelGroup, zone3LabelGroup;

// Simulation state
let simRunning = false, simPaused = false;
let simStep = -1, simPhase = 'idle'; // phases: idle, moving, lowering, dipping, raising
let simTimer = 0, simSpeed = 5;
let jigY = 15, jigTargetX = 0;
const JIG_RAIL_Y = 15;
const JIG_DIP_Y = 1.5;

// Live RFID Hardware Mode state
let liveModeActive = false;
let livePollInterval = null;
let liveActiveReaderId = null; // 1 to 15
let liveActiveEPC = '';
let liveActiveRSSI = 'N/A';
let liveDwellTimer = 0;
let liveStabilizationTimer = 0;
let liveStabilizationActive = false;
let liveGracePeriods = 0;
let livePrevTagData = {}; // Stores epc -> { lt, rc } for differential tracking
const STABILIZATION_DELAY = 10.0; // 10 seconds delay as required
const LIVE_SERVER_URL = 'http://127.0.0.1:12345/';

// Computed layout positions
let layoutData = { readers: {}, tanks: {} };
let centerX = 0;

// ============================================================
//  INIT
// ============================================================
function init() {
    clock = new THREE.Clock();
    computeLayout();

    scene = new THREE.Scene();
    scene.background = new THREE.Color(0xdce8f2);
    scene.fog = new THREE.FogExp2(0xdce8f2, 0.003);

    camera = new THREE.PerspectiveCamera(50, window.innerWidth / window.innerHeight, 0.1, 500);
    camera.position.set(centerX, 55, 70);

    renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.0;
    renderer.outputColorSpace = THREE.SRGBColorSpace;
    document.getElementById('canvas-container').appendChild(renderer.domElement);

    labelRenderer = new CSS2DRenderer();
    labelRenderer.setSize(window.innerWidth, window.innerHeight);
    labelRenderer.domElement.style.position = 'absolute';
    labelRenderer.domElement.style.top = '0';
    labelRenderer.domElement.style.left = '0';
    labelRenderer.domElement.style.pointerEvents = 'none';
    document.getElementById('label-container').appendChild(labelRenderer.domElement);

    controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.07;
    controls.minDistance = 5;
    controls.maxDistance = 200;
    controls.maxPolarAngle = Math.PI * 0.48;
    controls.target.set(centerX, 2, -10);
    controls.update();

    rfSignalGroup = new THREE.Group(); rfSignalGroup.name = 'rfSignals'; scene.add(rfSignalGroup);
    measureGroup = new THREE.Group(); measureGroup.name = 'measurements'; scene.add(measureGroup);
    labelGroup = new THREE.Group(); labelGroup.name = 'labels'; scene.add(labelGroup);

    // Initialize zone labels groups as children of the main label group
    zone1LabelGroup = new THREE.Group(); zone1LabelGroup.name = 'zone1Labels'; labelGroup.add(zone1LabelGroup);
    zone2LabelGroup = new THREE.Group(); zone2LabelGroup.name = 'zone2Labels'; labelGroup.add(zone2LabelGroup);
    zone3LabelGroup = new THREE.Group(); zone3LabelGroup.name = 'zone3Labels'; labelGroup.add(zone3LabelGroup);

    buildLighting();
    buildFactory();
    buildArea1();
    buildDegrease();
    buildEnclosure();
    buildArea3();
    buildOverheadRail();
    buildJig();
    buildAllRFSignals();
    buildKeyMeasurements();
    buildAreaLabels();

    window.addEventListener('resize', onResize);
    document.addEventListener('keydown', onKeyDown);
    setupUI();

    setTimeout(() => {
        const ls = document.getElementById('loading-screen');
        ls.classList.add('fade-out');
        setTimeout(() => ls.style.display = 'none', 800);
    }, 2800);

    animate();
}

// ============================================================
//  COMPUTE LAYOUT POSITIONS
// ============================================================
function computeLayout() {
    // Area 1 readers
    LAYOUT.area1_readers.forEach(r => {
        layoutData.readers[r.id] = { x: r.x, z: LAYOUT.area1_readerZ, y: LAYOUT.area1_standH };
    });

    // Degrease
    const dg = LAYOUT.degrease;
    layoutData.tanks[dg.id] = { x: dg.x, z: 0 };
    layoutData.readers[dg.readerId] = { x: dg.x, z: 5, y: 7 };

    // Enclosure tanks
    let ex = LAYOUT.enclosure.startX;
    LAYOUT.enclosure.tanks.forEach((t, i) => {
        const cx = ex + TANK_W / 2;
        layoutData.tanks[t.id] = { x: cx, z: 0 };
        layoutData.readers[t.readerId] = { x: cx, z: LAYOUT.enclosure.deviceToTank, y: 7 };
        ex += TANK_W + LAYOUT.enclosure.gap;
    });
    const enclosureEndX = ex - LAYOUT.enclosure.gap;

    // Area 3 tanks
    let a3x = enclosureEndX;
    LAYOUT.area3.forEach(t => {
        a3x += t.gapBefore;
        const cx = a3x + TANK_W / 2;
        layoutData.tanks[t.id] = { x: cx, z: 0 };
        layoutData.readers[t.readerId] = { x: cx, z: LAYOUT.area3_deviceToTank, y: 7 };
        a3x += TANK_W;
    });

    // Compute center for camera
    const allX = Object.values(layoutData.tanks).map(t => t.x).concat(Object.values(layoutData.readers).map(r => r.x));
    centerX = (Math.min(...allX) + Math.max(...allX)) / 2;
}

// ============================================================
//  LIGHTING
// ============================================================
function buildLighting() {
    scene.add(new THREE.AmbientLight(0xffffff, 0.7));

    const hemi = new THREE.HemisphereLight(0xffffff, 0xcceeff, 0.8);
    hemi.position.set(0, 50, 0);
    scene.add(hemi);

    const dir = new THREE.DirectionalLight(0xfffae6, 1.8);
    dir.position.set(centerX + 40, 60, 40);
    dir.castShadow = true;
    dir.shadow.mapSize.set(2048, 2048);
    dir.shadow.camera.left = -80; dir.shadow.camera.right = 80;
    dir.shadow.camera.top = 60; dir.shadow.camera.bottom = -60;
    dir.shadow.camera.near = 1; dir.shadow.camera.far = 150;
    dir.shadow.bias = -0.001;
    scene.add(dir);

    scene.add(new THREE.DirectionalLight(0xddf0ff, 0.6).translateX(-30).translateY(20));

    // Overhead factory lights along the line
    for (let x = -5; x <= 115; x += 15) {
        const pl = new THREE.PointLight(0xffffee, 0.4, 40, 1.5);
        pl.position.set(x, 18, -15);
        scene.add(pl);
        const bulb = new THREE.Mesh(new THREE.SphereGeometry(0.2, 6, 6), new THREE.MeshBasicMaterial({ color: 0xffffff }));
        bulb.position.copy(pl.position);
        scene.add(bulb);
    }
}

// ============================================================
//  FACTORY ENVIRONMENT
// ============================================================
function buildFactory() {
    const floorW = 150, floorD = 80;
    const floor = new THREE.Mesh(
        new THREE.PlaneGeometry(floorW, floorD),
        new THREE.MeshStandardMaterial({ color: 0xd0d5db, roughness: 0.9, metalness: 0.05 })
    );
    floor.rotation.x = -Math.PI / 2;
    floor.position.set(centerX, 0, -floorD / 2 + 15);
    floor.receiveShadow = true;
    scene.add(floor);

    const grid = new THREE.GridHelper(floorW, floorW / 2, 0xa0aab5, 0xb0bac5);
    grid.position.set(centerX, 0.01, -floorD / 2 + 15);
    grid.material.opacity = 0.35; grid.material.transparent = true;
    scene.add(grid);

    // Back wall
    const wallMat = new THREE.MeshStandardMaterial({ color: 0xeeeeee, roughness: 0.85, metalness: 0.1 });
    const bw = new THREE.Mesh(new THREE.PlaneGeometry(floorW, 20), wallMat);
    bw.position.set(centerX, 10, -floorD + 15);
    bw.receiveShadow = true;
    scene.add(bw);

    // Left wall
    const lw = new THREE.Mesh(new THREE.PlaneGeometry(floorD, 20), wallMat);
    lw.position.set(centerX - floorW / 2, 10, -floorD / 2 + 15);
    lw.rotation.y = Math.PI / 2;
    scene.add(lw);

    // Ceiling beams
    const beamMat = new THREE.MeshStandardMaterial({ color: 0xa0a4a8, roughness: 0.6, metalness: 0.5 });
    for (let x = centerX - 60; x <= centerX + 60; x += 20) {
        const beam = new THREE.Mesh(new THREE.BoxGeometry(0.4, 0.6, floorD), beamMat);
        beam.position.set(x, 19, -floorD / 2 + 15);
        scene.add(beam);
    }

    // Safety floor markings
    const safeMat = new THREE.MeshBasicMaterial({ color: 0xd4a017, transparent: true, opacity: 0.5 });
    const stripe = new THREE.Mesh(new THREE.PlaneGeometry(120, 0.12), safeMat);
    stripe.rotation.x = -Math.PI / 2;
    stripe.position.set(centerX, 0.015, 8);
    scene.add(stripe);
    const stripe2 = stripe.clone();
    stripe2.position.z = -55;
    scene.add(stripe2);
}

// ============================================================
//  REUSABLE: CREATE TANK
// ============================================================
function createTank(id, x, label, liqColor) {
    const g = new THREE.Group();
    g.name = `tank_${id}`;
    const steelMat = new THREE.MeshStandardMaterial({ color: 0x6a7a7e, roughness: 0.35, metalness: 0.85 });
    const w = TANK_W, l = TANK_L, h = TANK_H, t = TANK_THICK;

    // Bottom
    g.add(makeMesh(new THREE.BoxGeometry(w, t, l), steelMat, 0, t / 2, -l / 2));
    // Front wall (z=0 side)
    g.add(makeMesh(new THREE.BoxGeometry(w, h, t), steelMat, 0, h / 2 + t, 0));
    // Back wall
    g.add(makeMesh(new THREE.BoxGeometry(w, h, t), steelMat, 0, h / 2 + t, -l));
    // Left wall
    g.add(makeMesh(new THREE.BoxGeometry(t, h, l), steelMat, -w / 2 + t / 2, h / 2 + t, -l / 2));
    // Right wall
    g.add(makeMesh(new THREE.BoxGeometry(t, h, l), steelMat, w / 2 - t / 2, h / 2 + t, -l / 2));

    // Liquid
    const lh = (h - t) * LIQUID_LEVEL;
    const liquidMat = new THREE.MeshPhysicalMaterial({
        color: liqColor, transparent: true, opacity: 0.45,
        roughness: 0.1, metalness: 0, transmission: 0.25, thickness: 1.5, side: THREE.DoubleSide
    });
    g.add(makeMesh(new THREE.BoxGeometry(w - t * 2, lh, l - t * 2), liquidMat, 0, t + lh / 2, -l / 2));

    // Liquid surface glow
    const surfMat = new THREE.MeshBasicMaterial({ color: liqColor, transparent: true, opacity: 0.12, side: THREE.DoubleSide });
    const surf = makeMesh(new THREE.PlaneGeometry(w - t * 2, l - t * 2), surfMat, 0, t + lh + 0.01, -l / 2);
    surf.rotation.x = -Math.PI / 2;
    surf.name = 'surface_' + id;
    g.add(surf);

    // Rim
    const rimMat = new THREE.MeshStandardMaterial({ color: 0x555f63, roughness: 0.3, metalness: 0.9 });
    const rh = 0.12, rw = 0.2;
    g.add(makeMesh(new THREE.BoxGeometry(w + rw, rh, rw), rimMat, 0, h + t + rh / 2, 0));
    g.add(makeMesh(new THREE.BoxGeometry(w + rw, rh, rw), rimMat, 0, h + t + rh / 2, -l));
    g.add(makeMesh(new THREE.BoxGeometry(rw, rh, l + rw), rimMat, -w / 2, h + t + rh / 2, -l / 2));
    g.add(makeMesh(new THREE.BoxGeometry(rw, rh, l + rw), rimMat, w / 2, h + t + rh / 2, -l / 2));

    g.position.set(x, 0, 0);
    scene.add(g);
    tankMeshes[id] = g;
    tankPositions[id] = { x, z: -l / 2 }; // center of tank for jig positioning

    // No longer creating 3D timer label above the tanks as they are shown in the bottom SCADA HMI panel

    return g;
}

function makeMesh(geo, mat, x, y, z) {
    const m = new THREE.Mesh(geo, mat);
    m.position.set(x, y, z);
    m.castShadow = true; m.receiveShadow = true;
    return m;
}

// ============================================================
//  REUSABLE: CREATE READER ON STAND
// ============================================================
function createReader(id, x, z, standH) {
    const g = new THREE.Group();
    g.name = `reader_${id}`;
    
    // Materials
    const poleMat = new THREE.MeshStandardMaterial({ color: 0x4a5258, roughness: 0.4, metalness: 0.7 });
    const antMat = new THREE.MeshStandardMaterial({ color: 0xf4f6f9, roughness: 0.2, metalness: 0.1 });
    const bracketMat = new THREE.MeshStandardMaterial({ color: 0xb0b5ba, roughness: 0.3, metalness: 0.85 });
    const pcbMat = new THREE.MeshStandardMaterial({ color: 0x116633, roughness: 0.6, metalness: 0.15 });
    const chipMat = new THREE.MeshStandardMaterial({ color: 0x111111, roughness: 0.6, metalness: 0.2 });
    const silionMat = new THREE.MeshStandardMaterial({ color: 0xc0c5ca, roughness: 0.25, metalness: 0.7 });
    const ribbonMat = new THREE.MeshStandardMaterial({ color: 0xeeeeee, roughness: 0.8, metalness: 0.0 });
    const connectorMat = new THREE.MeshStandardMaterial({ color: 0x222222, roughness: 0.5, metalness: 0.3 });
    const ethMat = new THREE.MeshStandardMaterial({ color: 0xdddddd, roughness: 0.4, metalness: 0.5 });
    const stickerMat = new THREE.MeshStandardMaterial({ color: 0xf0f0f0, roughness: 0.9, metalness: 0.0 });

    // 1. Base plate & Pole
    g.add(makeMesh(new THREE.CylinderGeometry(0.5, 0.6, 0.15, 12), poleMat, 0, 0.075, 0));
    g.add(makeMesh(new THREE.CylinderGeometry(0.08, 0.08, standH - 0.15, 8), poleMat, 0, standH / 2, 0));
    
    // 2. White Square Antenna Panel (front face)
    const antSize = 0.9;
    const antThick = 0.08;
    const ant = makeMesh(new THREE.BoxGeometry(antSize, antSize, antThick), antMat, 0, standH, 0);
    ant.name = 'antenna_' + id;
    g.add(ant);
    
    // 3. Center circular indentation on the front
    const indentMat = new THREE.MeshStandardMaterial({ color: 0xe8ecef, roughness: 0.4, metalness: 0.1 });
    const indent = makeMesh(new THREE.CylinderGeometry(0.15, 0.15, antThick + 0.005, 16), indentMat, 0, standH, 0);
    indent.rotation.x = Math.PI / 2;
    g.add(indent);

    // 4. Large Aluminum Backplate (mounting plate for modules)
    const bpW = 0.85, bpH = 0.85, bpT = 0.025;
    const backplate = makeMesh(new THREE.BoxGeometry(bpW, bpH, bpT), bracketMat, 0, standH, antThick / 2 + bpT / 2);
    g.add(backplate);

    // Mounting holes (visual detail)
    const holeMat = new THREE.MeshStandardMaterial({ color: 0x333333, roughness: 0.7, metalness: 0.3 });
    const holeGeo = new THREE.CylinderGeometry(0.015, 0.015, bpT + 0.01, 8);
    [[-0.32, 0.32], [0.32, 0.32], [-0.32, -0.32], [0.32, -0.32], [0, 0.32], [0, -0.32]].forEach(([hx, hy]) => {
        const hole = makeMesh(holeGeo, holeMat, hx, standH + hy, antThick / 2 + bpT / 2);
        hole.rotation.x = Math.PI / 2;
        g.add(hole);
    });

    // 5. SILION SIM7100 Reader Module (silver box, left side of backplate)
    const silW = 0.28, silH = 0.2, silT = 0.05;
    const silZ = antThick / 2 + bpT + silT / 2;
    const silion = makeMesh(new THREE.BoxGeometry(silW, silH, silT), silionMat, -0.2, standH + 0.05, silZ);
    g.add(silion);
    // SILION label sticker
    const stickerGeo = new THREE.PlaneGeometry(0.18, 0.08);
    const sticker = new THREE.Mesh(stickerGeo, stickerMat);
    sticker.position.set(-0.2, standH + 0.05, silZ + silT / 2 + 0.001);
    g.add(sticker);
    // QR code on sticker
    const qrMat = new THREE.MeshStandardMaterial({ color: 0x333333, roughness: 0.9, metalness: 0 });
    const qr = makeMesh(new THREE.PlaneGeometry(0.04, 0.04), qrMat, -0.16, standH + 0.05, silZ + silT / 2 + 0.002);
    g.add(qr);
    // Connector port on SILION
    g.add(makeMesh(new THREE.BoxGeometry(0.12, 0.04, 0.015), connectorMat, -0.2, standH - 0.02, silZ + silT / 2 - 0.005));

    // 6. SDL1010 PCB Board (green board, right side of backplate)
    const pcbW = 0.3, pcbH = 0.25, pcbT = 0.02;
    const pcbZ = antThick / 2 + bpT + pcbT / 2;
    const pcb = makeMesh(new THREE.BoxGeometry(pcbW, pcbH, pcbT), pcbMat, 0.18, standH, pcbZ);
    g.add(pcb);
    // Main IC chip on PCB
    g.add(makeMesh(new THREE.BoxGeometry(0.06, 0.06, 0.01), chipMat, 0.12, standH + 0.04, pcbZ + pcbT / 2 + 0.005));
    // Secondary chip
    g.add(makeMesh(new THREE.BoxGeometry(0.04, 0.04, 0.008), chipMat, 0.22, standH + 0.04, pcbZ + pcbT / 2 + 0.004));
    // Ethernet port (silver box)
    g.add(makeMesh(new THREE.BoxGeometry(0.07, 0.06, 0.06), ethMat, 0.3, standH + 0.02, pcbZ));
    // Green terminal block
    const termMat = new THREE.MeshStandardMaterial({ color: 0x22aa44, roughness: 0.6, metalness: 0.2 });
    g.add(makeMesh(new THREE.BoxGeometry(0.06, 0.04, 0.04), termMat, 0.3, standH - 0.06, pcbZ));
    // Capacitors / small components
    const capMat = new THREE.MeshStandardMaterial({ color: 0x665544, roughness: 0.7, metalness: 0.1 });
    for (let i = 0; i < 4; i++) {
        g.add(makeMesh(new THREE.CylinderGeometry(0.008, 0.008, 0.015, 6), capMat, 0.1 + i * 0.05, standH - 0.06, pcbZ + pcbT / 2 + 0.007));
    }
    // PCB label sticker
    const pcbLabel = new THREE.Mesh(new THREE.PlaneGeometry(0.1, 0.04), stickerMat);
    pcbLabel.position.set(0.18, standH - 0.02, pcbZ + pcbT / 2 + 0.001);
    g.add(pcbLabel);

    // 7. Ribbon Cable connecting SILION to SDL1010
    const ribbonW = 0.08, ribbonH = 0.015;
    const ribbonLen = 0.22;
    const ribbon = makeMesh(new THREE.BoxGeometry(ribbonLen, ribbonH, 0.004), ribbonMat, 0, standH + 0.05, silZ - 0.01);
    g.add(ribbon);
    // Ribbon connectors at each end
    g.add(makeMesh(new THREE.BoxGeometry(0.03, 0.025, 0.012), connectorMat, -0.08, standH + 0.05, silZ - 0.01));
    g.add(makeMesh(new THREE.BoxGeometry(0.03, 0.025, 0.012), connectorMat, 0.08, standH + 0.05, silZ - 0.01));

    // 8. Status LED (visible for simulation feedback)
    const led = new THREE.Mesh(new THREE.SphereGeometry(0.035, 8, 8), new THREE.MeshBasicMaterial({ color: 0x22ff66 }));
    led.position.set(antSize / 2 - 0.1, standH + antSize / 2 - 0.1, -antThick / 2);
    led.name = 'led_' + id;
    g.add(led);
    readerLEDs[id] = led;

    // 9. Detection flash ring (invisible by default, lights up on detection)
    const flashGeo = new THREE.RingGeometry(0.35, 0.48, 24);
    const flashMat = new THREE.MeshBasicMaterial({ color: 0xff3300, transparent: true, opacity: 0, side: THREE.DoubleSide });
    const flash = new THREE.Mesh(flashGeo, flashMat);
    flash.position.set(0, standH, -antThick / 2 - 0.01);
    flash.name = 'flash_' + id;
    g.add(flash);

    g.position.set(x, 0, z);
    scene.add(g);
    readerMeshes[id] = g;
    return g;
}

// ============================================================
//  AREA 1: WALL MOUNTED READERS (1-4) + JIG AREA
// ============================================================
function buildArea1() {
    // Readers on stands
    LAYOUT.area1_readers.forEach(r => {
        createReader(r.id, r.x, LAYOUT.area1_readerZ, LAYOUT.area1_standH);
    });

    // Standard Wall directly behind the readers
    const wallGeo = new THREE.PlaneGeometry(24, 14);
    const wallMat = new THREE.MeshStandardMaterial({ color: 0xe0e5ea, roughness: 0.8, metalness: 0.15 });
    const wall = new THREE.Mesh(wallGeo, wallMat);
    wall.position.set(5.25, 7, LAYOUT.area1_wallZ);
    wall.receiveShadow = true;
    scene.add(wall);

    // Jig approach markers on floor
    const markerMat = new THREE.MeshBasicMaterial({ color: 0x3b82f6, transparent: true, opacity: 0.3 });
    for (let i = 0; i < 4; i++) {
        const marker = new THREE.Mesh(new THREE.PlaneGeometry(1.5, 8), markerMat);
        marker.rotation.x = -Math.PI / 2;
        marker.position.set(LAYOUT.area1_readers[i].x, 0.02, 5);
        scene.add(marker);
    }

    // "JIG IN AREA" floor label
    addLabel('⬆ JIG IN AREA', 5.25, 0.3, 10, 'area-label', zone1LabelGroup);
}

// ============================================================
//  DEGREASE SECTION (READER 5)
// ============================================================
function buildDegrease() {
    const dg = LAYOUT.degrease;
    createTank(dg.id, dg.x, dg.label, dg.liqColor);
    createReader(dg.readerId, dg.x, 5, 7);

    // Glass barrier between reader 5 and degrease tank
    const glassMat = new THREE.MeshPhysicalMaterial({
        color: 0x88ccff, transparent: true, opacity: 0.1,
        roughness: 0.05, transmission: 0.9, thickness: 0.3,
        clearcoat: 1.0, side: THREE.DoubleSide, depthWrite: false
    });
    const glass = new THREE.Mesh(new THREE.PlaneGeometry(TANK_W + 1, 8), glassMat);
    glass.position.set(dg.x, 4, 2.5);
    scene.add(glass);

    addLabel('🧪 DEGREASE', dg.x, TANK_H + 1, -2, 'tank-label', zone2LabelGroup);
    addLabel('📡 Reader #5', dg.x, 8, 5, 'reader-label', zone2LabelGroup);
}

// ============================================================
//  ENCLOSURE AREA (READERS 6-11, TANKS INSIDE)
// ============================================================
function buildEnclosure() {
    enclosureGroup = new THREE.Group();
    enclosureGroup.name = 'Enclosure';

    const tanks = LAYOUT.enclosure.tanks;
    let ex = LAYOUT.enclosure.startX;
    const tankCenters = [];

    tanks.forEach((t, i) => {
        const cx = ex + TANK_W / 2;
        tankCenters.push(cx);
        createTank(t.id, cx, t.label, t.liqColor);
        createReader(t.readerId, cx, LAYOUT.enclosure.deviceToTank, 7);
        addLabel(`🧪 ${t.label}`, cx, TANK_H + 1, -2, 'tank-label', zone2LabelGroup);
        addLabel(`📡 #${t.readerId}`, cx, 8, LAYOUT.enclosure.deviceToTank, 'reader-label', zone2LabelGroup);
        ex += TANK_W + LAYOUT.enclosure.gap;
    });

    const encEndX = ex - LAYOUT.enclosure.gap;
    const encStartX = LAYOUT.enclosure.startX;
    const encW = encEndX - encStartX;
    const encCX = encStartX + encW / 2;
    const encH = 9;
    const ft = 0.2;

    const frameMat = new THREE.MeshStandardMaterial({ color: 0x90959a, roughness: 0.4, metalness: 0.8 });

    // Vertical corner posts
    const corners = [
        [encStartX, 0],  [encEndX, 0],
        [encStartX, -TANK_L], [encEndX, -TANK_L]
    ];
    corners.forEach(([cx, cz]) => {
        enclosureGroup.add(makeMesh(new THREE.BoxGeometry(ft, encH, ft), frameMat, cx, encH / 2, cz));
    });

    // Horizontal top frame
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(encW, ft, ft), frameMat, encCX, encH, 0));
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(encW, ft, ft), frameMat, encCX, encH, -TANK_L));
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(ft, ft, TANK_L), frameMat, encStartX, encH, -TANK_L / 2));
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(ft, ft, TANK_L), frameMat, encEndX, encH, -TANK_L / 2));

    // Bottom frame
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(encW, ft * 0.6, ft * 0.6), frameMat, encCX, ft * 0.3, 0));
    enclosureGroup.add(makeMesh(new THREE.BoxGeometry(encW, ft * 0.6, ft * 0.6), frameMat, encCX, ft * 0.3, -TANK_L));

    // Glass panel — FRONT side (z=0 side, facing readers)
    const glassMat = new THREE.MeshPhysicalMaterial({
        color: 0x88ccff, transparent: true, opacity: 0.1,
        roughness: 0.05, transmission: 0.9, thickness: 0.4,
        clearcoat: 1.0, side: THREE.DoubleSide, depthWrite: false
    });
    const glass = new THREE.Mesh(new THREE.PlaneGeometry(encW, encH - 0.5), glassMat);
    glass.position.set(encCX, encH / 2, 0.1);
    glass.name = 'enclosureGlass';
    enclosureGroup.add(glass);

    // Glass edge highlight
    const glassEdge = new THREE.LineSegments(
        new THREE.EdgesGeometry(new THREE.PlaneGeometry(encW, encH - 0.5)),
        new THREE.LineBasicMaterial({ color: 0x44aadd, transparent: true, opacity: 0.25 })
    );
    glassEdge.position.copy(glass.position);
    enclosureGroup.add(glassEdge);

    // Side mesh panels (semi-transparent)
    const meshMat = new THREE.MeshStandardMaterial({
        color: 0xb0b5ba, transparent: true, opacity: 0.25, side: THREE.DoubleSide, depthWrite: false
    });
    const sidePanelGeo = new THREE.PlaneGeometry(TANK_L, encH - 0.5);
    const lp = new THREE.Mesh(sidePanelGeo, meshMat);
    lp.position.set(encStartX, encH / 2, -TANK_L / 2); lp.rotation.y = Math.PI / 2;
    enclosureGroup.add(lp);
    const rp = new THREE.Mesh(sidePanelGeo, meshMat);
    rp.position.set(encEndX, encH / 2, -TANK_L / 2); rp.rotation.y = Math.PI / 2;
    enclosureGroup.add(rp);

    // Back panel
    const bp = new THREE.Mesh(new THREE.PlaneGeometry(encW, encH - 0.5), meshMat);
    bp.position.set(encCX, encH / 2, -TANK_L);
    enclosureGroup.add(bp);

    scene.add(enclosureGroup);

    // Enclosure area label
    addLabel('🏗️ ENCLOSURE (Glass Front — Tanks Inside)', encCX, encH + 1, 0, 'area-label', zone2LabelGroup);
}

// ============================================================
//  AREA 3: POST-ENCLOSURE TANKS (12-15)
// ============================================================
function buildArea3() {
    LAYOUT.area3.forEach(t => {
        const pos = layoutData.tanks[t.id];
        createTank(t.id, pos.x, t.label, t.liqColor);
        createReader(t.readerId, pos.x, LAYOUT.area3_deviceToTank, 7);

        // Glass barrier for each Area 3 tank
        const glassMat = new THREE.MeshPhysicalMaterial({
            color: 0x88ccff, transparent: true, opacity: 0.08,
            roughness: 0.05, transmission: 0.9, thickness: 0.3,
            clearcoat: 1.0, side: THREE.DoubleSide, depthWrite: false
        });
        const glass = new THREE.Mesh(new THREE.PlaneGeometry(TANK_W + 0.5, 7), glassMat);
        glass.position.set(pos.x, 3.5, 1.5);
        scene.add(glass);

        addLabel(`🧪 ${t.label}`, pos.x, TANK_H + 1, -2, 'tank-label', zone3LabelGroup);
        addLabel(`📡 #${t.readerId}`, pos.x, 8, LAYOUT.area3_deviceToTank, 'reader-label', zone3LabelGroup);
    });
}

// ============================================================
//  OVERHEAD RAIL SYSTEM
// ============================================================
function buildOverheadRail() {
    const railMat = new THREE.MeshStandardMaterial({ color: 0x3a3e44, roughness: 0.5, metalness: 0.7 });
    const railLen = 120;
    // I-beam rail
    overheadRail = new THREE.Group();
    // Top flange
    overheadRail.add(makeMesh(new THREE.BoxGeometry(railLen, 0.15, 0.6), railMat, centerX, JIG_RAIL_Y + 0.4, -TANK_L / 2));
    // Web
    overheadRail.add(makeMesh(new THREE.BoxGeometry(railLen, 0.6, 0.12), railMat, centerX, JIG_RAIL_Y + 0.1, -TANK_L / 2));
    // Bottom flange
    overheadRail.add(makeMesh(new THREE.BoxGeometry(railLen, 0.12, 0.5), railMat, centerX, JIG_RAIL_Y - 0.2, -TANK_L / 2));

    // Support columns
    for (let x = -5; x <= 110; x += 18) {
        const col = makeMesh(new THREE.BoxGeometry(0.25, JIG_RAIL_Y + 0.5, 0.25), railMat, x, (JIG_RAIL_Y + 0.5) / 2, -TANK_L / 2);
        overheadRail.add(col);
    }
    scene.add(overheadRail);
}

// ============================================================
//  JIG (MASSIVE HORIZONTAL ROD + RFID TAG)
// ============================================================
function buildJig() {
    jigGroup = new THREE.Group();
    jigGroup.name = 'jig';

    const rodMat = new THREE.MeshStandardMaterial({ color: 0x778899, roughness: 0.5, metalness: 0.8 }); // Heavy steel
    const frameMat = new THREE.MeshStandardMaterial({ color: 0x334455, roughness: 0.6, metalness: 0.8 });
    const workpieceMat = new THREE.MeshStandardMaterial({ color: 0xb0b0b0, roughness: 0.3, metalness: 0.7 });

    // Trolley (rides on rail)
    jigGroup.add(makeMesh(new THREE.BoxGeometry(2, 0.4, 2), frameMat, 0, JIG_RAIL_Y - 0.1, 0));
    
    // Industrial Warning Light
    const warningLightMat = new THREE.MeshBasicMaterial({ color: 0x332200 });
    const warningLight = makeMesh(new THREE.CylinderGeometry(0.15, 0.15, 0.3, 12), warningLightMat, 0, JIG_RAIL_Y + 0.25, 0);
    warningLight.name = 'warningLight';
    jigGroup.add(warningLight);

    // Spreader beam right below trolley
    const spreaderLen = 38;
    jigGroup.add(makeMesh(new THREE.BoxGeometry(1.2, 0.6, spreaderLen), frameMat, 0, JIG_RAIL_Y - 0.8, 0));

    // The moving part that dips
    jigRod = new THREE.Group(); 

    // Dynamic Hoisting Chains (attached to spreader)
    const chainMat = new THREE.MeshStandardMaterial({ color: 0x444444, roughness: 0.8, metalness: 0.5 });
    jigChain1 = makeMesh(new THREE.CylinderGeometry(0.08, 0.08, 1, 8), chainMat, 0, 0, 15);
    jigChain2 = makeMesh(new THREE.CylinderGeometry(0.08, 0.08, 1, 8), chainMat, 0, 0, -15);
    jigGroup.add(jigChain1);
    jigGroup.add(jigChain2);

    // The massive horizontal rod (jigged horizontally)
    const mainRodLen = 46; // Less than 49.2ft tank length
    const mainRod = makeMesh(new THREE.CylinderGeometry(0.35, 0.35, mainRodLen, 16), rodMat, 0, JIG_RAIL_Y - 8.0, 0);
    mainRod.rotation.x = Math.PI / 2; // Align along Z axis
    jigRod.add(mainRod);

    // RFID Tag (attached to the front tip of the horizontal main rod)
    const tagMat = new THREE.MeshStandardMaterial({ color: 0x111111, roughness: 0.4, metalness: 0.3 });
    jigTag = makeMesh(new THREE.BoxGeometry(0.4, 0.4, 0.15), tagMat, 0, JIG_RAIL_Y - 8.0, 23.08);
    const tagLed = makeMesh(new THREE.BoxGeometry(0.1, 0.1, 0.16), new THREE.MeshBasicMaterial({color: 0x22dd66}), 0, JIG_RAIL_Y - 8.0, 23.08);
    
    // Back RFID Tag (attached to the back tip for Zone 1 readers at the opposite side)
    const backTag = makeMesh(new THREE.BoxGeometry(0.4, 0.4, 0.15), tagMat, 0, JIG_RAIL_Y - 8.0, -23.08);
    const backTagLed = makeMesh(new THREE.BoxGeometry(0.1, 0.1, 0.16), new THREE.MeshBasicMaterial({color: 0x22dd66}), 0, JIG_RAIL_Y - 8.0, -23.08);
    
    const tagGroup = new THREE.Group();
    tagGroup.add(jigTag);
    tagGroup.add(tagLed);
    tagGroup.add(backTag);
    tagGroup.add(backTagLed);
    tagGroup.name = 'rfidTag';
    jigRod.add(tagGroup);

    jigGroup.add(jigRod);

    // Start position: Area 1
    jigGroup.position.set(-3.0, 0, -TANK_L / 2);
    scene.add(jigGroup);

    addLabel('🏷️ RFID Tag (Horizontal Jig)', -3.0, JIG_RAIL_Y + 1.2, -TANK_L / 2, 'jig-label', jigGroup);
}

// ============================================================
//  RF SIGNAL VISUALIZATION (for all readers)
// ============================================================
function buildAllRFSignals() {
    Object.entries(layoutData.readers).forEach(([id, pos]) => {
        buildRFSignal(parseInt(id), pos.x, pos.y, pos.z);
    });
}

function buildRFSignal(readerId, rx, ry, rz) {
    const g = new THREE.Group();
    g.name = `signal_${readerId}`;
    g.userData.readerId = readerId;

    const color = 0x22d3ee;
    // Cone wireframe pointing down
    const coneH = 3;
    const cone = new THREE.Mesh(
        new THREE.ConeGeometry(1.5, coneH, 16, 1, true),
        new THREE.MeshBasicMaterial({ color, wireframe: true, transparent: true, opacity: 0.06, depthWrite: false })
    );
    cone.position.set(0, -coneH / 2 - 0.2, 0);
    cone.rotation.x = Math.PI;
    cone.name = 'cone';
    g.add(cone);

    // Pulsing rings
    for (let i = 0; i < 3; i++) {
        const ring = new THREE.Mesh(
            new THREE.RingGeometry(0.2 + i * 0.35, 0.25 + i * 0.35, 24),
            new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 0.1 - i * 0.025, side: THREE.DoubleSide, depthWrite: false })
        );
        ring.rotation.x = -Math.PI / 2;
        ring.position.y = -0.5 - i * 0.8;
        ring.userData = { idx: i, baseOpacity: ring.material.opacity };
        ring.name = `ring_${i}`;
        g.add(ring);
    }

    g.position.set(rx, ry, rz);
    rfSignalGroup.add(g);
}

// ============================================================
//  KEY MEASUREMENTS
// ============================================================
function buildKeyMeasurements() {
    const y = -0.5;

    // Area 1 to Degrease: 5 ft gap (from x=10.5 to x=15.5 approximately)
    addDimLine(10.5, y, 8, 15.5, y, 8, '5.0 ft', '1.52 m');

    // Degrease to Enclosure: 5 ft gap
    addDimLine(20.5, y, 8, 25.5, y, 8, '5.0 ft', '1.52 m');

    // Enclosure end to Dryer: 10 ft gap
    const encEnd = LAYOUT.enclosure.startX + (TANK_W + LAYOUT.enclosure.gap) * 6 - LAYOUT.enclosure.gap;
    const dryerStart = layoutData.tanks['dryer'].x - TANK_W / 2;
    addDimLine(encEnd, y, 8, dryerStart, y, 8, '10 ft', '3.05 m');

    // Dryer to Zinc: 7 ft
    const dryerEnd = layoutData.tanks['dryer'].x + TANK_W / 2;
    const zincStart = layoutData.tanks['zinc'].x - TANK_W / 2;
    addDimLine(dryerEnd, y, 8, zincStart, y, 8, '7 ft', '2.13 m');

    // Zinc to Quenching: 5 ft
    const zincEnd = layoutData.tanks['zinc'].x + TANK_W / 2;
    const quenchStart = layoutData.tanks['quenching'].x - TANK_W / 2;
    addDimLine(zincEnd, y, 8, quenchStart, y, 8, '5 ft', '1.52 m');

    // Quenching to Dichrom: 4 ft
    const quenchEnd = layoutData.tanks['quenching'].x + TANK_W / 2;
    const dichStart = layoutData.tanks['dichrom'].x - TANK_W / 2;
    addDimLine(quenchEnd, y, 8, dichStart, y, 8, '4 ft', '1.22 m');

    // Reader stand height
    addDimLine(-3, 0, -14.6, -3, 7, -14.6, '7 ft', '2.13 m', true);

    // Tank height example
    const exTank = layoutData.tanks['acid1'];
    addDimLine(exTank.x + TANK_W / 2 + 1, 0, -2, exTank.x + TANK_W / 2 + 1, TANK_H, -2, '4 ft', '1.22 m', true);

    // Zone 1 Reader to Jig Tag (Back tag)
    addDimLine(LAYOUT.area1_readers[0].x - 1, 0.5, LAYOUT.area1_readerZ, LAYOUT.area1_readers[0].x - 1, 0.5, -47.6, '10 ft', '3.05 m');

    // Zone 1 Device to Device spacing
    addDimLine(LAYOUT.area1_readers[0].x, 8.5, LAYOUT.area1_readerZ, LAYOUT.area1_readers[1].x, 8.5, LAYOUT.area1_readerZ, '3.5 ft', '1.07 m');

    // Zone 2 Reader to Tank
    addDimLine(layoutData.tanks['acid1'].x - 1, 6, 0, layoutData.tanks['acid1'].x - 1, 6, LAYOUT.enclosure.deviceToTank, '2.5 ft', '0.76 m');

    // Zone 3 Reader to Tank
    addDimLine(layoutData.tanks['dryer'].x - 1, 6, 0, layoutData.tanks['dryer'].x - 1, 6, LAYOUT.area3_deviceToTank, '3.5 ft', '1.07 m');
}

function addDimLine(x1, y1, z1, x2, y2, z2, ftText, mText, isVertical) {
    const g = new THREE.Group();
    const color = 0xf59e0b;
    const mat = new THREE.LineBasicMaterial({ color, transparent: true, opacity: 0.6 });

    // Main line
    const pts = [new THREE.Vector3(x1, y1, z1), new THREE.Vector3(x2, y2, z2)];
    g.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts), mat));

    // End caps
    const capLen = 0.3;
    const capDir = isVertical ? new THREE.Vector3(1, 0, 0) : new THREE.Vector3(0, 1, 0);
    const s = new THREE.Vector3(x1, y1, z1);
    const e = new THREE.Vector3(x2, y2, z2);
    g.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([
        s.clone().addScaledVector(capDir, -capLen / 2), s.clone().addScaledVector(capDir, capLen / 2)
    ]), mat));
    g.add(new THREE.Line(new THREE.BufferGeometry().setFromPoints([
        e.clone().addScaledVector(capDir, -capLen / 2), e.clone().addScaledVector(capDir, capLen / 2)
    ]), mat));

    // Label
    const mid = new THREE.Vector3((x1 + x2) / 2, (y1 + y2) / 2, (z1 + z2) / 2);
    const lbl = document.createElement('div');
    lbl.className = 'label-3d measurement-label';
    lbl.textContent = ftText;
    lbl.dataset.ft = ftText;
    lbl.dataset.m = mText;
    const css = new CSS2DObject(lbl);
    css.position.copy(mid);
    if (isVertical) css.position.x -= 0.8;
    else css.position.y += 0.4;
    g.add(css);

    measureGroup.add(g);
}

// ============================================================
//  AREA LABELS
// ============================================================
function buildAreaLabels() {
    addLabel('ZONE 1 — WALL MOUNTED READERS', 5.25, 10, LAYOUT.area1_readerZ, 'area-label', zone1LabelGroup);
    addLabel('ZONE 2 — INSIDE ENCLOSURE', 37.5, 10, -20, 'area-label', zone2LabelGroup);
    addLabel('ZONE 3 — POST-ENCLOSURE', (layoutData.tanks['dryer'].x + layoutData.tanks['dichrom'].x) / 2, 10, -TANK_L - 3, 'area-label', zone3LabelGroup);

    // Reader labels for Area 1
    LAYOUT.area1_readers.forEach(r => {
        addLabel(`📡 #${r.id}`, r.x, 8, 0, 'reader-label', zone1LabelGroup);
    });
}

function addLabel(text, x, y, z, className, parent) {
    const div = document.createElement('div');
    div.className = `label-3d ${className}`;
    div.innerHTML = text;
    const css = new CSS2DObject(div);
    css.position.set(x, y, z);
    (parent || labelGroup).add(css);
    return css;
}

// ============================================================
//  PROCESS SIMULATION
// ============================================================
function startSimulation() {
    simRunning = true; simPaused = false;
    simStep = 0; simPhase = 'moving'; simTimer = 0;
    jigGroup.position.set(-3.0, 0, -TANK_L / 2);
    jigRod.position.y = 0;
    updateSimUI();
    document.getElementById('btn-play').disabled = true;
    document.getElementById('btn-pause').disabled = false;
    document.getElementById('btn-reset').disabled = false;
    document.getElementById('process-status').textContent = 'Running...';
    if (document.getElementById('timer-stat')) document.getElementById('timer-stat').classList.add('active');
    showToast('Process Simulation Started');
}

function pauseSimulation() {
    simPaused = !simPaused;
    document.getElementById('btn-pause').textContent = simPaused ? '▶' : '⏸';
    document.getElementById('process-status').textContent = simPaused ? 'Paused' : 'Running...';
}

function resetSimulation() {
    simRunning = false; simPaused = false;
    simStep = -1; simPhase = 'idle'; simTimer = 0;
    jigGroup.position.set(-3.0, 0, -TANK_L / 2);
    jigRod.position.y = 0;
    // Reset LEDs
    Object.values(readerLEDs).forEach(led => { led.material.color.setHex(0x22ff66); led.scale.setScalar(1); });
    document.getElementById('btn-play').disabled = false;
    document.getElementById('btn-pause').disabled = true;
    document.getElementById('btn-reset').disabled = true;
    document.getElementById('btn-pause').textContent = '⏸';
    document.getElementById('process-status').textContent = 'Ready to Start';
    document.getElementById('timer-value').textContent = '00:00';
    document.getElementById('timer-tank').textContent = '—';
    if (document.getElementById('timer-stat')) document.getElementById('timer-stat').classList.remove('active');
    showToast('Simulation Reset');
}

function updateSimulation(dt) {
    if (!simRunning || simPaused || simStep < 0 || simStep >= PROCESS_STEPS.length) return;

    const step = PROCESS_STEPS[simStep];
    const speed = simSpeed * 2;

    if (step.type === 'detect') {
        // Area 1: jig passes through readers
        if (simPhase === 'moving') {
            // Flash reader LEDs
            step.readers.forEach(rid => {
                const led = readerLEDs[rid];
                if (led) { led.material.color.setHex(0xff4444); led.scale.setScalar(1.5); }
            });
            simTimer += dt * speed;
            if (simTimer >= 2) {
                step.readers.forEach(rid => {
                    const led = readerLEDs[rid];
                    if (led) { led.material.color.setHex(0x22ff66); led.scale.setScalar(1); }
                });
                simTimer = 0;
                simStep++;
                simPhase = 'moving';
            }
        }
        updateSimUI();
        return;
    }

    // Dip process
    const tankPos = layoutData.tanks[step.tank];
    if (!tankPos) { simStep++; simPhase = 'moving'; return; }
    const targetX = tankPos.x;

    switch (simPhase) {
        case 'moving': {
            const jx = jigGroup.position.x;
            const dx = targetX - jx;
            if (Math.abs(dx) > 0.2) {
                jigGroup.position.x += Math.sign(dx) * speed * dt * 3;
            } else {
                jigGroup.position.x = targetX;
                simPhase = 'lowering';
            }
            // Activate reader LED
            step.readers.forEach(rid => {
                const led = readerLEDs[rid];
                if (led) { led.material.color.setHex(0xff8800); led.scale.setScalar(1.3); }
            });
            break;
        }
        case 'lowering': {
            jigRod.position.y -= speed * dt * 2.0;
            if (jigRod.position.y <= -4.5) {
                jigRod.position.y = -4.5;
                simPhase = 'dipping';
                simTimer = 0;
                // Activate reader — tag detected
                step.readers.forEach(rid => {
                    const led = readerLEDs[rid];
                    if (led) { led.material.color.setHex(0xff0000); led.scale.setScalar(2); }
                    // Flash ring
                    const rg = readerMeshes[rid];
                    if (rg) {
                        const flash = rg.getObjectByName('flash_' + rid);
                        if (flash) { flash.material.opacity = 0.8; flash.material.color.setHex(0xff3300); }
                    }
                });
            }
            break;
        }
        case 'dipping': {
            simTimer += dt * speed;
            if (simTimer >= step.dipTime) {
                simPhase = 'raising';
            }
            break;
        }
        case 'raising': {
            jigRod.position.y += speed * dt * 2.0;
            if (jigRod.position.y >= 0) {
                jigRod.position.y = 0;
                // Reset reader LED
                step.readers.forEach(rid => {
                    const led = readerLEDs[rid];
                    if (led) { led.material.color.setHex(0x22ff66); led.scale.setScalar(1); }
                    // Reset flash ring
                    const rg = readerMeshes[rid];
                    if (rg) {
                        const flash = rg.getObjectByName('flash_' + rid);
                        if (flash) { flash.material.opacity = 0; }
                    }
                });
                simTimer = 0;
                simStep++;
                simPhase = 'moving';
                if (simStep >= PROCESS_STEPS.length) {
                    simPhase = 'returning';
                    document.getElementById('process-status').textContent = 'Returning to Start...';
                    showToast('Cycle Complete - Returning');
                }
            }
            break;
        }
        case 'returning': {
            // Move backwards quickly to start position for next cycle
            const returnSpeed = speed * 3.5;
            jigGroup.position.x -= returnSpeed * dt * 3;
            if (jigGroup.position.x <= -3.0) {
                jigGroup.position.x = -3.0;
                simStep = 0;
                simPhase = 'moving'; // Auto restart next cycle
                document.getElementById('process-status').textContent = 'Cycle Restarted';
                showToast('New Cycle Started');
            }
            break;
        }
    }
    updateSimUI();
}

function updateSimUI() {
    // Clear all 3D tank timers
    Object.values(layoutData.tanks).forEach(t => {
        if (t.timerElem) {
            t.timerElem.textContent = '--:--';
            t.timerElem.classList.remove('active-timer');
        }
    });

    if (simStep < 0 || simStep >= PROCESS_STEPS.length) {
        if (document.getElementById('hmi-load')) document.getElementById('hmi-load').textContent = '0 kg';
        if (document.getElementById('hmi-temp')) {
            document.getElementById('hmi-temp').textContent = '-- °C';
            document.getElementById('hmi-temp').className = 'hmi-value';
        }
        if (document.getElementById('hmi-ph')) document.getElementById('hmi-ph').textContent = '--';
        return;
    }

    if (simPhase === 'returning') {
        document.getElementById('timer-tank').textContent = 'Returning to Start...';
        document.getElementById('timer-value').textContent = '----';
        return;
    }

    const step = PROCESS_STEPS[simStep];

    // Timer display
    if (simPhase === 'dipping') {
        const sec = Math.floor(simTimer);
        const total = step.dipTime;
        const timeStr = String(Math.floor(sec / 60)).padStart(2, '0') + ':' + String(sec % 60).padStart(2, '0');
        
        document.getElementById('timer-value').textContent = timeStr;
        document.getElementById('timer-tank').textContent = `${step.name} (${sec}/${total}s)`;
        document.getElementById('timer-stat').classList.add('active');

        // Update active 3D tank timer hovering above tank
        const currentTank = step.tank ? layoutData.tanks[step.tank] : null;
        if (currentTank && currentTank.timerElem) {
            currentTank.timerElem.textContent = `${timeStr} / ${total}s`;
            currentTank.timerElem.classList.add('active-timer');
        }
    } else {
        if (step && step.type === 'detect') {
            document.getElementById('timer-value').textContent = 'N/A';
            document.getElementById('timer-tank').textContent = 'ZONE 1 (DETECT ONLY)';
        } else {
            document.getElementById('timer-value').textContent = '--:--';
            document.getElementById('timer-tank').textContent = step.name + ' — ' + simPhase;
        }
        document.getElementById('timer-stat').classList.remove('active');
    }

    // SCADA HMI Telemetry Update
    if (document.getElementById('hmi-load')) {
        document.getElementById('hmi-load').textContent = '2450 kg';
        if (step.tank && simPhase === 'dipping') {
            let temp = 25, ph = 7;
            if (step.tank.includes('acid')) { temp = 65; ph = 2.5; }
            else if (step.tank === 'degrease') { temp = 80; ph = 9.5; }
            else if (step.tank === 'flux') { temp = 40; ph = 4.5; }
            else if (step.tank === 'dryer') { temp = 120; ph = 'N/A'; }
            else if (step.tank === 'zinc') { temp = 450; ph = 'N/A'; }
            
            const tempEl = document.getElementById('hmi-temp');
            tempEl.textContent = temp + ' °C';
            document.getElementById('hmi-ph').textContent = ph;
            
            if (temp > 100) tempEl.className = 'hmi-value danger';
            else if (temp > 50) tempEl.className = 'hmi-value warning';
            else tempEl.className = 'hmi-value';
        } else {
            const tempEl = document.getElementById('hmi-temp');
            tempEl.textContent = '-- °C';
            tempEl.className = 'hmi-value';
            document.getElementById('hmi-ph').textContent = '--';
        }
    }
}

// ============================================================
//  UI CONTROLS
// ============================================================
function setupUI() {
    // HMI panel is now in index.html, no need to create dynamically

    // Zone toggle buttons
    document.getElementById('toggle-zone1').addEventListener('click', function() {
        this.classList.toggle('active');
        if (zone1LabelGroup) zone1LabelGroup.visible = this.classList.contains('active');
        showToast(this.classList.contains('active') ? 'Zone 1 Labels: ON' : 'Zone 1 Labels: OFF');
    });
    document.getElementById('toggle-zone2').addEventListener('click', function() {
        this.classList.toggle('active');
        if (zone2LabelGroup) zone2LabelGroup.visible = this.classList.contains('active');
        showToast(this.classList.contains('active') ? 'Zone 2 Labels: ON' : 'Zone 2 Labels: OFF');
    });
    document.getElementById('toggle-zone3').addEventListener('click', function() {
        this.classList.toggle('active');
        if (zone3LabelGroup) zone3LabelGroup.visible = this.classList.contains('active');
        showToast(this.classList.contains('active') ? 'Zone 3 Labels: ON' : 'Zone 3 Labels: OFF');
    });

    // Camera views
    document.querySelectorAll('.view-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            document.querySelectorAll('.view-btn').forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            switchView(btn.dataset.view);
        });
    });

    // Feature toggles
    document.getElementById('toggle-signal').addEventListener('click', function () {
        showSignal = !showSignal; this.classList.toggle('active');
        rfSignalGroup.visible = showSignal;
        showToast(showSignal ? 'RF Signal: ON' : 'RF Signal: OFF');
    });
    document.getElementById('toggle-measurements').addEventListener('click', function () {
        showMeasurements = !showMeasurements; this.classList.toggle('active');
        measureGroup.visible = showMeasurements;
        showToast(showMeasurements ? 'Measurements: ON' : 'Measurements: OFF');
    });
    document.getElementById('toggle-labels').addEventListener('click', function () {
        showLabels = !showLabels; this.classList.toggle('active');
        labelGroup.visible = showLabels;
        showToast(showLabels ? 'Labels: ON' : 'Labels: OFF');
    });
    document.getElementById('toggle-xray').addEventListener('click', function () {
        xrayMode = !xrayMode; this.classList.toggle('active');
        applyXray(xrayMode);
        showToast(xrayMode ? 'X-Ray: ON' : 'X-Ray: OFF');
    });

    // Units
    document.getElementById('unit-toggle').addEventListener('click', () => {
        isMetric = !isMetric;
        document.querySelectorAll('.unit-label').forEach(l => l.classList.toggle('active'));
        updateUnits();
        showToast(isMetric ? 'Units: Metric (m)' : 'Units: Imperial (ft)');
    });

    // Panel toggle
    document.getElementById('specs-toggle').addEventListener('click', () => {
        document.getElementById('specs-panel').classList.toggle('collapsed');
    });

    // Simulation controls
    document.getElementById('btn-play').addEventListener('click', startSimulation);
    document.getElementById('btn-pause').addEventListener('click', pauseSimulation);
    document.getElementById('btn-reset').addEventListener('click', resetSimulation);
    document.getElementById('btn-live').addEventListener('click', toggleLiveMode);
    document.getElementById('sim-speed').addEventListener('input', (e) => {
        simSpeed = parseInt(e.target.value);
    });
}

function switchView(view) {
    const dur = 1200;
    const views = {
        perspective: { pos: [centerX, 55, 70], target: [centerX, 2, -15] },
        top:   { pos: [centerX, 90, -TANK_L / 2 + 0.1], target: [centerX, 0, -TANK_L / 2] },
        front: { pos: [centerX, 10, 30], target: [centerX, 4, 0] },
        side:  { pos: [-15, 12, -TANK_L / 2], target: [centerX, 4, -TANK_L / 2] },
        area1: { pos: [5.25, 15, 18], target: [5.25, 3, 0] },
        area2: { pos: [41.5, 20, 15], target: [41.5, 3, -10] },
        area3: { pos: [87, 18, 18], target: [87, 3, -5] }
    };
    const v = views[view] || views.perspective;
    animateCamera(new THREE.Vector3(...v.pos), new THREE.Vector3(...v.target), dur);
}

function animateCamera(tPos, tTarget, duration) {
    const sPos = camera.position.clone();
    const sTarget = controls.target.clone();
    const start = performance.now();
    function step(now) {
        const t = Math.min((now - start) / duration, 1);
        const e = t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
        camera.position.lerpVectors(sPos, tPos, e);
        controls.target.lerpVectors(sTarget, tTarget, e);
        controls.update();
        if (t < 1) requestAnimationFrame(step);
    }
    requestAnimationFrame(step);
}

function updateUnits() {
    document.querySelectorAll('.spec-value[data-ft]').forEach(el => {
        el.textContent = isMetric ? (el.dataset.m + (el.dataset.m.includes('×') ? ' m' : ' m')) : (el.dataset.ft + (el.dataset.ft.includes('×') ? ' ft' : ' ft'));
    });
    document.querySelectorAll('.measurement-label').forEach(el => {
        el.textContent = isMetric ? el.dataset.m : el.dataset.ft;
    });
}

function applyXray(on) {
    scene.traverse(obj => {
        if (obj.isMesh && !obj.name.startsWith('surface_') && !obj.name.startsWith('rfidTag') && !obj.name.startsWith('led_')) {
            if (on) {
                obj.userData._origTrans = obj.material.transparent;
                obj.userData._origOp = obj.material.opacity;
                obj.userData._origWire = obj.material.wireframe;
                obj.material.transparent = true;
                obj.material.opacity = Math.min(obj.material.opacity, 0.12);
                obj.material.wireframe = true;
                obj.material.needsUpdate = true;
            } else if (obj.userData._origTrans !== undefined) {
                obj.material.transparent = obj.userData._origTrans;
                obj.material.opacity = obj.userData._origOp;
                obj.material.wireframe = obj.userData._origWire;
                obj.material.needsUpdate = true;
            }
        }
    });
}

function showToast(msg) {
    const t = document.getElementById('toast');
    document.getElementById('toast-message').textContent = msg;
    t.classList.remove('hidden'); t.classList.add('show');
    setTimeout(() => { t.classList.remove('show'); setTimeout(() => t.classList.add('hidden'), 300); }, 1600);
}

function onKeyDown(e) {
    if (e.key === 'r' || e.key === 'R') {
        switchView('perspective');
        document.querySelectorAll('.view-btn').forEach(b => b.classList.remove('active'));
        document.querySelector('[data-view="perspective"]').classList.add('active');
    }
    if (e.key === ' ') { e.preventDefault(); if (simRunning) pauseSimulation(); else startSimulation(); }
}

function onResize() {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
    labelRenderer.setSize(window.innerWidth, window.innerHeight);
}

// ============================================================
//  LIVE HARDWARE RFID INTEGRATION (Silion + SDL1010 Server)
// ============================================================
function toggleLiveMode() {
    liveModeActive = !liveModeActive;
    const btn = document.getElementById('btn-live');
    
    if (liveModeActive) {
        // Reset synthetic simulation
        resetSimulation();
        
        // Disable synthetic controls
        document.getElementById('btn-play').disabled = true;
        document.getElementById('btn-pause').disabled = true;
        document.getElementById('btn-reset').disabled = true;
        
        // Update button UI
        btn.classList.add('active');
        btn.textContent = '🔌 Live RFID: ON';
        
        // Reset positions
        jigGroup.position.set(-3.0, 0, -TANK_L / 2);
        jigRod.position.y = 0;
        resetAllReaderLEDs();
        
        // Start polling loop
        liveGracePeriods = 0;
        livePrevTagData = {};
        pollLiveRFIDServer(); // Immediate initial poll
        livePollInterval = setInterval(pollLiveRFIDServer, 500);
        
        showToast('Live RFID Mode Enabled');
        updateLiveUI('Standby');
    } else {
        // Clear polling
        if (livePollInterval) {
            clearInterval(livePollInterval);
            livePollInterval = null;
        }
        
        // Enable synthetic controls
        document.getElementById('btn-play').disabled = false;
        document.getElementById('btn-pause').disabled = true;
        document.getElementById('btn-reset').disabled = true;
        
        // Update button UI
        btn.classList.remove('active');
        btn.textContent = '🔌 Live RFID: OFF';
        
        // Reset variables
        liveActiveReaderId = null;
        liveActiveEPC = '';
        liveActiveRSSI = 'N/A';
        liveDwellTimer = 0;
        liveStabilizationActive = false;
        liveStabilizationTimer = 0;
        livePrevTagData = {};
        
        // Reset positions & lights
        jigGroup.position.set(-3.0, 0, -TANK_L / 2);
        jigRod.position.y = 0;
        resetAllReaderLEDs();
        
        // Reset UI labels
        document.getElementById('process-status').textContent = 'Ready to Start';
        document.getElementById('timer-value').textContent = '00:00';
        document.getElementById('timer-tank').textContent = 'DIP TIMER';
        document.getElementById('timer-stat').classList.remove('active');
        
        showToast('Live RFID Mode Disabled');
    }
}

function pollLiveRFIDServer() {
    if (!liveModeActive) return;
    
    // Use clear=false query parameter to prevent clearing the tag map on the server.
    // This allows multiple dashboards to run simultaneously without stealing data from each other.
    fetch(LIVE_SERVER_URL + '?clear=false')
        .then(response => response.json())
        .then(result => {
            if (result && Array.isArray(result.tags) && result.tags.length > 0) {
                // Find a tag that has a valid antenna ID (at or antenna) and is actively scanning (differential tracking)
                let activeTag = null;
                for (let i = 0; i < result.tags.length; i++) {
                    const t = result.tags[i];
                    if (t.hasOwnProperty('at') || t.hasOwnProperty('antenna')) {
                        const epc = t.ep || t.epc;
                        const lt = t.lt || 0;
                        const rc = t.rc || 0;
                        const prev = livePrevTagData[epc];
                        
                        // Active if:
                        // 1. We've never seen this tag before (prev is undefined)
                        // 2. OR its last-seen timestamp (lt) has updated
                        // 3. OR its read count (rc) has increased
                        if (!prev || lt !== prev.lt || rc !== prev.rc) {
                            activeTag = t;
                            livePrevTagData[epc] = { lt, rc };
                            break;
                        }
                    }
                }
                
                if (activeTag) {
                    const antId = parseInt(activeTag.at || activeTag.antenna);
                    // Verify reader ID is in range 1-15
                    if (antId >= 1 && antId <= 15) {
                        liveActiveReaderId = antId;
                        liveActiveEPC = activeTag.ep || activeTag.epc || 'N/A';
                        liveActiveRSSI = activeTag.ri || activeTag.rssi || 'N/A';
                        liveGracePeriods = 0;
                    }
                } else {
                    // No active changes (stale tag read), increment grace period
                    handleLiveGraceTimeout();
                }
            } else {
                handleLiveGraceTimeout();
            }
        })
        .catch(err => {
            console.warn('RFID Server Connection Error:', err);
            if (liveActiveReaderId !== null) {
                liveGracePeriods++;
                if (liveGracePeriods > 4) {
                    liveActiveReaderId = null;
                    liveActiveEPC = '';
                    liveActiveRSSI = 'N/A';
                    liveStabilizationActive = false;
                    liveStabilizationTimer = 0;
                    updateLiveUI('Server Connection Error');
                }
            } else {
                const statusEl = document.getElementById('process-status');
                if (statusEl) statusEl.innerHTML = `LIVE: <span style="color: #ef4444;">DISCONNECTED</span><br><span style="color: #64748b; font-size: 0.55rem;">Server not running on port 12345</span>`;
            }
        });
}

function handleLiveGraceTimeout() {
    if (liveActiveReaderId !== null) {
        liveGracePeriods++;
        if (liveGracePeriods > 3) { // 1.5 seconds threshold
            liveActiveReaderId = null;
            liveActiveEPC = '';
            liveActiveRSSI = 'N/A';
            liveStabilizationActive = false;
            liveStabilizationTimer = 0;
        }
    }
}

function updateLiveRFIDMode(dt) {
    const speed = simSpeed * 2;
    
    if (liveActiveReaderId !== null) {
        const targetX = layoutData.readers[liveActiveReaderId].x;
        const jx = jigGroup.position.x;
        const dx = targetX - jx;
        
        if (Math.abs(dx) > 0.2) {
            // Safety: Raise jig first before shifting crane horizontally
            if (jigRod.position.y < 0) {
                jigRod.position.y += speed * dt * 2.0;
                if (jigRod.position.y >= 0) jigRod.position.y = 0;
                updateLiveUI('Safety Raise...');
            } else {
                // Move crane horizontally
                jigGroup.position.x += Math.sign(dx) * speed * dt * 3;
                setReaderLEDColor(liveActiveReaderId, 0xff8800, 1.3);
                updateLiveUI(`Moving to Reader #${liveActiveReaderId}...`);
            }
            setReaderFlashRing(liveActiveReaderId, false);
        } else {
            // Crane arrived at the correct reader/tank
            jigGroup.position.x = targetX;
            
            // Start stabilization delay (which is our 10-second lowering animation)
            if (!liveStabilizationActive && liveDwellTimer === 0) {
                liveStabilizationActive = true;
                liveStabilizationTimer = STABILIZATION_DELAY;
            }
            
            if (liveStabilizationActive && liveStabilizationTimer > 0) {
                liveStabilizationTimer -= dt;
                if (liveStabilizationTimer < 0) liveStabilizationTimer = 0;
                
                // Animate the rod lowering progressively in sync with the 10s delay
                const progress = (STABILIZATION_DELAY - liveStabilizationTimer) / STABILIZATION_DELAY;
                jigRod.position.y = -4.5 * progress;
                
                setReaderLEDColor(liveActiveReaderId, 0xffaa00, 1.4);
                updateLiveUI(`Stabilizing/Lowering (${liveStabilizationTimer.toFixed(1)}s)...`);
                
                if (liveStabilizationTimer === 0) {
                    liveStabilizationActive = false;
                    jigRod.position.y = -4.5;
                    liveDwellTimer = 0.001; // Start the process dip timer
                }
            } else {
                // Fully lowered: run process dwell timer
                liveDwellTimer += dt;
                setReaderLEDColor(liveActiveReaderId, 0xff0000, 1.8);
                setReaderFlashRing(liveActiveReaderId, true);
                updateLiveUI('Processing / Dipping...');
            }
        }
    } else {
        // No tag active: raise jig to default home height
        liveStabilizationActive = false;
        liveStabilizationTimer = 0;
        if (jigRod.position.y < 0) {
            jigRod.position.y += speed * dt * 2.0;
            if (jigRod.position.y >= 0) {
                jigRod.position.y = 0;
                resetAllReaderLEDs();
                liveDwellTimer = 0;
            }
            updateLiveUI('Raising Jig...');
        } else {
            resetAllReaderLEDs();
            updateLiveUI('Standby - Waiting for tag...');
            liveDwellTimer = 0;
        }
    }
}

function setReaderLEDColor(id, hex, scale) {
    const led = readerLEDs[id];
    if (led) {
        led.material.color.setHex(hex);
        led.scale.setScalar(scale);
        led.material.opacity = 1.0;
    }
}

function setReaderFlashRing(id, active) {
    const rg = readerMeshes[id];
    if (rg) {
        const flash = rg.getObjectByName('flash_' + id);
        if (flash) {
            flash.material.opacity = active ? 0.8 : 0;
            if (active) flash.material.color.setHex(0xff3300);
        }
    }
}

function resetAllReaderLEDs() {
    Object.entries(readerLEDs).forEach(([id, led]) => {
        led.material.color.setHex(0x22ff66);
        led.scale.setScalar(1);
    });
    Object.entries(readerMeshes).forEach(([id, rg]) => {
        const flash = rg.getObjectByName('flash_' + id);
        if (flash) {
            flash.material.opacity = 0;
        }
    });
}

function updateLiveUI(statusText) {
    const timerValEl = document.getElementById('timer-value');
    const timerTankEl = document.getElementById('timer-tank');
    const timerStatEl = document.getElementById('timer-stat');
    
    if (timerValEl) {
        if (liveActiveReaderId !== null && !liveStabilizationActive && jigRod.position.y <= -4.5) {
            timerValEl.textContent = formatTime(liveDwellTimer);
            timerStatEl.classList.add('active');
        } else if (liveStabilizationActive) {
            timerValEl.textContent = 'WAIT';
            timerStatEl.classList.remove('active');
        } else {
            timerValEl.textContent = '--:--';
            timerStatEl.classList.remove('active');
        }
    }
    
    if (timerTankEl) {
        if (liveActiveReaderId !== null) {
            const step = PROCESS_STEPS.find(s => s.readers.includes(liveActiveReaderId));
            const tankName = step ? step.name : `Reader #${liveActiveReaderId}`;
            timerTankEl.textContent = `${tankName} — ${statusText.toUpperCase()}`;
        } else {
            timerTankEl.textContent = `LIVE RFID — ${statusText.toUpperCase()}`;
        }
    }
    
    if (liveActiveReaderId !== null && jigRod.position.y <= -4.5) {
        const step = PROCESS_STEPS.find(s => s.readers.includes(liveActiveReaderId));
        if (step && step.tank) {
            let temp = 25, ph = 7;
            if (step.tank.includes('acid')) { temp = 65; ph = 2.5; }
            else if (step.tank === 'degrease') { temp = 80; ph = 9.5; }
            else if (step.tank === 'flux') { temp = 40; ph = 4.5; }
            else if (step.tank === 'dryer') { temp = 120; ph = 'N/A'; }
            else if (step.tank === 'zinc') { temp = 450; ph = 'N/A'; }
            
            const tempEl = document.getElementById('hmi-temp');
            if (tempEl) {
                tempEl.textContent = temp + ' °C';
                if (temp > 100) tempEl.className = 'hmi-value danger';
                else if (temp > 50) tempEl.className = 'hmi-value warning';
                else tempEl.className = 'hmi-value';
            }
            
            const phEl = document.getElementById('hmi-ph');
            if (phEl) phEl.textContent = ph;
        }
        
        const loadEl = document.getElementById('hmi-load');
        if (loadEl) loadEl.textContent = '2450 kg';
    } else {
        const tempEl = document.getElementById('hmi-temp');
        if (tempEl) {
            tempEl.textContent = '-- °C';
            tempEl.className = 'hmi-value';
        }
        const phEl = document.getElementById('hmi-ph');
        if (phEl) phEl.textContent = '--';
        const loadEl = document.getElementById('hmi-load');
        if (loadEl) loadEl.textContent = '0 kg';
    }
    
    const statusEl = document.getElementById('process-status');
    if (statusEl) {
        if (liveModeActive) {
            if (liveActiveReaderId !== null) {
                statusEl.innerHTML = `LIVE: ACTIVE<br>EPC: <span style="font-family: monospace; font-size: 0.6rem; color: #0ea5e9;">${liveActiveEPC.substring(0, 10)}...</span><br>RSSI: <span style="color: #10b981;">${liveActiveRSSI} dBm</span>`;
            } else {
                statusEl.innerHTML = `LIVE: ACTIVE<br><span style="color: #64748b; font-size: 0.62rem;">Waiting for physical tag...</span>`;
            }
        }
    }
}

function formatTime(sec) {
    const m = Math.floor(sec / 60);
    const s = Math.floor(sec % 60);
    return String(m).padStart(2, '0') + ':' + String(s).padStart(2, '0');
}

// ============================================================

// ============================================================
//  ANIMATION LOOP
// ============================================================
function animate() {
    requestAnimationFrame(animate);
    const dt = clock.getDelta();
    const elapsed = clock.getElapsedTime();

    // RF signal animation
    if (showSignal) {
        rfSignalGroup.children.forEach(sg => {
            sg.children.forEach(child => {
                if (child.name === 'cone') {
                    child.rotation.y = elapsed * 0.3;
                    child.material.opacity = 0.04 + Math.sin(elapsed * 2) * 0.02;
                }
                if (child.name && child.name.startsWith('ring_')) {
                    const idx = child.userData.idx;
                    const wave = Math.sin(elapsed * 2.5 - idx * 0.8) * 0.5 + 0.5;
                    child.material.opacity = child.userData.baseOpacity * (0.3 + wave * 0.7);
                    child.scale.setScalar(1 + Math.sin(elapsed * 2 - idx * 0.5) * 0.1);
                }
            });
        });
    }

    // Liquid surface shimmer
    Object.keys(tankMeshes).forEach(id => {
        const tank = tankMeshes[id];
        const surf = tank.getObjectByName('surface_' + id);
        if (surf) surf.material.opacity = 0.08 + Math.sin(elapsed * 1.2 + id.length) * 0.04;
    });

    // LED blink
    Object.entries(readerLEDs).forEach(([id, led]) => {
        if (!simRunning) {
            led.material.opacity = 0.6 + Math.sin(elapsed * 3 + parseInt(id)) * 0.4;
        }
    });

    // Flash ring pulse animation (pulses when detecting)
    if (simRunning) {
        Object.keys(readerMeshes).forEach(id => {
            const rg = readerMeshes[id];
            const flash = rg.getObjectByName('flash_' + id);
            if (flash && flash.material.opacity > 0) {
                flash.material.opacity = 0.4 + Math.sin(elapsed * 8) * 0.4;
                flash.scale.setScalar(1.0 + Math.sin(elapsed * 6) * 0.15);
            }
        });
    }

    // RFID tag glow
    if (jigTag) {
        jigTag.material.emissiveIntensity = 0.2 + Math.sin(elapsed * 4) * 0.2;
    }

    // Dynamic Chain Linkage Update
    if (jigChain1 && jigChain2 && jigRod) {
        const topY = JIG_RAIL_Y - 0.8;
        const bottomY = (JIG_RAIL_Y - 8.0) + jigRod.position.y;
        const len = topY - bottomY;
        
        jigChain1.scale.y = len;
        jigChain1.position.y = topY - len / 2;
        
        jigChain2.scale.y = len;
        jigChain2.position.y = topY - len / 2;
    }

    // Jig Warning Light
    if (jigGroup) {
        const wl = jigGroup.getObjectByName('warningLight');
        if (wl) {
            const isMoving = liveModeActive 
                ? (liveActiveReaderId !== null && Math.abs(layoutData.readers[liveActiveReaderId].x - jigGroup.position.x) > 0.2)
                : (simRunning && (simPhase === 'moving' || simPhase === 'returning'));
            
            if (isMoving) {
                wl.material.color.setHex((Math.floor(elapsed * 6) % 2 === 0) ? 0xffaa00 : 0x332200);
            } else {
                wl.material.color.setHex(0x332200);
            }
        }
    }

    // Simulation update
    if (liveModeActive) {
        updateLiveRFIDMode(dt);
    } else {
        updateSimulation(dt);
    }

    controls.update();
    renderer.render(scene, camera);
    labelRenderer.render(scene, camera);
}

// ============================================================
//  START
// ============================================================
init();
