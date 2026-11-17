/**
 * Browser demo: drop an .obj (+ .mtl) and render it with Three.js.
 *
 * Geometry comes straight from the wasm wrapper as interleaved corner buffers
 * (x y z nx ny nz u v), so Three.js reads them through InterleavedBuffer and
 * per-material draw groups -- no index buffer, no de-indexing in JS.
 */
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

import { initTinyObj, STRIDE, NO_MATERIAL } from '../js/index.js';

const canvas = document.getElementById('view');
const status = document.getElementById('status');
const pick = document.getElementById('pick');
const files = document.getElementById('files');
const dropzone = document.getElementById('dropzone');

const renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));

const scene = new THREE.Scene();
scene.background = new THREE.Color(0x101216);

const camera = new THREE.PerspectiveCamera(45, 1, 0.01, 1000);
camera.position.set(3, 2, 4);

const controls = new OrbitControls(camera, canvas);
controls.enableDamping = true;

scene.add(new THREE.HemisphereLight(0xffffff, 0x222833, 1.1));
const key = new THREE.DirectionalLight(0xffffff, 1.6);
key.position.set(4, 6, 3);
scene.add(key);

const grid = new THREE.GridHelper(10, 10, 0x2b323c, 0x1c222a);
grid.material.transparent = true;
grid.material.opacity = 0.75;
scene.add(grid);

const fallbackMaterial = new THREE.MeshPhongMaterial({
  color: 0x9aa4b2,
  shininess: 10,
  side: THREE.DoubleSide,
});

let current = null;
let tinyobj = null;

function setStatus(text, kind = 'info') {
  status.textContent = text;
  status.dataset.kind = kind;
}

function resize() {
  const width = canvas.clientWidth || window.innerWidth;
  const height = canvas.clientHeight || window.innerHeight;
  renderer.setSize(width, height, false);
  camera.aspect = width / height;
  camera.updateProjectionMatrix();
}

function frame(object) {
  const box = new THREE.Box3().setFromObject(object);
  if (box.isEmpty()) return;
  const size = box.getSize(new THREE.Vector3());
  const center = box.getCenter(new THREE.Vector3());
  const radius = Math.max(size.x, size.y, size.z) * 0.5 || 1;

  controls.target.copy(center);
  const distance = radius / Math.tan((camera.fov * Math.PI) / 360);
  const direction = new THREE.Vector3(1, 0.65, 1).normalize();
  camera.position.copy(center).addScaledVector(direction, distance * 1.9);
  camera.near = Math.max(distance / 100, 0.001);
  camera.far = distance * 100;
  camera.updateProjectionMatrix();
  controls.update();

  grid.position.y = box.min.y - size.y * 0.02;
}

function disposeObject(object) {
  for (const child of object.children) {
    child.geometry?.dispose();
    if (Array.isArray(child.material)) {
      for (const material of child.material) {
        if (material !== fallbackMaterial) material.dispose();
      }
    } else if (child.material && child.material !== fallbackMaterial) {
      child.material.dispose();
    }
  }
}

function materialFor(entry) {
  const material = new THREE.MeshPhongMaterial({
    color: new THREE.Color(
      clamp01(entry.diffuse[0]),
      clamp01(entry.diffuse[1]),
      clamp01(entry.diffuse[2]),
    ),
    emissive: new THREE.Color(
      clamp01(entry.emissive[0]),
      clamp01(entry.emissive[1]),
      clamp01(entry.emissive[2]),
    ),
    shininess: Math.max(entry.shininess, 0) * 2,
    specular: new THREE.Color(0x1a1a1a),
    side: THREE.DoubleSide,
  });
  if (entry.dissolve < 1) {
    material.transparent = true;
    material.opacity = clamp01(entry.dissolve);
  }
  return material;
}

function clamp01(v) {
  return v < 0 ? 0 : v > 1 ? 1 : v;
}

function buildGroup(model) {
  const group = new THREE.Group();

  for (const shape of model.shapes) {
    if (!shape.triangleCount) continue;

    const buffer = new THREE.InterleavedBuffer(shape.vertices, STRIDE);
    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute(
      'position',
      new THREE.InterleavedBufferAttribute(buffer, 3, 0),
    );
    geometry.setAttribute(
      'normal',
      new THREE.InterleavedBufferAttribute(buffer, 3, 3),
    );
    geometry.setAttribute(
      'uv',
      new THREE.InterleavedBufferAttribute(buffer, 2, 6),
    );

    const materials = model.materials.map(materialFor);
    materials.push(fallbackMaterial);
    const fallbackIndex = materials.length - 1;

    for (const run of shape.groups) {
      const index =
        run.material === NO_MATERIAL || run.material >= model.materials.length
          ? fallbackIndex
          : run.material;
      geometry.addGroup(run.start * 3, run.count * 3, index);
    }

    geometry.computeBoundingSphere();
    group.add(new THREE.Mesh(geometry, materials));
    if (shape.name) group.name = shape.name;
  }

  return group;
}

async function showModel(objFile, mtlFile) {
  setStatus(`Parsing ${objFile.name}…`);

  const [obj, mtl] = await Promise.all([
    readSource(objFile),
    mtlFile ? readSource(mtlFile) : null,
  ]);

  const model = tinyobj.parse(obj, {
    mtl,
    mtlName: mtlFile ? mtlFile.name : '',
  });

  const group = buildGroup(model);
  if (!group.children.length) throw new Error('No triangles found in the file.');

  if (current) {
    scene.remove(current);
    disposeObject(current);
  }
  current = group;
  scene.add(group);
  frame(group);

  const triangles = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  const parts = [
    `${objFile.name}: ${triangles} triangles`,
    `${model.shapes.length} shape${model.shapes.length === 1 ? '' : 's'}`,
    `${model.materials.length} material${model.materials.length === 1 ? '' : 's'}`,
    mtlFile ? `mtl ${mtlFile.name}` : 'no .mtl',
  ];
  const warnings = model.message.trim();
  setStatus(
    `${parts.join(' · ')}\n${warnings}`.trim(),
    warnings ? 'warn' : 'info',
  );
}

function readSource(file) {
  return file.arrayBuffer();
}

async function handleFiles(list) {
  if (!tinyobj) {
    setStatus('The WebAssembly module is still loading…', 'warn');
    return;
  }
  const picked = Array.from(list).filter((file) => /\.(obj|mtl)$/i.test(file.name));
  if (!picked.length) {
    setStatus('Please choose a .obj file (and optionally its .mtl).', 'error');
    return;
  }

  const objFile = picked.find((file) => /\.obj$/i.test(file.name));
  if (!objFile) {
    setStatus('No .obj file in that selection — only .mtl was dropped.', 'error');
    return;
  }

  const stem = objFile.name.replace(/\.obj$/i, '').toLowerCase();
  const mtls = picked.filter((file) => /\.mtl$/i.test(file.name));
  const mtlFile =
    mtls.find((file) => file.name.replace(/\.mtl$/i, '').toLowerCase() === stem) ||
    (mtls.length === 1 ? mtls[0] : null);

  try {
    await showModel(objFile, mtlFile);
  } catch (error) {
    setStatus(`Failed to load ${objFile.name}: ${error.message}`, 'error');
  }
}

let dragDepth = 0;

window.addEventListener('dragenter', (event) => {
  event.preventDefault();
  dragDepth++;
  document.body.dataset.dragging = 'true';
});

window.addEventListener('dragover', (event) => {
  event.preventDefault();
  event.dataTransfer.dropEffect = 'copy';
});

window.addEventListener('dragleave', () => {
  dragDepth = Math.max(0, dragDepth - 1);
  if (!dragDepth) document.body.dataset.dragging = 'false';
});

window.addEventListener('drop', (event) => {
  event.preventDefault();
  dragDepth = 0;
  document.body.dataset.dragging = 'false';
  if (event.dataTransfer?.files?.length) handleFiles(event.dataTransfer.files);
});

pick.addEventListener('click', () => files.click());
files.addEventListener('change', () => {
  if (files.files?.length) handleFiles(files.files);
  files.value = '';
});

document.addEventListener('keydown', (event) => {
  if (event.key === 'o' && (event.ctrlKey || event.metaKey)) {
    event.preventDefault();
    files.click();
  }
});

function onResize() {
  resize();
}
window.addEventListener('resize', onResize);

renderer.setAnimationLoop(() => {
  controls.update();
  renderer.render(scene, camera);
});

function disableUi(reason) {
  pick.disabled = true;
  dropzone.textContent = reason;
  setStatus(reason, 'error');
}

window.addEventListener('beforeunload', () => {
  if (current) disposeObject(current);
  renderer.dispose();
});

resize();
setStatus('Loading WebAssembly…');
try {
  tinyobj = await initTinyObj({
    locateFile: (path) => new URL(`../dist/${path}`, import.meta.url).href,
  });
  setStatus('Ready — drop an .obj or use “Choose .obj”.');
} catch (error) {
  disableUi(
    `Could not load the WebAssembly module: ${error.message}. ` +
      'Run ./build.sh and serve the web/ directory over HTTP.',
  );
  throw error;
}
