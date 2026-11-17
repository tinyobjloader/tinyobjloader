/**
 * Browser demo: drop an .obj (or a whole folder) and render it with Three.js.
 *
 * Geometry comes straight from the wasm wrapper as interleaved corner buffers
 * (x y z nx ny nz u v), so Three.js reads them through InterleavedBuffer and
 * per-material draw groups -- no index buffer, no de-indexing in JS.
 */
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';

import { initTinyObj, STRIDE, NO_MATERIAL } from '../js/index.js';
import { parseSubdTags, subdivideShape } from './subd.js';

const canvas = document.getElementById('view');
const status = document.getElementById('status');
const pick = document.getElementById('pick');
const pickFolder = document.getElementById('pick-folder');
const files = document.getElementById('files');
const folder = document.getElementById('folder');
const dropzone = document.getElementById('dropzone');
const materialsEl = document.getElementById('materials');
const shapesEl = document.getElementById('shapes');
const selectionEl = document.getElementById('selection');
const selectionDetailEl = document.getElementById('selection-detail');
const selectionMaterialsEl = document.getElementById('selection-materials');
const tabShapes = document.getElementById('tab-shapes');
const tabMaterials = document.getElementById('tab-materials');
const shapesView = document.getElementById('shapes-view');
const materialsView = document.getElementById('materials-view');
const shadingSelect = document.getElementById('shading');
const texturesCheck = document.getElementById('textures');
const resetButton = document.getElementById('reset');
const subdivSelect = document.getElementById('subdiv');
const boneSelect = document.getElementById('bone');
const playButton = document.getElementById('play');
const timelineInput = document.getElementById('timeline');
const timeLabel = document.getElementById('time');

const IMAGE_RE = /\.(png|jpe?g|webp|gif|bmp)$/i;

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

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2();

let current = null;
let currentModel = null;
let currentMaterials = [];
let currentMaps = [];
let selectedIndex = -1;
let highlightBox = null;
let highlightWire = null;
let pointerStart = null;
let subdivLevel = 0;
let boneIndex = -1;
let skinData = null; // { root, bones, skeleton, weightByVertex }
let heatMaterial = null;
let playing = false;
let timelineValue = 0;
let lastFrameTime = 0;
let tinyobj = null;
let textureUrls = [];
let textureFiles = new Map();
let shading = 'smooth';
let showTextures = true;

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
        if (material !== fallbackMaterial) {
          disposeMaps(material);
          material.dispose();
        }
      }
    } else if (child.material && child.material !== fallbackMaterial) {
      disposeMaps(child.material);
      child.material.dispose();
    }
  }
}

function disposeMaps(material) {
  const maps = material.userData?.maps;
  if (!maps) return;
  for (const texture of Object.values(maps)) texture?.dispose();
  material.userData.maps = null;
}

function revokeUrls(urls) {
  for (const url of urls) URL.revokeObjectURL(url);
}

function releaseTextures() {
  for (const material of currentMaterials) disposeMaps(material);
  revokeUrls(textureUrls);
  textureUrls = [];
}

function clamp01(v) {
  return v < 0 ? 0 : v > 1 ? 1 : v;
}

function baseName(path) {
  return String(path).replace(/\\/g, '/').split('/').pop().toLowerCase();
}

function populateBoneSelect() {
  boneSelect.replaceChildren();
  const off = document.createElement('option');
  off.value = '-1';
  off.textContent = 'Off';
  boneSelect.append(off);
  if (skinData) {
    skinData.joints.forEach((joint, index) => {
      const option = document.createElement('option');
      option.value = String(index);
      option.textContent = joint.name;
      boneSelect.append(option);
    });
  }
  boneSelect.disabled = !skinData;
  playButton.disabled = !skinData;
  timelineInput.disabled = !skinData;
  boneSelect.value = '-1';
}

function parseSkeleton(lines) {
  const joints = [];
  for (const line of lines) {
    const token = String(line).split(/\s+/);
    if (token[0] === 'skel_joint' && token.length >= 3) {
      const bind = token.length >= 19 ? token.slice(3, 19).map(Number) : null;
      joints.push({
        name: token[1],
        parentName: token[2] === '-' ? null : token[2],
        bind,
        rest: null,
      });
    } else if (token[0] === 'skel_rest' && token.length >= 18 && joints.length) {
      const joint = joints.find((j) => j.name === token[1]);
      if (joint) joint.rest = token.slice(2, 18).map(Number);
    }
  }
  for (const joint of joints) {
    joint.parent = joint.parentName
      ? joints.findIndex((j) => j.name === joint.parentName)
      : -1;
  }
  return joints;
}

function buildSkinData(model) {
  if (!model.skinWeights?.length || !model.skelLines?.length) return null;
  const joints = parseSkeleton(model.skelLines);
  if (!joints.length) return null;
  const bones = joints.map((joint) => {
    const bone = new THREE.Bone();
    bone.name = joint.name;
    const matrix = joint.bind || joint.rest;
    bone.userData.world = matrix?.length === 16
      ? new THREE.Vector3(matrix[12], matrix[13], matrix[14])
      : new THREE.Vector3();
    return bone;
  });
  bones.forEach((bone, i) => {
    const parent = joints[i].parent;
    if (parent >= 0) {
      bone.position.copy(bone.userData.world).sub(bones[parent].userData.world);
      bones[parent].add(bone);
    } else {
      bone.position.copy(bone.userData.world);
    }
  });
  const root = bones.find((bone) => bone.parent === null) || bones[0];
  root.updateMatrixWorld(true);
  return {
    joints,
    bones,
    root,
    skeleton: new THREE.Skeleton(bones),
    weightByVertex: new Map(
      model.skinWeights.map((weight) => [weight.vertexId, weight.joints]),
    ),
  };
}

function attachSkinAttributes(geometry, shape) {
  if (!skinData) return;
  const corners = shape.cornerVertices.length;
  const indices = new Uint16Array(corners * 4);
  const weights = new Float32Array(corners * 4);
  for (let c = 0; c < corners; c++) {
    const joints = skinData.weightByVertex.get(shape.cornerVertices[c]) || [];
    for (let j = 0; j < 4; j++) {
      const src = joints[j];
      const id = src ? src.id : 0;
      indices[c * 4 + j] = id >= 0 && id < skinData.bones.length ? id : 0;
      weights[c * 4 + j] = src ? src.weight : 0;
    }
  }
  geometry.setAttribute('skinIndex', new THREE.Uint16BufferAttribute(indices, 4));
  geometry.setAttribute('skinWeight', new THREE.BufferAttribute(weights, 4));
}

function applyHeatmap() {
  for (const mesh of current?.children || []) {
    const geometry = mesh.geometry;
    mesh.userData.baseMaterials ||= mesh.material;
    if (boneIndex < 0 || !geometry.getAttribute('skinWeight')) {
      mesh.material = mesh.userData.baseMaterials;
      geometry.deleteAttribute('color');
      continue;
    }
    const ia = geometry.getAttribute('skinIndex').array;
    const wa = geometry.getAttribute('skinWeight').array;
    const colors = new Float32Array((ia.length / 4) * 3);
    for (let c = 0; c < colors.length / 3; c++) {
      let weight = 0;
      for (let j = 0; j < 4; j++) {
        if (ia[c * 4 + j] === boneIndex) weight += wa[c * 4 + j];
      }
      const color = new THREE.Color().setHSL((1 - Math.min(weight, 1)) * 0.66, 1, 0.5);
      colors[c * 3] = color.r;
      colors[c * 3 + 1] = color.g;
      colors[c * 3 + 2] = color.b;
    }
    geometry.setAttribute('color', new THREE.BufferAttribute(colors, 3));
    heatMaterial ||= new THREE.MeshPhongMaterial({
      vertexColors: true,
      side: THREE.DoubleSide,
    });
    const maxIndex = geometry.groups.reduce((n, g) => Math.max(n, g.materialIndex), 0);
    mesh.material = Array.from({ length: maxIndex + 1 }, () => heatMaterial);
  }
}

function applyPose() {
  if (!skinData) return;
  const t = timelineValue * Math.PI * 2;
  for (let i = 0; i < skinData.bones.length; i++) {
    skinData.bones[i].rotation.set(
      Math.sin(t + i * 0.7) * 0.12,
      Math.sin(t * 0.5 + i * 1.1) * 0.3,
      Math.cos(t * 0.7 + i * 0.5) * 0.08,
    );
  }
  skinData.root.updateMatrixWorld(true);
  skinData.skeleton.update();
  timelineInput.value = String(Math.round(timelineValue * 1000));
  timeLabel.textContent = `${(timelineValue * 2).toFixed(2)}s`;
}

function loadImageTexture(file, srgb) {
  return new Promise((resolve) => {
    const url = URL.createObjectURL(file);
    textureUrls.push(url);
    const image = new Image();
    image.onload = () => {
      const texture = new THREE.Texture(image);
      texture.colorSpace = srgb ? THREE.SRGBColorSpace : THREE.NoColorSpace;
      texture.wrapS = THREE.RepeatWrapping;
      texture.wrapT = THREE.RepeatWrapping;
      texture.anisotropy = renderer.capabilities.getMaxAnisotropy();
      texture.needsUpdate = true;
      resolve(texture);
    };
    image.onerror = () => resolve(null);
    image.src = url;
  });
}

async function loadMaps(entry) {
  const maps = {};
  await Promise.all(
    Object.entries(entry.textures || {}).map(async ([kind, name]) => {
      const file = textureFiles.get(baseName(name));
      if (!file) return;
      const srgb =
        kind === 'diffuse' || kind === 'emissive' || kind === 'ambient' ||
        kind === 'specular';
      const texture = await loadImageTexture(file, srgb);
      if (texture) maps[kind] = texture;
    }),
  );
  return maps;
}

function applyMaps(material) {
  const maps = material.userData?.maps || {};
  const pickMap = (kind) => (showTextures ? maps[kind] || null : null);
  material.map = pickMap('diffuse');
  material.emissiveMap = pickMap('emissive');
  material.specularMap = pickMap('specular');
  material.normalMap = pickMap('normal');
  material.bumpMap = pickMap('bump');
  material.alphaMap = pickMap('alpha');
}

function applyShading() {
  for (const material of currentMaterials) {
    material.flatShading = shading === 'flat';
    material.wireframe = shading === 'wireframe';
    applyMaps(material);
    material.needsUpdate = true;
  }
}

function materialFor(entry, maps) {
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
  material.userData.maps = maps;
  applyMaps(material);
  return material;
}

function buildGroup(model, maps) {
  const group = new THREE.Group();

  for (const [shapeIndex, shape] of model.shapes.entries()) {
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
    attachSkinAttributes(geometry, shape);

    const materials = model.materials.map((entry, i) =>
      materialFor(entry, maps[i]),
    );
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
    const mesh = skinData
      ? new THREE.SkinnedMesh(geometry, materials)
      : new THREE.Mesh(geometry, materials);
    if (skinData) mesh.bind(skinData.skeleton);
    mesh.userData.shapeIndex = shapeIndex;
    group.add(mesh);
    if (shape.name) group.name = shape.name;
  }

  return group;
}

function fmt(values) {
  return values.map((v) => v.toFixed(2)).join(', ');
}

function materialCard(entry, index) {
  const section = document.createElement('section');
  section.className = 'material';

  const title = document.createElement('div');
  title.className = 'material-title';
  const swatch = document.createElement('span');
  swatch.className = 'swatch';
  const [r, g, b] = entry.diffuse.map((v) => Math.round(clamp01(v) * 255));
  swatch.style.background = `rgb(${r}, ${g}, ${b})`;
  const name = document.createElement('span');
  name.textContent = entry.name || `<material ${index}>`;
  title.append(swatch, name);

  const list = document.createElement('dl');
  const row = (key, value) => {
    const dt = document.createElement('dt');
    dt.textContent = key;
    const dd = document.createElement('dd');
    dd.textContent = value;
    list.append(dt, dd);
  };
  row('Kd', fmt(entry.diffuse));
  row('Ke', fmt(entry.emissive));
  row('Ns', entry.shininess.toFixed(1));
  row('d', entry.dissolve.toFixed(2));
  row('Ni', entry.ior.toFixed(2));
  row('illum', String(entry.illum));
  row('Pr/Pm', `${entry.roughness.toFixed(2)} / ${entry.metallic.toFixed(2)}`);
  const maps = Object.entries(entry.textures || {});
  if (maps.length) row('maps', maps.map(([k, v]) => `${k}: ${v}`).join('\n'));

  section.append(title, list);
  return section;
}

function renderMaterials(model) {
  materialsEl.className = '';
  materialsEl.replaceChildren();
  if (!model.materials.length) {
    materialsEl.textContent = 'No materials in this model';
    materialsEl.className = 'empty';
    return;
  }
  for (const [index, entry] of model.materials.entries()) {
    materialsEl.append(materialCard(entry, index));
  }
}

function renderShapes(model) {
  shapesEl.className = '';
  shapesEl.replaceChildren();
  if (!model.shapes.length) {
    shapesEl.textContent = 'No shapes in this model';
    shapesEl.className = 'empty';
    return;
  }
  model.shapes.forEach((shape, index) => {
    const row = document.createElement('button');
    row.type = 'button';
    row.className = 'shape-row';
    row.textContent = `${shape.name || `shape ${index}`} · ${shape.triangleCount} tris`;
    if (index === selectedIndex) row.classList.add('selected');
    row.addEventListener('click', () => selectShape(index));
    shapesEl.append(row);
  });
}

function clearHighlight() {
  if (highlightWire) {
    highlightWire.parent?.remove(highlightWire);
    highlightWire.material.dispose();
    highlightWire = null;
  }
  if (highlightBox) {
    scene.remove(highlightBox);
    highlightBox.geometry?.dispose();
    highlightBox.material?.dispose();
    highlightBox = null;
  }
}

function updateHighlight() {
  clearHighlight();
  if (selectedIndex < 0 || !current) return;
  const mesh = current.children.find(
    (child) => child.userData.shapeIndex === selectedIndex,
  );
  if (!mesh) return;

  const wire = new THREE.Mesh(
    mesh.geometry,
    new THREE.MeshBasicMaterial({
      color: 0x7cc4ff,
      wireframe: true,
      transparent: true,
      opacity: 0.5,
      depthTest: false,
    }),
  );
  wire.renderOrder = 2;
  mesh.add(wire);
  highlightWire = wire;

  const box = new THREE.Box3().setFromObject(mesh);
  const helper = new THREE.Box3Helper(box, 0x7cc4ff);
  helper.renderOrder = 3;
  scene.add(helper);
  highlightBox = helper;
}

function renderSelection() {
  const shape = currentModel?.shapes[selectedIndex];
  if (!shape) {
    selectionEl.hidden = true;
    return;
  }
  selectionEl.hidden = false;
  selectionDetailEl.replaceChildren();

  const mesh = current?.children.find(
    (child) => child.userData.shapeIndex === selectedIndex,
  );
  const box = mesh ? new THREE.Box3().setFromObject(mesh) : new THREE.Box3();
  const size = box.isEmpty()
    ? new THREE.Vector3()
    : box.getSize(new THREE.Vector3());
  const list = document.createElement('dl');
  const row = (key, value) => {
    const dt = document.createElement('dt');
    dt.textContent = key;
    const dd = document.createElement('dd');
    dd.textContent = value;
    list.append(dt, dd);
  };
  row('name', shape.name || `shape ${selectedIndex}`);
  row('tris', String(shape.triangleCount));
  row('groups', String(shape.groups.length));
  if (shape.tagLines?.length) {
    const tags = parseSubdTags(shape.tagLines);
    row('subd', `${tags.scheme}${tags.creases ? ` · ${tags.creases} creases` : ''}`);
  }
  row('size', `${size.x.toFixed(2)} × ${size.y.toFixed(2)} × ${size.z.toFixed(2)}`);
  selectionDetailEl.append(list);

  selectionMaterialsEl.replaceChildren();
  const ids = [...new Set(shape.groups.map((group) => group.material))];
  if (!ids.length) {
    selectionMaterialsEl.textContent = 'No materials';
    return;
  }
  for (const id of ids) {
    if (id === NO_MATERIAL || id >= currentModel.materials.length) {
      const div = document.createElement('div');
      div.className = 'empty';
      div.textContent = '(no material)';
      selectionMaterialsEl.append(div);
    } else {
      selectionMaterialsEl.append(materialCard(currentModel.materials[id], id));
    }
  }
}

function selectShape(index) {
  if (!currentModel) return;
  selectedIndex = index;
  updateHighlight();
  renderShapes(currentModel);
  renderSelection();
}

function renderPanel(model) {
  renderMaterials(model);
  renderShapes(model);
  renderSelection();
}

function rebuildSubdivision() {
  if (!currentModel || !current) return;
  boneIndex = -1;
  boneSelect.value = '-1';
  applyHeatmap();
  clearHighlight();
  selectedIndex = -1;

  const model = {
    ...currentModel,
    shapes: currentModel.shapes.map((shape) =>
      subdivideShape(shape, subdivLevel),
    ),
  };
  const group = buildGroup(model, currentMaps);
  scene.remove(current);
  disposeObject(current);
  current = group;
  currentMaterials = group.children.flatMap((child) => child.material).filter(
    (material) => material !== fallbackMaterial,
  );
  scene.add(group);
  applyShading();
  applyHeatmap();
  applyPose();
  frame(group);
  renderPanel(model);
}

async function showModel(objFile, mtl, extra) {
  setStatus(`Parsing ${objFile.name}…`);

  const obj = await objFile.arrayBuffer();
  const model = tinyobj.parse(obj, mtl);

  if (skinData?.root) scene.remove(skinData.root);
  skinData?.skeleton.dispose();
  skinData = buildSkinData(model);

  // New textures get their own URL batch; old ones stay alive until the new
  // model is ready so a failed load leaves the current view intact.
  const oldUrls = textureUrls;
  textureUrls = [];
  let maps;
  try {
    maps = await Promise.all(model.materials.map((entry) => loadMaps(entry)));
  } catch (error) {
    revokeUrls(textureUrls);
    textureUrls = oldUrls;
    throw error;
  }
  const group = buildGroup(model, maps);
  currentMaps = maps;
  if (!group.children.length) {
    revokeUrls(textureUrls);
    textureUrls = oldUrls;
    throw new Error('No triangles found in the file.');
  }

  textureFiles = new Map();

  clearHighlight();
  selectedIndex = -1;
  if (current) {
    scene.remove(current);
    disposeObject(current);
  }
  revokeUrls(oldUrls);
  current = group;
  currentModel = model;
  currentMaterials = group.children.flatMap((child) => child.material).filter(
    (material) => material !== fallbackMaterial,
  );
  scene.add(group);
  if (skinData) scene.add(skinData.root);
  boneIndex = -1;
  populateBoneSelect();
  applyShading();
  applyHeatmap();
  applyPose();
  if (subdivLevel > 0) rebuildSubdivision();
  else frame(group);
  renderPanel(model);

  const triangles = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  const parts = [
    `${objFile.name}: ${triangles} triangles`,
    `${model.shapes.length} shape${model.shapes.length === 1 ? '' : 's'}`,
    `${model.materials.length} material${model.materials.length === 1 ? '' : 's'}`,
    ...extra,
    ...(skinData ? [`${skinData.joints.length} bones`] : []),
  ];
  const warnings = model.message.trim();
  setStatus(
    `${parts.join(' · ')}\n${warnings}`.trim(),
    warnings ? 'warn' : 'info',
  );
}

async function handleFiles(list) {
  if (!tinyobj) {
    setStatus('The WebAssembly module is still loading…', 'warn');
    return;
  }
  const all = Array.from(list);
  const objs = all.filter((file) => /\.obj$/i.test(file.name));
  const mtls = all.filter((file) => /\.mtl$/i.test(file.name));
  const images = all.filter((file) => IMAGE_RE.test(file.name));

  if (!objs.length) {
    setStatus('Please choose a .obj file (and optionally its .mtl).', 'error');
    return;
  }

  textureFiles = new Map(images.map((file) => [baseName(file.name), file]));
  const objFile = objs[0];
  const extra = [];
  if (objs.length > 1) extra.push(`+${objs.length - 1} more .obj`);

  let mtl = {};
  if (mtls.length === 1) {
    mtl = { mtl: await mtls[0].arrayBuffer(), mtlName: mtls[0].name };
    extra.push(`mtl ${mtls[0].name}`);
  } else if (mtls.length > 1) {
    const text = (await Promise.all(mtls.map((file) => file.text()))).join('\n');
    mtl = { mtl: new TextEncoder().encode(text), mtlName: '' };
    extra.push(`${mtls.length} mtl files`);
  } else {
    extra.push('no .mtl');
  }
  if (images.length) extra.push(`${images.length} textures`);

  try {
    await showModel(objFile, mtl, extra);
  } catch (error) {
    setStatus(`Failed to load ${objFile.name}: ${error.message}`, 'error');
  }
}

async function readEntry(entry, out) {
  if (entry.isFile) {
    return new Promise((resolve, reject) =>
      entry.file((file) => {
        out.push(file);
        resolve();
      }, reject),
    );
  }
  if (entry.isDirectory) {
    return new Promise((resolve, reject) => {
      const reader = entry.createReader();
      const readBatch = () =>
        reader.readEntries(async (batch) => {
          if (!batch.length) return resolve();
          try {
            await Promise.all(batch.map((child) => readEntry(child, out)));
          } catch (error) {
            return reject(error);
          }
          readBatch();
        }, reject);
      readBatch();
    });
  }
}

async function filesFromDataTransfer(dt) {
  try {
    const entries = Array.from(dt.items || [])
      .map((item) => item.webkitGetAsEntry?.())
      .filter(Boolean);
    if (entries.length) {
      const out = [];
      await Promise.all(entries.map((entry) => readEntry(entry, out)));
      if (out.length) return out;
    }
  } catch {
    /* fall back to the flat file list */
  }
  return Array.from(dt.files || []);
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
  if (event.dataTransfer) {
    filesFromDataTransfer(event.dataTransfer).then(handleFiles);
  }
});

pick.addEventListener('click', () => files.click());
pickFolder.addEventListener('click', () => folder.click());
files.addEventListener('change', () => {
  if (files.files?.length) handleFiles(files.files);
  files.value = '';
});
folder.addEventListener('change', () => {
  if (folder.files?.length) handleFiles(folder.files);
  folder.value = '';
});
shadingSelect.addEventListener('change', () => {
  shading = shadingSelect.value;
  applyShading();
});
texturesCheck.addEventListener('change', () => {
  showTextures = texturesCheck.checked;
  applyShading();
});
resetButton.addEventListener('click', () => {
  if (current) frame(current);
});
subdivSelect.addEventListener('change', () => {
  subdivLevel = Number(subdivSelect.value);
  rebuildSubdivision();
});
boneSelect.addEventListener('change', () => {
  boneIndex = Number(boneSelect.value);
  applyHeatmap();
});
playButton.addEventListener('click', () => {
  playing = !playing;
  playButton.textContent = playing ? '❚❚' : '▶';
});
timelineInput.addEventListener('input', () => {
  timelineValue = Number(timelineInput.value) / 1000;
  applyPose();
});

canvas.addEventListener('pointerdown', (event) => {
  pointerStart = { x: event.clientX, y: event.clientY };
});
canvas.addEventListener('pointerup', (event) => {
  if (!pointerStart || !current) return;
  const moved = Math.hypot(
    event.clientX - pointerStart.x,
    event.clientY - pointerStart.y,
  );
  pointerStart = null;
  if (moved > 5) return; // an orbit drag, not a pick
  const rect = canvas.getBoundingClientRect();
  pointer.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
  pointer.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  const hit = raycaster.intersectObjects(current.children, false)[0];
  selectShape(hit ? hit.object.userData.shapeIndex : -1);
});

function setTab(which) {
  const shapes = which === 'shapes';
  tabShapes.classList.toggle('active', shapes);
  tabMaterials.classList.toggle('active', !shapes);
  shapesView.hidden = !shapes;
  materialsView.hidden = shapes;
}
tabShapes.addEventListener('click', () => setTab('shapes'));
tabMaterials.addEventListener('click', () => setTab('materials'));

document.addEventListener('keydown', (event) => {
  if (event.key === 'o' && (event.ctrlKey || event.metaKey)) {
    event.preventDefault();
    files.click();
  }
});

window.addEventListener('resize', resize);

renderer.setAnimationLoop(() => {
  const now = performance.now();
  if (playing && skinData) {
    const delta = lastFrameTime ? (now - lastFrameTime) / 1000 : 0;
    timelineValue = (timelineValue + delta / 2) % 1;
    applyPose();
  }
  lastFrameTime = now;
  controls.update();
  renderer.render(scene, camera);
});

function disableUi(reason) {
  pick.disabled = true;
  pickFolder.disabled = true;
  resetButton.disabled = true;
  dropzone.textContent = reason;
  setStatus(reason, 'error');
}

window.addEventListener('beforeunload', () => {
  clearHighlight();
  releaseTextures();
  if (current) disposeObject(current);
  renderer.dispose();
});

resize();
setStatus('Loading WebAssembly…');
try {
  tinyobj = await initTinyObj({
    locateFile: (path) => new URL(`../dist/${path}`, import.meta.url).href,
  });
  setStatus('Ready — drop an .obj, a folder, or use “Choose .obj”.');
} catch (error) {
  disableUi(
    `Could not load the WebAssembly module: ${error.message}. ` +
      'Run ./build.sh and serve the web/ directory over HTTP.',
  );
  throw error;
}
