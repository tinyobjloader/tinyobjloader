/**
 * Headless smoke test for the built wasm package.
 *
 *   node test/smoke.mjs      (run from web/, after ./build.sh)
 *
 * Uses the real npm entry point (`js/index.js`) and the real model files.
 */
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

import { initTinyObj, STRIDE, NO_MATERIAL } from '../js/index.js';

const here = path.dirname(fileURLToPath(import.meta.url));
const repo = path.resolve(here, '..', '..');

let failures = 0;
function check(cond, message) {
  if (!cond) {
    failures++;
    console.error(`FAIL: ${message}`);
  }
  return cond;
}

async function load(name) {
  return readFile(path.join(repo, 'models', name));
}

function checkShape(shapes, label) {
  for (const [i, shape] of shapes.entries()) {
    check(shape.vertices instanceof Float32Array, `${label}: shape ${i} vertices type`);
    check(
      shape.vertices.length === shape.triangleCount * 3 * STRIDE,
      `${label}: shape ${i} has ${shape.vertices.length} floats for ` +
        `${shape.triangleCount} triangles`,
    );
    let covered = 0;
    for (const [g, group] of shape.groups.entries()) {
      check(group.start === covered, `${label}: shape ${i} group ${g} start`);
      check(group.count > 0, `${label}: shape ${i} group ${g} empty`);
      covered += group.count;
    }
    check(covered === shape.triangleCount, `${label}: shape ${i} groups cover all triangles`);
    for (let v = 0; v < shape.vertices.length; v += STRIDE) {
      const nx = shape.vertices[v + 3];
      const ny = shape.vertices[v + 4];
      const nz = shape.vertices[v + 5];
      const len2 = nx * nx + ny * ny + nz * nz;
      check(len2 > 0.98 && len2 < 1.02, `${label}: shape ${i} corner ${v / STRIDE} normal`);
    }
  }
}

const tinyobj = await initTinyObj();

/* --- cube.obj + cube.mtl ------------------------------------------------- */
{
  const obj = await load('cube.obj');
  const mtl = await load('cube.mtl');
  const model = tinyobj.parse(obj, { mtl, mtlName: 'cube.mtl' });

  const tris = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  check(tris === 12, `cube: ${tris} triangles, want 12`);
  check(model.materials.length === 5, `cube: ${model.materials.length} materials, want 5`);
  check(model.materials.map((m) => m.name).join(',') === 'white,red,green,blue,light',
    `cube: material names ${model.materials.map((m) => m.name)}`);
  const white = model.materials[0];
  check(white.diffuse.join(',') === '1,1,1', `cube: white diffuse ${white.diffuse}`);
  const red = model.materials[1];
  check(red.diffuse.join(',') === '1,0,0', `cube: red diffuse ${red.diffuse}`);
  const groupMaterials = new Set(
    model.shapes.flatMap((s) => s.groups.map((g) => g.material)),
  );
  check(groupMaterials.has(1) && groupMaterials.has(2),
    `cube: expected red and green draw groups, got ${[...groupMaterials]}`);
  check(model.message === '', `cube: unexpected warnings: ${model.message}`);
  checkShape(model.shapes, 'cube');
}

/* --- cornell_box.obj, mtl name omitted ---------------------------------- */
{
  const obj = await load('cornell_box.obj');
  const mtl = await load('cornell_box.mtl');
  const model = tinyobj.parse(obj, { mtl });
  const tris = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  check(tris === 36, `cornell: ${tris} triangles, want 36`);
  check(model.materials.length === 5, `cornell: ${model.materials.length} materials`);
  checkShape(model.shapes, 'cornell');
}

/* --- n-gon: one 10-gon must tessellate into n-2 = 8 triangles ----------- */
{
  const obj = await load('issue-319-003.obj');
  const model = tinyobj.parse(obj);
  const tris = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  check(tris === 8, `issue-319-003: ${tris} triangles, want 8`);
  checkShape(model.shapes, 'issue-319-003');
}

/* --- quads with texcoords ----------------------------------------------- */
{
  const obj = await load('issue-295-trianguation-failure.obj');
  const model = tinyobj.parse(obj);
  const tris = model.shapes.reduce((n, s) => n + s.triangleCount, 0);
  check(tris > 0, 'issue-295: no triangles');
  checkShape(model.shapes, 'issue-295');
  let uvSeen = 0;
  for (const shape of model.shapes) {
    for (let v = 0; v < shape.vertices.length; v += STRIDE) {
      const u = shape.vertices[v + 6];
      const w = shape.vertices[v + 7];
      check(u >= -0.001 && u <= 1.001, `issue-295: u ${u} out of range`);
      check(w >= -0.001 && w <= 1.001, `issue-295: v ${w} out of range`);
      if (u !== 0 || w !== 0) uvSeen++;
    }
  }
  check(uvSeen > 0, 'issue-295: no texcoords decoded');
}

/* --- string input + mtl-less object ------------------------------------- */
{
  const model = tinyobj.parse('v 0 0 0\nv 1 0 0\nv 0 1 0\nv 0 0 1\nf 1 2 3\nf 1 2 4\n');
  check(model.shapes.length === 1, `inline: ${model.shapes.length} shapes, want 1`);
  check(model.shapes[0].triangleCount === 2, 'inline: triangle count');
  check(model.shapes[0].groups.length === 1, 'inline: group count');
  check(model.shapes[0].groups[0].material === NO_MATERIAL,
    `inline: material id ${model.shapes[0].groups[0].material}`);
  checkShape(model.shapes, 'inline');
}

/* --- failures surface as thrown errors ---------------------------------- */
{
  let threw = false;
  try {
    tinyobj.parse(new Uint8Array());
  } catch (error) {
    threw = /empty/i.test(error.message);
  }
  check(threw, 'empty input should throw');

  let result = null;
  try {
    tinyobj.parse('mtllib nope.mtl\nv 0 0 0\nv 1 0 0\nv 0 1 0\nf 1 2 3\n', {
      mtl: new TextEncoder().encode(''),
      mtlName: 'nope.mtl',
    });
  } catch (error) {
    result = error;
  }
  check(result === null || result instanceof Error, 'malformed mtl should not crash');

  try {
    tinyobj.parse('f 1 2 3\nf 4 5 6\n');
  } catch (error) {
    check(error.result !== undefined, 'error.result should carry the C result code');
    check(error.message.length > 0, 'error.message should be populated');
  }
}

/* --- handle reuse ------------------------------------------------------- */
{
  const obj = await load('cube.obj');
  for (let i = 0; i < 25; i++) {
    const model = tinyobj.parse(obj);
    check(model.shapes.length > 0, `iter ${i}: empty result`);
  }
}

tinyobj.dispose();

if (failures) {
  console.error(`\n${failures} check(s) failed`);
  process.exit(1);
}
console.log('smoke: all checks passed');
