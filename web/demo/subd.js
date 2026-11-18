/**
 * Subdivision preview for the demo. The loader exposes the `t` tags verbatim;
 * this module summarizes them and applies Loop refinement to welded vertices,
 * honouring creases and corners. Material groups stay contiguous, and skin
 * weights are interpolated alongside the corner attributes.
 */

const STRIDE = 8; // must match STRIDE in js/index.js

function normalizeNormal(attr) {
  const length = Math.hypot(attr[3], attr[4], attr[5]);
  if (length > 1e-8) {
    attr[3] /= length;
    attr[4] /= length;
    attr[5] /= length;
  }
  return attr;
}

export function parseSubdTags(lines = []) {
  const info = {
    scheme: 'catmark',
    creases: 0,
    corners: 0,
    holes: 0,
    boundary: null,
    count: lines.length,
    creaseMap: new Map(),
    cornerSet: new Set(),
    holeSet: new Set(),
  };
  for (const raw of lines) {
    const token = String(raw).trim().split(/\s+/);
    if (token[0] !== 't' || token.length < 4) continue;
    const counts = token[2].split('/').map(Number);
    const ni = counts[0] | 0;
    const nf = counts[1] | 0;
    if (token[1] === 'scheme') {
      info.scheme = token[token.length - 1];
    } else if (token[1] === 'interpolateboundary') {
      info.boundary = Number(token[token.length - 1]);
    } else if (token[1] === 'crease') {
      const ints = token.slice(3, 3 + ni).map(Number);
      const sharpCount = nf === 1 ? 1 : ni;
      const sharp = token.slice(3 + ni, 3 + ni + sharpCount).map(Number);
      for (let k = 0; k < Math.floor(ni / 2); k++) {
        const a = ints[2 * k];
        const b = ints[2 * k + 1];
        info.creaseMap.set(
          `${Math.min(a, b)}-${Math.max(a, b)}`,
          sharp[nf === 1 ? 0 : k],
        );
      }
      info.creases += Math.floor(ni / 2);
    } else if (token[1] === 'corner') {
      for (let k = 0; k < ni; k++) info.cornerSet.add(Number(token[3 + k]));
      info.corners += ni;
    } else if (token[1] === 'hole') {
      for (let k = 0; k < ni; k++) info.holeSet.add(Number(token[3 + k]));
      info.holes += ni;
    }
  }
  return info;
}

function isSharpEdge(idA, idB, tags) {
  const sharpness = tags.creaseMap.get(`${Math.min(idA, idB)}-${Math.max(idA, idB)}`);
  return Number.isFinite(sharpness) && sharpness >= 10;
}

export function subdivideShape(shape, levels, maxTriangles = 2_000_000) {
  const tags = parseSubdTags(shape.tagLines);
  let result = shape;
  for (let i = 0; i < levels; i++) {
    if (result.triangleCount * 4 > maxTriangles) break;
    result = subdivideOnce(result, tags);
  }
  return result;
}

function buildLocal(shape, group) {
  const lookup = new Map();
  const positions = [];
  const ids = [];
  const skins = [];
  const triangles = [];
  for (let tri = group.start; tri < group.start + group.count; tri++) {
    const local = [];
    for (let k = 0; k < 3; k++) {
      const corner = tri * 3 + k;
      const id = shape.cornerVertices[corner];
      let index = lookup.get(id);
      if (index === undefined) {
        index = positions.length;
        lookup.set(id, index);
        ids.push(id);
        positions.push(
          shape.vertices.slice(corner * STRIDE, (corner + 1) * STRIDE),
        );
        skins.push(
          shape.cornerSkin
            ? shape.cornerSkin.slice(corner * 8, corner * 8 + 8)
            : new Float32Array(8),
        );
      }
      local.push(index);
    }
    triangles.push(local);
  }
  return { positions, ids, skins, triangles };
}

function averageSkin(skins, indices) {
  const out = new Float32Array(8);
  for (const index of indices) {
    for (let k = 0; k < 8; k++) out[k] += skins[index][k] / indices.length;
  }
  // The first four slots are joint ids (integers), the last four are weights.
  let total = 0;
  for (let k = 4; k < 8; k++) total += out[k];
  if (total > 0) for (let k = 4; k < 8; k++) out[k] /= total;
  return out;
}

function subdivideOnce(shape, tags) {
  const outVertices = new Float32Array(shape.triangleCount * 4 * 3 * STRIDE);
  const outCorners = new Uint32Array(shape.triangleCount * 4 * 3);
  const outSkin = shape.cornerSkin
    ? new Float32Array(shape.triangleCount * 4 * 3 * 8)
    : null;
  const outGroups = [];
  let outTri = 0;

  const emit = (tri, attrs, ids, skins) => {
    for (let k = 0; k < 3; k++) {
      const dst = tri * 3 + k;
      outVertices.set(attrs[k], dst * STRIDE);
      outCorners[dst] = ids[k];
      if (outSkin && skins) outSkin.set(skins[k], dst * 8);
    }
  };

  for (const group of shape.groups) {
    const { positions, ids, skins, triangles } = buildLocal(shape, group);
    const start = outTri;
    if (!triangles.length) {
      outGroups.push({ ...group, start, count: 0 });
      continue;
    }

    const neighbors = positions.map(() => new Set());
    const edges = new Map();
    for (const [face, tri] of triangles.entries()) {
      for (const [a, b] of [
        [tri[0], tri[1]],
        [tri[1], tri[2]],
        [tri[2], tri[0]],
      ]) {
        const key = `${Math.min(a, b)}-${Math.max(a, b)}`;
        let edge = edges.get(key);
        if (!edge) {
          edge = { a: Math.min(a, b), b: Math.max(a, b), faces: [], opposite: [] };
          edges.set(key, edge);
        }
        edge.faces.push(face);
        edge.opposite.push(tri.find((v) => v !== a && v !== b));
        neighbors[a].add(b);
        neighbors[b].add(a);
      }
    }

    const boundary = positions.map(() => false);
    for (const edge of edges.values()) {
      if (edge.faces.length === 1) {
        boundary[edge.a] = true;
        boundary[edge.b] = true;
      }
    }

    const updated = positions.map((position, vertex) => {
      const adjacent = neighbors[vertex];
      const sharpCorner =
        tags.cornerSet.has(ids[vertex]) ||
        [...adjacent].every((other) => isSharpEdge(ids[vertex], ids[other], tags));
      if (!adjacent.size || sharpCorner) return position.slice();
      const beta = (boundary[vertex] ? 0.125 : 0.375) / adjacent.size;
      const resultAttr = new Float32Array(STRIDE);
      for (let k = 0; k < STRIDE; k++) resultAttr[k] = position[k] * (1 - adjacent.size * beta);
      for (const other of adjacent) {
        for (let k = 0; k < STRIDE; k++) resultAttr[k] += positions[other][k] * beta;
      }
      return normalizeNormal(resultAttr);
    });

    const edgePoints = new Map();
    const edgeSkins = new Map();
    for (const [key, edge] of edges) {
      const point = new Float32Array(STRIDE);
      const sharp = edge.faces.length === 1 || isSharpEdge(ids[edge.a], ids[edge.b], tags);
      if (sharp) {
        for (let k = 0; k < STRIDE; k++) {
          point[k] = (positions[edge.a][k] + positions[edge.b][k]) * 0.5;
        }
      } else {
        const o0 = positions[edge.opposite[0]];
        const o1 = positions[edge.opposite[1]];
        for (let k = 0; k < STRIDE; k++) {
          point[k] =
            0.375 * (positions[edge.a][k] + positions[edge.b][k]) +
            0.125 * (o0[k] + o1[k]);
        }
      }
      edgePoints.set(key, normalizeNormal(point));
      if (outSkin) {
        edgeSkins.set(key, averageSkin(skins, [edge.a, edge.b]));
      }
    }
    const edgePoint = (a, b) => edgePoints.get(`${Math.min(a, b)}-${Math.max(a, b)}`);
    const edgeSkin = (a, b) => edgeSkins.get(`${Math.min(a, b)}-${Math.max(a, b)}`);

    for (const tri of triangles) {
      const [a, b, c] = tri;
      const ab = edgePoint(a, b);
      const bc = edgePoint(b, c);
      const ca = edgePoint(a, c);
      const skinAB = edgeSkin?.(a, b);
      const skinBC = edgeSkin?.(b, c);
      const skinCA = edgeSkin?.(a, c);
      const emitTri = (attrs, origins, skinAttrs) =>
        emit(outTri, attrs, origins, skinAttrs);
      emitTri([updated[a], ab, ca], [ids[a], ids[a], ids[a]], [skins[a], skinAB, skinCA]);
      emitTri([ab, updated[b], bc], [ids[a], ids[b], ids[b]], [skinAB, skins[b], skinBC]);
      emitTri([ca, bc, updated[c]], [ids[a], ids[b], ids[c]], [skinCA, skinBC, skins[c]]);
      emitTri([ab, bc, ca], [ids[a], ids[b], ids[a]], [skinAB, skinBC, skinCA]);
      outTri += 4;
    }
    outGroups.push({ ...group, start, count: outTri - start });
  }

  const result = {
    ...shape,
    vertices: outVertices,
    cornerVertices: outCorners,
    triangleCount: outTri,
    groups: outGroups,
  };
  if (shape.cornerSkin) result.cornerSkin = outSkin;
  return result;
}
