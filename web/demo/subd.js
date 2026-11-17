/**
 * Lightweight subdivision preview for the demo. The loader exposes the `t`
 * tags verbatim; this module summarizes them and applies linear (bilinear)
 * midpoint refinement, which keeps material groups contiguous.
 */

export function parseSubdTags(lines = []) {
  const info = {
    scheme: 'catmark',
    creases: 0,
    corners: 0,
    holes: 0,
    boundary: null,
    count: lines.length,
  };
  for (const raw of lines) {
    const token = String(raw).trim().split(/\s+/);
    if (token[0] !== 't' || token.length < 3) continue;
    const counts = Number(token[2].split('/')[0]) || 0;
    if (token[1] === 'scheme') info.scheme = token[token.length - 1];
    else if (token[1] === 'interpolateboundary')
      info.boundary = Number(token[token.length - 1]);
    else if (token[1] === 'crease') info.creases += Math.max(1, Math.floor(counts / 2));
    else if (token[1] === 'corner') info.corners += counts;
    else if (token[1] === 'hole') info.holes += counts;
  }
  return info;
}

export function subdivideShape(shape, levels, maxTriangles = 2_000_000) {
  let result = shape;
  for (let i = 0; i < levels; i++) {
    if (result.triangleCount * 4 > maxTriangles) break;
    result = subdivideOnce(result);
  }
  return result;
}

function subdivideOnce(shape) {
  const stride = 8; // must match STRIDE in js/index.js
  const vertices = shape.vertices;
  const cornerIds = shape.cornerVertices;
  const total = shape.triangleCount;
  const outVertices = new Float32Array(total * 4 * 3 * stride);
  const outCorners = new Uint32Array(total * 4 * 3);
  const outGroups = [];
  let outTri = 0;

  const midpoint = (a, b) => {
    const value = new Float32Array(stride);
    for (let i = 0; i < stride; i++) {
      value[i] = (vertices[a * stride + i] + vertices[b * stride + i]) * 0.5;
    }
    const length = Math.hypot(value[3], value[4], value[5]);
    if (length > 1e-8) {
      value[3] /= length;
      value[4] /= length;
      value[5] /= length;
    }
    return value;
  };

  const emit = (tri, attrs, sources) => {
    for (let k = 0; k < 3; k++) {
      const dst = tri * 3 + k;
      outVertices.set(attrs[k], dst * stride);
      outCorners[dst] = cornerIds[sources[k]];
    }
  };

  for (const group of shape.groups) {
    const start = outTri;
    for (let tri = group.start; tri < group.start + group.count; tri++) {
      const a = tri * 3;
      const b = a + 1;
      const c = a + 2;
      const ab = midpoint(a, b);
      const bc = midpoint(b, c);
      const ca = midpoint(c, a);
      const vert = (i) => vertices.subarray(i * stride, (i + 1) * stride);
      emit(outTri, [vert(a), ab, ca], [a, a, a]);
      emit(outTri + 1, [ab, vert(b), bc], [a, b, b]);
      emit(outTri + 2, [ca, bc, vert(c)], [a, b, c]);
      emit(outTri + 3, [ab, bc, ca], [a, b, a]);
      outTri += 4;
    }
    outGroups.push({ ...group, start, count: outTri - start });
  }

  return {
    ...shape,
    vertices: outVertices,
    cornerVertices: outCorners,
    triangleCount: outTri,
    groups: outGroups,
  };
}
