/**
 * Minimal MaterialX-in-MTL reader for the demo: resolves a surface shader's
 * constant inputs and image-node connections into the handful of values that
 * Three.js MeshPhysicalMaterial understands. Classic MTL/PBR keys stay as the
 * fallback; malformed or unsupported graphs simply yield no override.
 */

const ALIASES = {
  baseColor: ['base_color', 'diffuse', 'albedo', 'baseColor'],
  metallic: ['base_metalness', 'metallic', 'metalness'],
  roughness: ['specular_roughness', 'roughness'],
  transmission: ['transmission', 'transmittance'],
  ior: ['specular_ior', 'ior'],
  clearcoat: ['coat_weight', 'clearcoat', 'clear_coat'],
  clearcoatRoughness: ['coat_roughness', 'clearcoat_roughness'],
  sheen: ['sheen_weight', 'sheen'],
  emissive: ['emission', 'emissive'],
  normal: ['normal'],
};

function parseValue(text) {
  const parts = text.split(/[\s,]+/).map(Number).filter(Number.isFinite);
  if (!parts.length) return null;
  return parts.length === 1 ? parts[0] : parts;
}

export function parseMtlx(lines = []) {
  const nodes = new Map();
  let surface = null;
  for (const raw of lines) {
    const tokens = String(raw).match(/"[^"]*"|\S+/g) || [];
    if (tokens[0] === 'mtlx_surface' && tokens.length >= 3) {
      surface = { name: tokens[1], category: tokens[2] };
    } else if (tokens[0] === 'mtlx_node' && tokens.length >= 4) {
      nodes.set(tokens[1], {
        name: tokens[1], category: tokens[2], type: tokens[3], inputs: {},
      });
    } else if (tokens[0] === 'mtlx_input' && tokens.length >= 4) {
      const dot = tokens[1].indexOf('.');
      if (dot < 0) continue;
      const nodeName = tokens[1].slice(0, dot);
      const port = tokens[1].slice(dot + 1);
      if (!nodes.has(nodeName)) nodes.set(nodeName, { name: nodeName, inputs: {} });
      const text = tokens.slice(3).join(' ').replace(/^"(.*)"$/, '$1');
      const connection = tokens.length === 4 && text.startsWith('@')
        ? text.slice(1).split('.')[0]
        : null;
      nodes.get(nodeName).inputs[port] = {
        type: tokens[2],
        value: connection ? null : text,
        connection,
      };
    }
  }
  return { surface, nodes };
}

export function resolveMtlx(lines) {
  const { surface, nodes } = parseMtlx(lines);
  if (!surface) return null;
  const shader = nodes.get(surface.name);
  if (!shader) return null;
  const result = { category: surface.category, values: {}, images: {} };
  for (const [role, aliases] of Object.entries(ALIASES)) {
    const input = aliases.map((name) => shader.inputs[name]).find(Boolean);
    if (!input) continue;
    if (input.connection) {
      const source = nodes.get(input.connection);
      const file = source?.inputs.file?.value || source?.inputs.filename?.value;
      if (file) result.images[role] = file;
    } else if (input.value !== null) {
      const value = parseValue(input.value);
      if (value !== null) result.values[role] = value;
    }
  }
  return result;
}
