"""MaterialX-in-MTL <-> Blender node trees (Principled BSDF + a node subset).

Supported MaterialX nodes and their Blender counterparts:
  image / tiledimage   Image Texture (float: + Separate Color, red)
  normalmap            Normal Map
  constant             RGB (color3) / Value (float)
  multiply/add/subtract  Math (float) / Mix color (color3)
  mix                  Mix (float or color3; A = bg, B = fg, Factor = mix)
  texcoord             UV Map
Surface shaders: open_pbr_surface, standard_surface, gltf_pbr,
UsdPreviewSurface (all become a Principled BSDF; the category is kept in the
material's `obj_mtlx_surface` property and used again on export).

On import every mapped Principled input is first set to the MaterialX default
of the surface shader, so export writes only values that differ from it.
Anything else is reported and left out; the classic MTL keys are always read
(fallback) and written.
"""
import os

from . import mtlx

# surface category -> [(mtlx input, type, Principled socket, scale, MaterialX default)]
_C = "color3"
_F = "float"
SURFACES = {
    "open_pbr_surface": [
        ("base_color", _C, "Base Color", 1, (0.8, 0.8, 0.8)),
        ("base_metalness", _F, "Metallic", 1, 0.0),
        ("specular_weight", _F, "Specular IOR Level", 0.5, 1.0),
        ("specular_roughness", _F, "Roughness", 1, 0.3),
        ("specular_ior", _F, "IOR", 1, 1.5),
        ("specular_anisotropy", _F, "Anisotropic", 1, 0.0),
        ("transmission_weight", _F, "Transmission Weight", 1, 0.0),
        ("subsurface_weight", _F, "Subsurface Weight", 1, 0.0),
        ("fuzz_weight", _F, "Sheen Weight", 1, 0.0),
        ("fuzz_color", _C, "Sheen Tint", 1, (1.0, 1.0, 1.0)),
        ("coat_weight", _F, "Coat Weight", 1, 0.0),
        ("coat_roughness", _F, "Coat Roughness", 1, 0.0),
        ("coat_ior", _F, "Coat IOR", 1, 1.6),
        ("emission_luminance", _F, "Emission Strength", 1, 0.0),
        ("emission_color", _C, "Emission Color", 1, (1.0, 1.0, 1.0)),
        ("geometry_opacity", _F, "Alpha", 1, 1.0),
        ("geometry_normal", "vector3", "Normal", 1, None)],
    "standard_surface": [
        ("base_color", _C, "Base Color", 1, (0.8, 0.8, 0.8)),
        ("metalness", _F, "Metallic", 1, 0.0),
        ("specular", _F, "Specular IOR Level", 0.5, 1.0),
        ("specular_roughness", _F, "Roughness", 1, 0.2),
        ("specular_IOR", _F, "IOR", 1, 1.5),
        ("specular_anisotropy", _F, "Anisotropic", 1, 0.0),
        ("transmission", _F, "Transmission Weight", 1, 0.0),
        ("subsurface", _F, "Subsurface Weight", 1, 0.0),
        ("sheen", _F, "Sheen Weight", 1, 0.0),
        ("sheen_color", _C, "Sheen Tint", 1, (1.0, 1.0, 1.0)),
        ("coat", _F, "Coat Weight", 1, 0.0),
        ("coat_roughness", _F, "Coat Roughness", 1, 0.1),
        ("coat_IOR", _F, "Coat IOR", 1, 1.5),
        ("emission", _F, "Emission Strength", 1, 0.0),
        ("emission_color", _C, "Emission Color", 1, (1.0, 1.0, 1.0)),
        ("normal", "vector3", "Normal", 1, None)],
    "gltf_pbr": [
        ("base_color", _C, "Base Color", 1, (1.0, 1.0, 1.0)),
        ("metallic", _F, "Metallic", 1, 1.0),
        ("roughness", _F, "Roughness", 1, 1.0),
        ("ior", _F, "IOR", 1, 1.5),
        ("transmission", _F, "Transmission Weight", 1, 0.0),
        ("clearcoat", _F, "Coat Weight", 1, 0.0),
        ("clearcoat_roughness", _F, "Coat Roughness", 1, 0.0),
        ("emissive", _C, "Emission Color", 1, (0.0, 0.0, 0.0)),
        ("emissive_strength", _F, "Emission Strength", 1, 1.0),
        ("alpha", _F, "Alpha", 1, 1.0),
        ("normal", "vector3", "Normal", 1, None)],
    "UsdPreviewSurface": [
        ("diffuseColor", _C, "Base Color", 1, (0.18, 0.18, 0.18)),
        ("metallic", _F, "Metallic", 1, 0.0),
        ("roughness", _F, "Roughness", 1, 0.5),
        ("ior", _F, "IOR", 1, 1.5),
        ("clearcoat", _F, "Coat Weight", 1, 0.0),
        ("clearcoatRoughness", _F, "Coat Roughness", 1, 0.01),
        ("emissiveColor", _C, "Emission Color", 1, (0.0, 0.0, 0.0)),
        ("opacity", _F, "Alpha", 1, 1.0),
        ("normal", "vector3", "Normal", 1, None)],
}
# Emission Strength has no UsdPreviewSurface input: imported as 1.0
FIXED = {"UsdPreviewSurface": {"Emission Strength": 1.0}}

MATH_OPS = {"multiply": "MULTIPLY", "add": "ADD", "subtract": "SUBTRACT"}


def _floats(text):
    return [float(x) for x in text.split(",")]


def _socket_value(sock, ty, value):
    v = _floats(value)
    if ty == _C:
        sock.default_value = (v[0], v[1], v[2], 1.0) if len(sock.default_value) == 4 else v[:3]
    elif ty == _F:
        sock.default_value = v[0] if not hasattr(sock.default_value, "__len__") else (v[0],) * len(sock.default_value)
    else:
        sock.default_value = v[:len(sock.default_value)]


def _load_image(bpy, path, base_dir):
    full = path if os.path.isabs(path) else os.path.join(base_dir, path)
    try:
        return bpy.data.images.load(full, check_existing=True)
    except RuntimeError:
        img = bpy.data.images.new(os.path.basename(path) or "missing", 1, 1)
        img.source = 'FILE'
        img.filepath = full
        return img


# ---------------------------------------------------------------- import

def build_material(bpy, mat, m, classic, base_dir, warn):
    """Fill Blender material `mat` from an accepted mtlx.Material `m`
    (or from the classic keys when `m` is None)."""
    mat.use_nodes = True
    nt = mat.node_tree
    nt.nodes.clear()
    out = nt.nodes.new("ShaderNodeOutputMaterial")
    out.location = (400, 0)
    bsdf = nt.nodes.new("ShaderNodeBsdfPrincipled")
    nt.links.new(bsdf.outputs["BSDF"], out.inputs["Surface"])
    if m is None:
        _build_classic(bpy, nt, bsdf, classic, base_dir)
        return
    cat = m.surface[0][1]
    table = SURFACES.get(cat)
    if table is None:
        warn(f"{mat.name}: surface shader '{cat}' is not supported; using the classic keys")
        _build_classic(bpy, nt, bsdf, classic, base_dir)
        return
    mat["obj_mtlx_surface"] = cat
    if m.versions:
        mat["obj_mtlx_version"] = m.versions[0]
    if m.includes:
        mat["obj_mtlx_includes"] = "\n".join(m.includes)
    by_port = {e[0]: e for e in table}
    for (port, ty, sock, scale, default) in table:
        if default is not None:
            _socket_value(bsdf.inputs[sock], ty, ", ".join(map(str, (default if isinstance(default, tuple) else (default,)))))
            if scale != 1:
                bsdf.inputs[sock].default_value *= scale
    for sock, v in FIXED.get(cat, {}).items():
        bsdf.inputs[sock].default_value = v

    types = {n: t for (n, _, t) in m.nodes}
    cats = {n: c for (n, c, _) in m.nodes}
    consts = {}
    for (n, p, t, v) in m.inputs:
        consts.setdefault(n, {})[p] = (t, v)
    conns = {}
    for (src, _, dst, p, t) in m.conns:
        conns.setdefault(dst, {})[p] = src
    cspace = {(n, p): cs for (n, p, cs) in m.colorspaces}
    made = {}

    def node_out(n):
        """Blender output socket producing MaterialX node `n`, or None."""
        if n in made:
            return made[n]
        cat, ty = cats[n], types[n]
        ins, links = consts.get(n, {}), conns.get(n, {})
        sock = None
        if cat in ("image", "tiledimage") and ty in ("color3", "color4", "float", "vector3", "vector4"):
            tex = nt.nodes.new("ShaderNodeTexImage")
            tex.label = n
            if "file" in ins:
                img = _load_image(bpy, ins["file"][1], base_dir)
                cs = cspace.get((n, "file"))
                if cs == "srgb_texture":
                    img.colorspace_settings.name = "sRGB"
                elif ty == "float" or ty.startswith("vector"):
                    img.colorspace_settings.name = "Non-Color"
                else:
                    img.colorspace_settings.name = "Linear Rec.709"
                tex.image = img
            if ins.get("uaddressmode", ("", "periodic"))[1] == "clamp":
                tex.extension = 'EXTEND'
            if "texcoord" in links:
                uv = node_out(links["texcoord"])
                if uv is not None:
                    nt.links.new(uv, tex.inputs["Vector"])
            if cat == "tiledimage":
                warn(f"{mat.name}: tiledimage '{n}' imported as image (tiling not converted)")
            sock = tex.outputs["Color"]
            if ty == "float":
                sep = nt.nodes.new("ShaderNodeSeparateColor")
                nt.links.new(sock, sep.inputs["Color"])
                sock = sep.outputs["Red"]
        elif cat == "normalmap" and ty == "vector3":
            nm = nt.nodes.new("ShaderNodeNormalMap")
            nm.label = n
            if "in" in links:
                src = node_out(links["in"])
                if src is not None:
                    nt.links.new(src, nm.inputs["Color"])
            if "scale" in ins:
                nm.inputs["Strength"].default_value = _floats(ins["scale"][1])[0]
            sock = nm.outputs["Normal"]
        elif cat == "constant" and ty in (_C, _F):
            c = nt.nodes.new("ShaderNodeRGB" if ty == _C else "ShaderNodeValue")
            c.label = n
            if "value" in ins:
                v = _floats(ins["value"][1])
                c.outputs[0].default_value = (v[0], v[1], v[2], 1.0) if ty == _C else v[0]
            sock = c.outputs[0]
        elif cat in MATH_OPS and ty in (_C, _F):
            if ty == _F:
                op = nt.nodes.new("ShaderNodeMath")
                op.operation = MATH_OPS[cat]
                slots = [op.inputs[0], op.inputs[1]]
                sock = op.outputs[0]
            else:
                op = nt.nodes.new("ShaderNodeMix")
                op.data_type = 'RGBA'
                op.blend_type = MATH_OPS[cat]
                op.inputs["Factor"].default_value = 1.0
                slots = [op.inputs[6], op.inputs[7]]  # A, B (color)
                sock = op.outputs[2]
            op.label = n
            for port, slot in zip(("in1", "in2"), slots):
                if port in links:
                    src = node_out(links[port])
                    if src is not None:
                        nt.links.new(src, slot)
                elif port in ins:
                    _socket_value(slot, ins[port][0], ins[port][1])
        elif cat == "mix" and ty in (_C, _F):
            op = nt.nodes.new("ShaderNodeMix")
            op.label = n
            op.data_type = 'RGBA' if ty == _C else 'FLOAT'
            a, b = (op.inputs[6], op.inputs[7]) if ty == _C else (op.inputs[2], op.inputs[3])
            sock = op.outputs[2] if ty == _C else op.outputs[0]
            for port, slot in (("bg", a), ("fg", b), ("mix", op.inputs["Factor"])):
                if port in links:
                    src = node_out(links[port])
                    if src is not None:
                        nt.links.new(src, slot)
                elif port in ins:
                    _socket_value(slot, ins[port][0], ins[port][1])
        elif cat == "texcoord" and ty == "vector2":
            uvn = nt.nodes.new("ShaderNodeUVMap")
            uvn.label = n
            sock = uvn.outputs["UV"]
        else:
            warn(f"{mat.name}: node '{n}' ({cat} {ty}) is not supported; its connections are dropped")
        made[n] = sock
        return sock

    surf = m.surf_name
    for p, (t, v) in consts.get(surf, {}).items():
        if p in by_port:
            _, ty, sock, scale, _ = by_port[p]
            _socket_value(bsdf.inputs[sock], ty, v)
            if scale != 1:
                bsdf.inputs[sock].default_value *= scale
        else:
            warn(f"{mat.name}: input '{p}' of {cat} is not mapped to Blender; dropped")
    for p, src in conns.get(surf, {}).items():
        if p not in by_port:
            warn(f"{mat.name}: input '{p}' of {cat} is not mapped to Blender; dropped")
            continue
        s = node_out(src)
        if s is not None:
            nt.links.new(s, bsdf.inputs[by_port[p][2]])
    _layout(nt, out)


def _build_classic(bpy, nt, bsdf, classic, base_dir):
    def num(key, n):
        v = classic.get(key)
        try:
            return [float(x) for x in v[:n]] if v and len(v) >= n else None
        except ValueError:
            return None
    kd = num("Kd", 3)
    if kd:
        bsdf.inputs["Base Color"].default_value = (*kd, 1.0)
    for key, sock in (("Pr", "Roughness"), ("Pm", "Metallic"), ("d", "Alpha")):
        v = num(key, 1)
        if v:
            bsdf.inputs[sock].default_value = v[0]
    ke = num("Ke", 3)
    if ke and any(ke):
        bsdf.inputs["Emission Color"].default_value = (*ke, 1.0)
        bsdf.inputs["Emission Strength"].default_value = 1.0
    for key, sock, data in (("map_Kd", "Base Color", False), ("map_Pr", "Roughness", True),
                            ("map_Pm", "Metallic", True)):
        if classic.get(key):
            tex = nt.nodes.new("ShaderNodeTexImage")
            tex.image = _load_image(bpy, classic[key][-1], base_dir)
            if data:
                tex.image.colorspace_settings.name = "Non-Color"
            nt.links.new(tex.outputs["Color"], bsdf.inputs[sock])
    nrm = classic.get("norm") or classic.get("map_Bump") or classic.get("bump")
    if nrm:
        tex = nt.nodes.new("ShaderNodeTexImage")
        tex.image = _load_image(bpy, nrm[-1], base_dir)
        tex.image.colorspace_settings.name = "Non-Color"
        nm = nt.nodes.new("ShaderNodeNormalMap")
        nt.links.new(tex.outputs["Color"], nm.inputs["Color"])
        nt.links.new(nm.outputs["Normal"], bsdf.inputs["Normal"])


def _layout(nt, out):
    depth = {out: 0}
    stack = [out]
    while stack:
        n = stack.pop()
        for s in n.inputs:
            for l in s.links:
                if depth.get(l.from_node, -1) < depth[n] + 1:
                    depth[l.from_node] = depth[n] + 1
                    stack.append(l.from_node)
    rows = {}
    for n, d in depth.items():
        rows.setdefault(d, []).append(n)
        n.location = (400 - 300 * d, -250 * (len(rows[d]) - 1))


# ---------------------------------------------------------------- export

def _name_ok(s):
    return mtlx.valid_name(s)


def _fmt(x):
    s = f"{x:.6g}"
    return "0" if s == "-0" else s


def _vals(v, n):
    return " ".join(_fmt(x) for x in list(v)[:n])


def _differs(a, b):
    if isinstance(b, tuple):
        return any(abs(x - y) > 1e-6 for x, y in zip(a, b))
    return abs(a - b) > 1e-6


def material_lines(bpy, mat, mtl_dir, warn):
    """(classic [(key, value)], mtlx lines) for Blender material `mat`."""
    nt = mat.node_tree if mat.use_nodes else None
    bsdf = None
    if nt is not None:
        out = next((n for n in nt.nodes if n.type == 'OUTPUT_MATERIAL' and n.is_active_output), None)
        if out and out.inputs["Surface"].links:
            n = out.inputs["Surface"].links[0].from_node
            bsdf = n if n.type == 'BSDF_PRINCIPLED' else None
    if bsdf is None:
        c = mat.diffuse_color
        return [("Kd", _vals(c, 3))], []

    cat = mat.get("obj_mtlx_surface", "open_pbr_surface")
    table = SURFACES.get(cat, SURFACES["open_pbr_surface"])
    lines, nodes, inputs, conns, css = [], [], [], [], []
    names, memo = set(["shader"]), {}
    classic = []

    def fresh(base):
        base = "".join(c if (c.isascii() and (c.isalnum() or c == "_")) else "_" for c in base) or "n"
        if not (base[0].isalpha() or base[0] == "_"):
            base = "_" + base
        k, n = 1, base
        while n in names:
            k += 1
            n = f"{base}_{k}"
        names.add(n)
        return n

    def file_of(img):
        p = bpy.path.abspath(img.filepath) if img.filepath else img.name
        try:
            rel = os.path.relpath(p, mtl_dir)
            return p if rel.startswith("..") else rel.replace(os.sep, "/")
        except ValueError:
            return p

    def tok(v):
        if v.startswith("@"):
            v = "@" + v
        return f'"{v}"' if (" " in v or "\t" in v) else v

    def walk(sock, ty):
        """MaterialX node name for Blender output socket `sock` as type `ty`."""
        key = (sock.node.name, sock.identifier, ty)
        if key in memo:
            return memo[key]
        n = sock.node
        res = None
        if n.type == 'TEX_IMAGE' and n.image is not None and ty in (_C, "vector3"):
            res = image_node(n, ty)
        elif n.type == 'SEPARATE_COLOR' and sock.name == "Red" and ty == _F and n.inputs["Color"].links \
                and n.inputs["Color"].links[0].from_node.type == 'TEX_IMAGE':
            res = image_node(n.inputs["Color"].links[0].from_node, _F)
        elif n.type == 'NORMAL_MAP' and ty == "vector3":
            res = fresh(n.label or "normalmap")
            nodes.append(f"mtlx_node {res} normalmap vector3")
            if n.inputs["Color"].links:
                src = walk(n.inputs["Color"].links[0].from_socket, "vector3")
                if src:
                    conns.append(f"mtlx_input {res}.in vector3 @{src}")
            if abs(n.inputs["Strength"].default_value - 1.0) > 1e-6:
                inputs.append(f"mtlx_input {res}.scale float {_fmt(n.inputs['Strength'].default_value)}")
        elif n.type == 'RGB' and ty == _C:
            res = fresh(n.label or "constant")
            nodes.append(f"mtlx_node {res} constant color3")
            inputs.append(f"mtlx_input {res}.value color3 {_vals(n.outputs[0].default_value, 3)}")
        elif n.type == 'VALUE' and ty == _F:
            res = fresh(n.label or "constant")
            nodes.append(f"mtlx_node {res} constant float")
            inputs.append(f"mtlx_input {res}.value float {_fmt(n.outputs[0].default_value)}")
        elif n.type == 'MATH' and ty == _F and n.operation in ("MULTIPLY", "ADD", "SUBTRACT"):
            res = fresh(n.label or n.operation.lower())
            nodes.append(f"mtlx_node {res} {n.operation.lower()} float")
            for port, slot in (("in1", n.inputs[0]), ("in2", n.inputs[1])):
                operand(res, port, slot, _F)
        elif n.type == 'MIX' and n.data_type == 'RGBA' and ty == _C:
            if n.blend_type == 'MIX':
                res = fresh(n.label or "mix")
                nodes.append(f"mtlx_node {res} mix color3")
                operand(res, "bg", n.inputs[6], _C)
                operand(res, "fg", n.inputs[7], _C)
                operand(res, "mix", n.inputs["Factor"], _F)
            elif n.blend_type in ("MULTIPLY", "ADD", "SUBTRACT") and not n.inputs["Factor"].links \
                    and abs(n.inputs["Factor"].default_value - 1.0) < 1e-6:
                res = fresh(n.label or n.blend_type.lower())
                nodes.append(f"mtlx_node {res} {n.blend_type.lower()} color3")
                operand(res, "in1", n.inputs[6], _C)
                operand(res, "in2", n.inputs[7], _C)
        elif n.type == 'MIX' and n.data_type == 'FLOAT' and ty == _F and n.blend_type == 'MIX':
            res = fresh(n.label or "mix")
            nodes.append(f"mtlx_node {res} mix float")
            operand(res, "bg", n.inputs[2], _F)
            operand(res, "fg", n.inputs[3], _F)
            operand(res, "mix", n.inputs["Factor"], _F)
        elif n.type == 'UVMAP' and ty == "vector2":
            res = fresh(n.label or "texcoord")
            nodes.append(f"mtlx_node {res} texcoord vector2")
        if res is None:
            warn(f"{mat.name}: node '{n.name}' ({n.bl_idname}) cannot be written as MaterialX {ty}; "
                 "using the socket value")
        memo[key] = res
        return res

    def operand(res, port, slot, ty):
        if slot.links:
            src = walk(slot.links[0].from_socket, ty)
            if src:
                conns.append(f"mtlx_input {res}.{port} {ty} @{src}")
                return
        v = slot.default_value
        inputs.append(f"mtlx_input {res}.{port} {ty} " +
                      (_vals(v, 3) if ty == _C else _fmt(v if not hasattr(v, '__len__') else v[0])))

    def image_node(tex, ty):
        res = fresh(tex.label or "image")
        nodes.append(f"mtlx_node {res} image {ty}")
        inputs.append(f"mtlx_input {res}.file filename {tok(file_of(tex.image))}")
        if tex.extension == 'EXTEND':
            inputs.append(f"mtlx_input {res}.uaddressmode string clamp")
            inputs.append(f"mtlx_input {res}.vaddressmode string clamp")
        if tex.image.colorspace_settings.name == "sRGB":
            css.append(f"mtlx_colorspace {res}.file srgb_texture")
        if tex.inputs["Vector"].links:
            src = walk(tex.inputs["Vector"].links[0].from_socket, "vector2")
            if src:
                conns.append(f"mtlx_input {res}.texcoord vector2 @{src}")
        return res

    surf_in, surf_conn = [], []
    for (port, ty, sname, scale, default) in table:
        sock = bsdf.inputs[sname]
        if sock.links:
            src = walk(sock.links[0].from_socket, ty)
            if src:
                surf_conn.append(f"mtlx_input shader.{port} {ty} @{src}")
                continue
        if default is None:
            continue
        v = sock.default_value
        v = tuple(v)[:3] if ty == _C else v / scale
        if _differs(v, default):
            surf_in.append(f"mtlx_input shader.{port} {ty} " + (_vals(v, 3) if ty == _C else _fmt(v)))

    if "obj_mtlx_version" in mat:
        lines.append(f"mtlx_version {mat['obj_mtlx_version']}")
    lines.append(f"mtlx_surface shader {cat}")
    lines += nodes + surf_in + inputs + css + surf_conn + conns
    lines += [f"mtlx_include {tok(i)}" for i in str(mat.get("obj_mtlx_includes", "")).split("\n") if i]

    # classic fallback
    bc = bsdf.inputs["Base Color"]
    classic.append(("Kd", _vals(bc.default_value, 3) if not bc.links else "1 1 1"))
    for key, sname in (("Pr", "Roughness"), ("Pm", "Metallic"), ("d", "Alpha")):
        s = bsdf.inputs[sname]
        if not s.links:
            classic.append((key, _fmt(s.default_value)))
    ke, ks = bsdf.inputs["Emission Color"], bsdf.inputs["Emission Strength"]
    if not ke.links and ks.default_value > 0:
        classic.append(("Ke", _vals([c * ks.default_value for c in ke.default_value], 3)))
    if bc.links and bc.links[0].from_node.type == 'TEX_IMAGE' and bc.links[0].from_node.image:
        classic.append(("map_Kd", tok(file_of(bc.links[0].from_node.image))))
    return classic, lines
