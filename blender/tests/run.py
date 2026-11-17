"""Headless tests for the io_scene_obj_ext Blender add-on.

  blender -b --factory-startup --python-exit-code 1 \
      --python blender/tests/run.py -- WORKDIR

Builds the reference C checkers (tests/subd_dump, tests/mtlx_dump) with `cc`
and uses them to check what the add-on writes.
"""
import math
import os
import shutil
import subprocess
import sys

import bpy

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "blender"))
import io_scene_obj_ext as addon  # noqa: E402
from io_scene_obj_ext import subd, mtlx  # noqa: E402

WORK = sys.argv[sys.argv.index("--") + 1] if "--" in sys.argv else "/tmp/obj_ext_test"
os.makedirs(WORK, exist_ok=True)
FAILS = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        FAILS.append(msg)


def build_tools():
    tools = {}
    for name, srcs in (("subd_dump", ["tests/subd_dump.c", "tobj_subd.c"]),
                       ("mtlx_dump", ["tests/mtlx_dump.c", "tobj_mtlx.c"])):
        exe = os.path.join(WORK, name)
        subprocess.run(["cc", "-std=c11", "-O1", "-o", exe] + [os.path.join(ROOT, s) for s in srcs],
                       check=True)
        tools[name] = exe
    return tools


TOOLS = build_tools()


def c_subd(path):
    """{mesh number: (ok, model)} from the C checker; model = canonical lines parsed."""
    out = subprocess.run([TOOLS["subd_dump"], path], capture_output=True, text=True, check=True).stdout
    res, cur = [], None
    for line in out.splitlines():
        if line.startswith("mesh "):
            cur = [line.endswith("ok=1"), []]
            res.append(cur)
        else:
            cur[1].append(line)
    return [(ok, model(lines)) for ok, lines in res]


def model(lines):
    """Comparable form of canonical tag lines (sharpness as numbers; 0 = absent)."""
    m = {"crease": {}, "corner": {}, "hole": set(), "scalars": {}, "unknown": []}
    for l in lines:
        t = l.split()
        if t[1] == "crease":
            if subd.sharpness(t[5]) > 0:
                m["crease"][(int(t[3]), int(t[4]))] = round(min(subd.sharpness(t[5]), 10), 4)
        elif t[1] == "corner":
            if subd.sharpness(t[4]) > 0:
                m["corner"][int(t[3])] = round(min(subd.sharpness(t[4]), 10), 4)
        elif t[1] == "hole":
            m["hole"] |= set(map(int, t[3:]))
        elif t[1] in ("scheme", "interpolateboundary", "facevaryinginterpolateboundary",
                      "creasemethod", "smoothtriangles"):
            m["scalars"][t[1]] = t[3]
        else:
            m["unknown"].append(l)
    return m


def c_mtlx(path):
    out = subprocess.run([TOOLS["mtlx_dump"], path], capture_output=True, text=True, check=True).stdout
    return {l.split(" ext=")[0][4:]: l.endswith("ok=1") for l in out.splitlines() if l.startswith("mat ")}


def reset():
    bpy.ops.wm.read_factory_settings(use_empty=True)


def fixture(name):
    return os.path.join(ROOT, "formal", "Subd", "tests", name)


def evaluated(ob):
    dg = bpy.context.evaluated_depsgraph_get()
    me = ob.evaluated_get(dg).to_mesh()
    return sorted(tuple(round(c, 4) for c in v.co) for v in me.vertices)


def roundtrip(src, label):
    """import src, export, compare the tags of src and of the export with the C checker,
    re-import and compare Blender's evaluated (subdivided) surfaces."""
    reset()
    obs, _ = addon.import_obj(bpy.context, src)
    before = {ob.name: evaluated(ob) for ob in obs}
    out = os.path.join(WORK, label + ".obj")
    addon.export_obj(bpy.context, out, obs)
    a = [x for x in c_subd(src) if x[0]]
    b = c_subd(out)
    check(all(ok for ok, _ in b), f"{label}: every exported mesh is accepted by the C checker")
    check([m for _, m in a] == [m for _, m in b],
          f"{label}: exported tags equal the source tags (C models)")
    reset()
    obs2, _ = addon.import_obj(bpy.context, out)
    after = {ob.name: evaluated(ob) for ob in obs2}
    same = sorted(before.values()) == sorted(after.values())
    check(same, f"{label}: re-imported subdivided surfaces are identical")
    return obs2


# ---------------------------------------------------------------- tests

def test_subd_import():
    reset()
    obs, warns = addon.import_obj(bpy.context, fixture("box.obj"))
    ob = obs[0]
    mod = ob.modifiers.get("Subdivision")
    check(mod is not None and mod.type == 'SUBSURF', "box: Subdivision Surface modifier")
    check(mod.boundary_smooth == 'ALL', "box: interpolateboundary 2 -> boundary_smooth ALL")
    check(mod.uv_smooth == 'PRESERVE_CORNERS', "box: facevarying 1 -> uv_smooth PRESERVE_CORNERS")
    check(ob.get("obj_subd_creasemethod") == "chaikin", "box: creasemethod kept as property")
    check(ob.get("obj_subd_smoothtriangles") == "smooth", "box: smoothtriangles kept as property")
    check(ob.get("obj_subd_unknown") == "t mytag 1/1/1 7 1e3 hello", "box: unknown tag kept verbatim")
    me = ob.data
    ce = me.attributes["crease_edge"]
    val = {tuple(sorted(e.vertices)): ce.data[e.index].value for e in me.edges}
    check(abs(val[(0, 1)] - math.sqrt(0.3)) < 1e-6, "box: crease 0-1 sharpness 3 -> sqrt(0.3)")
    check(abs(val[(1, 2)] - 1.0) < 1e-6, "box: crease 1-2 sharpness 10 -> 1")
    check(val[(2, 3)] == 0.0, "box: crease 2-3 negative sharpness -> 0")
    cv = me.attributes["crease_vert"]
    check(abs(cv.data[0].value - math.sqrt(0.05)) < 1e-6 and abs(cv.data[6].value - math.sqrt(0.4)) < 1e-6,
          "box: corners")
    holes = me.attributes[addon.subd_blender.HOLE_ATTR]
    check([p.index for p in me.polygons if holes.data[p.index].value] == [1, 5], "box: holes 5 1")
    check(any("Chaikin" in w for w in warns) and any("hole" in w for w in warns),
          "box: unsupported features reported")


def test_crease_mapping():
    """sharpness 10*c^2 (Blender) vs a sharpness-3 crease written by the add-on."""
    reset()
    bpy.ops.mesh.primitive_cube_add()
    ob = bpy.context.object
    ce = ob.data.attributes.new("crease_edge", 'FLOAT', 'EDGE')
    ce.data[0].value = 0.5
    cv = ob.data.attributes.new("crease_vert", 'FLOAT', 'POINT')
    cv.data[3].value = 1.0
    mod = ob.modifiers.new("s", 'SUBSURF')
    mod.boundary_smooth = 'PRESERVE_CORNERS'
    out = os.path.join(WORK, "authored.obj")
    addon.export_obj(bpy.context, out, [ob])
    (ok, m), = c_subd(out)
    check(ok, "authored: exported tags accepted by the C checker")
    check(list(m["crease"].values()) == [2.5], "authored: crease 0.5 -> sharpness 2.5")
    check(list(m["corner"].items()) == [(3, 10.0)], "authored: vertex crease 1 -> sharpness 10")
    check(m["scalars"] == {"scheme": "catmark", "interpolateboundary": "1",
                           "facevaryinginterpolateboundary": "4"},
          "authored: scheme, boundary and UV smoothing written explicitly")


def test_subd_roundtrips():
    roundtrip(fixture("box.obj"), "box")
    obs = roundtrip(fixture("multi.obj"), "multi")
    loop = [ob for ob in obs if ob.get("obj_subd_scheme") == "loop"]
    check(len(loop) == 1, "multi: loop scheme kept as property")
    roundtrip(os.path.join(ROOT, "models", "catmark_torus_creases0.obj"), "torus")


def test_bad_tags():
    reset()
    obs, warns = addon.import_obj(bpy.context, fixture("bad.obj"))
    check(len(obs) == 14 and not any(ob.modifiers for ob in obs), "bad: no subdivision set up")
    check(sum("subdivision tags ignored" in w for w in warns) == 14, "bad: every mesh reported")


def test_python_port_matches_c():
    gen = os.path.join(ROOT, "formal", "Subd", "tools", "gen.py")
    bad = 0
    for i in range(200):
        p = os.path.join(WORK, "gen.obj")
        with open(p, "w") as f:
            f.write(subprocess.run([sys.executable, "-I", gen, str(i)], capture_output=True,
                                   text=True).stdout)
        c = subprocess.run([TOOLS["subd_dump"], p], capture_output=True, text=True).stdout
        bad += subd.dump_obj(open(p).read()) != c
    check(bad == 0, f"subd.py agrees with tobj_subd.c on 200 random files ({bad} differ)")


def _quad_obj(path, mtl, names):
    with open(path, "w") as f:
        f.write(f"mtllib {mtl}\n")
        for i, n in enumerate(names):
            x = 2 * i
            f.write(f"v {x} 0 0\nv {x + 1} 0 0\nv {x + 1} 1 0\nv {x} 1 0\n")
        f.write("vt 0 0\nvt 1 0\nvt 1 1\nvt 0 1\n")
        for i, n in enumerate(names):
            b = 4 * i
            f.write(f"o q{i}\nusemtl {n}\nf {b + 1}/1 {b + 2}/2 {b + 3}/3 {b + 4}/4\n")


def graph(mat):
    """Comparable form of a node tree: node kinds with labels, links, BSDF values."""
    nt = mat.node_tree
    kinds = sorted((n.bl_idname, n.label) for n in nt.nodes)
    links = sorted((l.from_node.bl_idname, l.from_node.label, l.from_socket.identifier,
                    l.to_node.bl_idname, l.to_node.label, l.to_socket.identifier) for l in nt.links)
    bsdf = next(n for n in nt.nodes if n.type == 'BSDF_PRINCIPLED')
    vals = {}
    for s in bsdf.inputs:
        if hasattr(s, "default_value") and not s.links:
            v = s.default_value
            vals[s.name] = tuple(round(x, 4) for x in v) if hasattr(v, "__len__") else round(v, 4)
    return kinds, links, vals


def test_materialx():
    src_dir = os.path.join(WORK, "mx_src")
    os.makedirs(src_dir, exist_ok=True)
    shutil.copy(os.path.join(HERE, "nodes.mtl"), src_dir)
    names = ["graph", "std", "preview", "classic_only"]
    obj = os.path.join(src_dir, "nodes.obj")
    _quad_obj(obj, "nodes.mtl", names)
    reset()
    obs, warns = addon.import_obj(bpy.context, obj)
    mats = {m.name: m for m in bpy.data.materials}
    g = mats["graph"].node_tree
    types = sorted(n.bl_idname for n in g.nodes)
    check(types.count("ShaderNodeTexImage") == 3 and "ShaderNodeNormalMap" in types and
          "ShaderNodeUVMap" in types and "ShaderNodeRGB" in types and "ShaderNodeMath" in types,
          "graph: MaterialX nodes became Blender nodes")
    albedo = next(n for n in g.nodes if n.label == "albedo")
    check(albedo.image.colorspace_settings.name == "sRGB", "graph: srgb_texture colorspace")
    check(albedo.image.filepath.endswith("tex/albedo map.png"), "graph: quoted file name with blank")
    bsdf = next(n for n in g.nodes if n.type == 'BSDF_PRINCIPLED')
    check(abs(bsdf.inputs["Metallic"].default_value - 0.25) < 1e-6, "graph: constant input")
    check(bsdf.inputs["Normal"].links[0].from_node.type == 'NORMAL_MAP', "graph: normal map connected")
    check(abs(next(n for n in mats["std"].node_tree.nodes if n.type == 'BSDF_PRINCIPLED')
              .inputs["Roughness"].default_value - 0.6) < 1e-6, "std: standard_surface input")
    check(mats["std"]["obj_mtlx_surface"] == "standard_surface", "std: category kept")
    check(abs(next(n for n in mats["classic_only"].node_tree.nodes if n.type == 'BSDF_PRINCIPLED')
              .inputs["Roughness"].default_value - 0.4) < 1e-6, "classic_only: Pr read")
    before = {n: graph(mats[n]) for n in names}

    out = os.path.join(WORK, "mx_out", "nodes.obj")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    addon.export_obj(bpy.context, out, obs)
    mtl = os.path.join(os.path.dirname(out), "nodes.mtl")
    v = c_mtlx(mtl)
    check(v.get("graph") and v.get("std") and v.get("preview"),
          "export: MaterialX materials accepted by the C checker")
    check(v.get("classic_only") is True, "export: Blender-only material written as MaterialX too")
    text = open(mtl).read()
    # textures outside the export folder are written with absolute paths
    check(f'"{os.path.join(src_dir, "tex", "albedo map.png")}"' in text,
          "export: texture outside the export folder written with an absolute path")
    reset()
    addon.import_obj(bpy.context, out)
    mats = {m.name: m for m in bpy.data.materials}
    for n in names:
        check(graph(mats[n]) == before[n], f"{n}: node tree survives export + re-import")


def test_operators():
    """The registered File > Import/Export operators."""
    reset()
    addon.register()
    try:
        r = bpy.ops.import_scene.obj_ext(filepath=fixture("box.obj"))
        check(r == {'FINISHED'} and bpy.data.objects.get("box") is not None, "operator: import")
        out = os.path.join(WORK, "op.obj")
        r = bpy.ops.export_scene.obj_ext(filepath=out)
        (ok, m), = c_subd(out)
        check(r == {'FINISHED'} and ok and m["hole"] == {1, 5}, "operator: export")
    finally:
        addon.unregister()


def main():
    for t in (test_operators, test_subd_import, test_crease_mapping, test_subd_roundtrips, test_bad_tags,
              test_python_port_matches_c, test_materialx):
        print(f"== {t.__name__}")
        try:
            t()
        except Exception as e:  # report and continue
            import traceback
            traceback.print_exc()
            FAILS.append(f"{t.__name__}: {e!r}")
    print(f"\n{'PASS' if not FAILS else 'FAIL'}: {len(FAILS)} failure(s)")
    for f in FAILS:
        print("  -", f)
    if FAILS:
        sys.exit(1)


main()
