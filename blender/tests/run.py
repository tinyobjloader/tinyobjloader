"""Headless tests for the io_scene_obj_ext Blender add-on.

  blender -b --factory-startup --python-exit-code 1 \
      --python blender/tests/run.py -- WORKDIR

Builds the reference C checkers (tests/subd_dump, tests/mtlx_dump) with `cc`
and uses them to check what the add-on writes.

OpenSubdiv cross-check: with OSD_ROOT set to an OpenSubdiv install prefix
(CPU backend is enough: include/ and lib/libosdCPU), blender/tests/osd_refine.cc
is built and Blender's subdivided surfaces are compared with OpenSubdiv's
(refined points and limit points). Without OSD_ROOT the check is skipped.
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
from io_scene_obj_ext import subd, mtlx, skel  # noqa: E402
from mathutils import Matrix, Vector  # noqa: E402

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
                       ("mtlx_dump", ["tests/mtlx_dump.c", "tobj_mtlx.c"]),
                       ("skel_dump", ["tests/skel_dump.c", "tobj_skel.c"])):
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


def build_osd_refine():
    root = os.environ.get("OSD_ROOT")
    if not root:
        return None
    obj = os.path.join(WORK, "tobj_subd.o")
    exe = os.path.join(WORK, "osd_refine")
    subprocess.run(["cc", "-std=c11", "-O1", "-c", os.path.join(ROOT, "tobj_subd.c"), "-o", obj],
                   check=True)
    subprocess.run(["c++", "-std=c++17", "-O1", f"-I{root}/include",
                    os.path.join(HERE, "osd_refine.cc"), obj, f"-L{root}/lib", "-losdCPU",
                    f"-Wl,-rpath,{root}/lib", "-o", exe], check=True)
    return exe


def osd_points(exe, path, level, limit):
    out = subprocess.run([exe, path, str(level)] + (["--limit"] if limit else []),
                         capture_output=True, text=True, check=True).stdout
    shapes, cur = {}, None
    for line in out.splitlines():
        t = line.split()
        if t[0] == "shape":
            cur = shapes.setdefault(t[1] if len(t) == 3 else "", [])
        else:
            cur.append(tuple(map(float, t)))
    return shapes


def test_opensubdiv():
    """Blender's evaluated Subdivision Surface vs OpenSubdiv (Far, CPU), same tags."""
    exe = build_osd_refine()
    if exe is None:
        print("skip OpenSubdiv cross-check (set OSD_ROOT to an OpenSubdiv install)")
        return
    from mathutils import kdtree
    files = [os.path.join(HERE, "osd_cross.obj"),
             os.path.join(ROOT, "models", "catmark_torus_creases0.obj")]
    # Limit points near an infinitely sharp crease that ends at a boundary: Blender's
    # adaptive patch evaluation is approximate there even at quality 10 (measured
    # 3.4e-3 at level 1, 1.1e-3 at levels 2 and 3), while OpenSubdiv's limit masks
    # are exact. All other limit points, and all refined points, match to 1e-5.
    limit_tol = {"grid_edge_corner": 5e-3, "grid_edge_only": 5e-3}
    for path in files:
        for limit in (False, True):
            for level in (1, 2, 3):
                ref = osd_points(exe, path, level, limit)
                reset()
                obs, _ = addon.import_obj(bpy.context, path, convert_axes=False)
                worst, counts, within = 0.0, True, True
                for ob in obs:
                    mod = ob.modifiers["Subdivision"]
                    mod.levels = level
                    mod.use_limit_surface = limit
                    # Blender evaluates the limit surface with adaptive patches; its
                    # default quality (3) is approximate near semi-sharp creases
                    # (up to 1.3e-2 on the torus), the maximum (10) is exact here.
                    mod.quality = 10
                    me = ob.evaluated_get(bpy.context.evaluated_depsgraph_get()).to_mesh()
                    pts = ref[ob.data.name if ob.data.name in ref else ""]
                    counts &= len(pts) == len(me.vertices)
                    kd = kdtree.KDTree(len(pts))
                    for i, p in enumerate(pts):
                        kd.insert(p, i)
                    kd.balance()
                    d = max(kd.find(v.co)[2] for v in me.vertices)
                    within &= d < (limit_tol.get(ob.name, 1e-4) if limit else 1e-4)
                    worst = max(worst, d)
                check(counts and within,
                      f"OpenSubdiv: {os.path.basename(path)} level {level} "
                      f"{'limit' if limit else 'refined'} (max distance {worst:.1e})")


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


# ---------------------------------------------------------------- skeletons

def c_skel(path):
    return subprocess.run([TOOLS["skel_dump"], path], capture_output=True, text=True,
                          check=True).stdout


def test_skel_python_port_matches_c():
    """skel.dump_obj == tests/skel_dump (C) on the fixtures and random files."""
    fixtures = os.path.join(ROOT, "formal", "Skel", "tests")
    files = [os.path.join(fixtures, f) for f in sorted(os.listdir(fixtures))]
    gen = os.path.join(ROOT, "formal", "Skel", "tools", "gen.py")
    for seed in range(300):
        p = os.path.join(WORK, f"skel_gen_{seed % 10}.obj")
        with open(p, "w") as f:
            f.write(subprocess.run([sys.executable, gen, str(seed)], capture_output=True,
                                   text=True, check=True).stdout)
        files.append(p)
        bad = [p for p in files if skel.dump_obj(open(p).read()) != c_skel(p)]
        if bad:
            break
        files = files[:4]
    check(not bad, "skel: Python port == C on 4 fixtures + 300 random files" +
          (f" (first mismatch {bad[0]})" if bad else ""))


def make_rig():
    """Column mesh skinned to root -> spine -> head; action bending spine/head."""
    reset()
    scene = bpy.context.scene
    scene.render.fps, scene.frame_start, scene.frame_end = 24, 1, 24
    ring = [(-0.2, -0.2), (0.2, -0.2), (0.2, 0.2), (-0.2, 0.2)]
    verts = [(x, y, 3.0 * k / 12) for k in range(13) for (x, y) in ring]
    faces = [(4 * k + i, 4 * k + (i + 1) % 4, 4 * k + (i + 1) % 4 + 4, 4 * k + i + 4)
             for k in range(12) for i in range(4)] + [(3, 2, 1, 0), (48, 49, 50, 51)]
    me = bpy.data.meshes.new("body")
    me.from_pydata(verts, [], faces)
    body = bpy.data.objects.new("body", me)
    scene.collection.objects.link(body)
    arm_data = bpy.data.armatures.new("rig")
    arm = bpy.data.objects.new("rig", arm_data)
    scene.collection.objects.link(arm)
    bpy.context.view_layer.objects.active = arm
    bpy.ops.object.mode_set(mode='EDIT')
    prev = None
    for i, n in enumerate(("root", "spine", "head")):
        eb = arm_data.edit_bones.new(n)
        eb.head, eb.tail, eb.parent = (0, 0, i), (0, 0, i + 1), prev
        eb.use_connect = prev is not None
        prev = eb
    bpy.ops.object.mode_set(mode='OBJECT')
    for n, lo in (("root", 0), ("spine", 1), ("head", 2)):
        g = body.vertex_groups.new(name=n)
        for v in me.vertices:
            w = max(0.0, 1.0 - abs(v.co.z - (lo + 0.5)))
            if w > 0:
                g.add([v.index], w, 'REPLACE')
    body.modifiers.new("Armature", 'ARMATURE').object = arm
    arm.animation_data_create().action = bpy.data.actions.new("bend")
    for frame, deg in ((1, 0), (12, 40), (24, 0)):
        for n in ("spine", "head"):
            pb = arm.pose.bones[n]
            pb.rotation_mode = 'XYZ'
            pb.rotation_euler = (math.radians(deg), 0, 0)
            pb.keyframe_insert("rotation_euler", frame=frame)
    return body, arm


def deformed(name, frame):
    """Evaluated world points of an object, in OBJ (Y-up) axes."""
    bpy.context.scene.frame_set(frame)
    ob = bpy.data.objects[name]
    ev = ob.evaluated_get(bpy.context.evaluated_depsgraph_get())
    return [(p.x, p.z, -p.y) for p in (ev.matrix_world @ v.co for v in ev.data.vertices)]


def max_dist(a, b):
    if len(a) != len(b):
        return float("inf")
    return max((Vector(p) - Vector(q)).length for p, q in zip(a, b))


SKEL_FRAMES = (1, 6, 12, 18, 24)


def test_skel_roundtrip(fmt="fbx"):
    """Rig -> OBJ (inline skeleton + animation sidecar) -> re-import: same deformation."""
    make_rig()
    want = {f: deformed("body", f) for f in SKEL_FRAMES}
    out = os.path.join(WORK, f"skel_rig_{fmt}.obj")
    side = f"skel_rig_{fmt}_skel." + ("usda" if fmt == "usd" else "fbx")
    w = addon.export_obj(bpy.context, out, list(bpy.context.scene.objects), sidecar_format=fmt)
    check(not w, f"skel export ({fmt}): no warnings {w}")
    dump = c_skel(out)
    check(dump.startswith("skel ok=1 joints=3\n"), "skel export: C checker accepts the skeleton")
    check(f"skel_anim {side}" in dump and os.path.exists(os.path.join(WORK, side)),
          f"skel export: animation sidecar {side}")
    text = open(out).read()
    check(skel.dump_obj(text) == dump, "skel export: lines are canonical (Python == C)")
    reset()
    obs, w = addon.import_obj(bpy.context, out)
    check(not w, f"skel import: no warnings {w}")
    arm = next((o for o in bpy.data.objects if o.type == 'ARMATURE'), None)
    check(arm is not None and [b.name for b in arm.data.bones] == ["root", "spine", "head"],
          "skel import: armature root/spine/head")
    for f in SKEL_FRAMES:
        d = max_dist(deformed("body", f), want[f])
        check(d < 1e-4, f"skel round trip ({fmt}) frame {f}: max distance {d:.2e}")


def test_skel_roundtrip_usd():
    test_skel_roundtrip("usd")


def test_skel_lib_only(fmt="fbx"):
    """Joint names only; bind, rest and animation from the sidecar (skel_lib)."""
    make_rig()
    want = {f: deformed("body", f) for f in SKEL_FRAMES}
    out = os.path.join(WORK, f"skel_lib_{fmt}.obj")
    side = f"skel_lib_{fmt}_skel." + ("usda" if fmt == "usd" else "fbx")
    addon.export_obj(bpy.context, out, list(bpy.context.scene.objects), sidecar_format=fmt)
    lines = []
    for line in open(out).read().splitlines():
        t = line.split()
        if t and t[0] == "skel_joint":
            lines.append(" ".join(t[:3]))
        elif t and t[0] in ("skel_rest", "skel_anim"):
            continue
        else:
            lines.append(line)
        if t and t[0] == "skel_joint" and t[1] == "head":
            lines += [f"skel_lib {side}", f"skel_anim {side}"]
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    check(c_skel(out).startswith("skel ok=1 joints=3"), "skel_lib: C checker accepts names only")
    reset()
    obs, w = addon.import_obj(bpy.context, out)
    check(not w, f"skel_lib ({fmt}) import: no warnings {w}")
    for f in SKEL_FRAMES:
        d = max_dist(deformed("body", f), want[f])
        check(d < 1e-4, f"skel_lib ({fmt}) frame {f}: max distance {d:.2e}")


def test_skel_lib_only_usd():
    test_skel_lib_only("usd")


def lbs(text):
    """Reference linear blend skinning of an OBJ with inline bind + rest (OBJ space)."""
    d = {"v": [], "vw": {}}
    sk = skel.parse_lines(text.splitlines())
    for line in text.splitlines():
        t = line.split()
        if t and t[0] == "v":
            d["v"].append(Vector(map(float, t[1:4])))
        elif t and t[0] == "vw":
            d["vw"][int(t[1])] = [(int(t[k]), float(t[k + 1])) for k in range(2, len(t), 2)]
    from io_scene_obj_ext.skel_blender import from_text
    world, binds = [], [from_text(j.bind) for j in sk.joints]
    for i, j in enumerate(sk.joints):
        if j.rest:
            local = from_text(j.rest)
        else:  # bind-relative
            local = binds[j.parent].inverted() @ binds[i] if j.parent >= 0 else binds[i]
        world.append(world[j.parent] @ local if j.parent >= 0 else local)
    skin = [world[i] @ from_text(j.bind).inverted() for i, j in enumerate(sk.joints)]
    out = []
    for i, p in enumerate(d["v"]):
        ws = d["vw"].get(i, [])
        tot = sum(w for _, w in ws) or 1.0
        out.append(tuple(sum(((skin[j] @ p) * (w / tot) for j, w in ws), Vector()) if ws else p))
    return out


def test_skel_inline_rest():
    """skel_rest differing from the bind pose: Blender's pose == reference LBS."""
    make_rig()
    out = os.path.join(WORK, "skel_rest.obj")
    addon.export_obj(bpy.context, out, list(bpy.context.scene.objects), skel_sidecar=False)
    rot = Matrix.Rotation(math.radians(30), 4, 'Z')  # bend head about the OBJ Z axis
    lines = []
    for line in open(out).read().splitlines():
        t = line.split()
        if t and t[0] == "skel_rest" and t[1] == "head":
            from io_scene_obj_ext.skel_blender import from_text, to_text
            line = " ".join(["skel_rest", "head"] + to_text(from_text(t[2:]) @ rot))
        lines.append(line)
    text = "\n".join(lines) + "\n"
    with open(out, "w") as f:
        f.write(text)
    want = lbs(text)
    reset()
    addon.import_obj(bpy.context, out)
    d = max_dist(deformed("body", 1), want)
    check(d < 1e-4, f"skel_rest pose vs reference LBS: max distance {d:.2e}")
    check(max_dist(want, lbs(text.replace("skel_rest head", "skel_rest_x head"))) > 0.1,
          "skel_rest: the test pose differs from the bind pose")


def test_skel_bad():
    """An ill-formed skeleton keeps the weights as vertex groups, without an armature."""
    reset()
    p = os.path.join(WORK, "skel_bad.obj")
    with open(p, "w") as f:
        f.write("skel_joint a -\nv 0 0 0\nv 1 0 0\nv 0 1 0\nvw 0 0 1\nf 1 2 3\n")
    obs, w = addon.import_obj(bpy.context, p)
    check(any("skeleton ignored" in x for x in w) and
          not any(o.type == 'ARMATURE' for o in bpy.data.objects), "skel bad: warning, no armature")


def test_skel_lightusd(fmt="fbx"):
    """LightUSD (skin_compare --dump on the exported OBJ) == Blender, per frame.
    Needs LIGHTUSD_SKIN_COMPARE (LightUSD tests/obj-skel/skin_compare); skipped otherwise."""
    exe = os.environ.get("LIGHTUSD_SKIN_COMPARE")
    if not exe:
        print("skip: LIGHTUSD_SKIN_COMPARE not set")
        return
    make_rig()
    want = {f: deformed("body", f) for f in SKEL_FRAMES}
    stem = f"skel_lightusd_{fmt}"
    out = os.path.join(WORK, stem + ".obj")
    addon.export_obj(bpy.context, out, list(bpy.context.scene.objects), sidecar_format=fmt)
    wrap = os.path.join(WORK, stem + "_scene.usda")
    with open(wrap, "w") as f:
        f.write('#usda 1.0\n(\n    defaultPrim = "W"\n    upAxis = "Y"\n    metersPerUnit = 1\n'
                '    timeCodesPerSecond = 24\n)\n\ndef SkelRoot "W" (\n    references = @' + stem + '.obj@\n)\n{\n}\n')
    for fr in SKEL_FRAMES:
        r = subprocess.run([exe, "--dump", wrap, str(fr)], capture_output=True, text=True)
        rows = [l.split() for l in r.stdout.splitlines() if l.startswith("/")]
        if r.returncode or len(rows) != 1:
            check(False, f"LightUSD dump frame {fr}: {r.stderr[-300:]}")
            continue
        v = list(map(float, rows[0][2:]))
        got = [Vector(v[i:i + 3]) for i in range(0, len(v), 3)]
        # LightUSD may split points per face: every point must lie on a Blender
        # point, and every Blender point must be covered
        ref = [Vector(p) for p in want[fr]]
        d1 = max(min((g - q).length for q in ref) for g in got)
        d2 = max(min((g - q).length for g in got) for q in ref)
        check(max(d1, d2) < 1e-4,
              f"LightUSD vs Blender ({fmt} sidecar) frame {fr}: max distance {max(d1, d2):.2e}")


def test_skel_lightusd_usd():
    test_skel_lightusd("usd")


def main():
    for t in (test_operators, test_subd_import, test_crease_mapping, test_subd_roundtrips, test_bad_tags,
              test_python_port_matches_c, test_materialx, test_opensubdiv,
              test_skel_python_port_matches_c, test_skel_roundtrip, test_skel_lib_only,
              test_skel_inline_rest, test_skel_bad, test_skel_lightusd,
              test_skel_roundtrip_usd, test_skel_lib_only_usd, test_skel_lightusd_usd):
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
