"""Blender <-> skel-obj.md: armature, vertex groups, optional FBX sidecar.

Import: joints with inline bind matrices become an armature (edit bones at the
bind transforms; `skel_rest` becomes the pose). Without inline binds, the
`skel_lib` sidecar (.fbx with Blender's FBX importer, or .usd/.usda/.usdc/.usdz
with its USD importer) is imported and its armature is used (joints matched by
name). `skel_anim`: the sidecar's action drives the armature. `vw` weights
become vertex groups plus an Armature modifier.

Export: an Armature modifier's armature gives `skel_joint` lines (inline bind =
the bone's rest transform in OBJ world space) and `skel_rest`; vertex groups
named after bones give `vw`. With an action and a sidecar format, the armature
and its action are written next to the OBJ (`<name>_skel.fbx` or
`<name>_skel.usda`, `skel_anim`).

Matrices: OBJ text is row-major with the translation in the last row (USD).
Blender's are column-vector; `conv` is the Blender -> OBJ change of world
axes (identity when axes are not converted), so W_obj = conv @ W_blender.
"""
import os
import re

from mathutils import Matrix

from . import skel


def axes(convert):
    if not convert:
        return Matrix.Identity(4)
    return Matrix(((1, 0, 0, 0), (0, 0, 1, 0), (0, -1, 0, 0), (0, 0, 0, 1)))


def from_text(m16):
    """16 row-major texts (translation last row) -> Blender Matrix."""
    v = [float(x) for x in m16]
    return Matrix([v[4 * r:4 * r + 4] for r in range(4)]).transposed()


def to_text(m):
    from .obj_io import fmt
    t = m.transposed()
    return [fmt(t[r][c]) for r in range(4) for c in range(4)]


# ---------------------------------------------------------------- import

USD_EXTS = (".usd", ".usda", ".usdc", ".usdz")


def is_sidecar(path):
    return path.lower().endswith(".fbx") or path.lower().endswith(USD_EXTS)


def _fbx_armature(bpy, context, path, warn, prim=None):
    """Import a sidecar (.fbx or USD); keep its armature object (meshes etc. are
    removed). `prim`: a USD Skeleton prim path, matched by its last component."""
    before = set(bpy.data.objects)
    if path.lower().endswith(USD_EXTS):
        try:
            # a sidecar is in the OBJ's units (OBJ has none): no unit conversion
            bpy.ops.wm.usd_import(filepath=path, import_skeletons=True, import_blendshapes=False,
                                  set_frame_range=False, apply_unit_conversion_scale=False)
        except Exception as e:  # noqa: BLE001
            warn(f"skeleton sidecar {os.path.basename(path)}: {e}")
            return None
        new = [o for o in bpy.data.objects if o not in before]
        arms = [o for o in new if o.type == 'ARMATURE']
        want = prim.rstrip("/").rsplit("/", 1)[-1] if prim else None
        arm = next((o for o in arms if want and o.name.split(".")[0] in (want, o.data.name)), None)
        arm = arm or (arms[0] if arms else None)
        keep = {arm}
        p = arm.parent if arm else None
        while p is not None:  # keep the transforms above the armature
            keep.add(p)
            p = p.parent
        for o in new:
            if o not in keep:
                bpy.data.objects.remove(o)
        if arm is None:
            warn(f"skeleton sidecar {os.path.basename(path)}: no armature")
        return arm
    try:
        # anim_offset=0: frame = FBX time * fps (the importer adds 1 by default), the
        # mapping of the exporter and of USD time codes; keep every bone (no leaf
        # bones are written by the exporter)
        bpy.ops.import_scene.fbx(filepath=path, use_anim=True, anim_offset=0.0,
                                 ignore_leaf_bones=False)
    except Exception as e:  # noqa: BLE001 (operator errors are RuntimeError)
        warn(f"skeleton sidecar {os.path.basename(path)}: {e}")
        return None
    new = [o for o in bpy.data.objects if o not in before]
    arm = next((o for o in new if o.type == 'ARMATURE'), None)
    for o in new:
        if o is not arm:
            bpy.data.objects.remove(o)
    if arm is None:
        warn(f"skeleton sidecar {os.path.basename(path)}: no armature")
    return arm


def _pick_action(bpy, arm, name):
    if arm is None or arm.animation_data is None:
        return None
    if name:
        for a in bpy.data.actions:
            if a.name == name or a.name.endswith("|" + name):
                return a
    return arm.animation_data.action


def _retarget(bpy, context, src, arm, names, act):
    """Key `arm`'s pose so each joint follows the same-named bone of `src` in
    world space (each joint keeps its own rest orientation: the offset between
    the two rest transforms is constant). Joints missing in `src` follow their
    parent at their rest offset."""
    scene = context.scene
    f0, f1 = (int(round(x)) for x in act.frame_range)
    frame = scene.frame_current
    out = bpy.data.actions.new(act.name)
    _assign(arm, out)
    bones = arm.data.bones
    a_inv = arm.matrix_world.inverted()
    offset = {}
    for n in names:
        if n in src.data.bones:
            offset[n] = (src.matrix_world @ src.data.bones[n].matrix_local).inverted() @ \
                (arm.matrix_world @ bones[n].matrix_local)
    for f in range(f0, f1 + 1):
        scene.frame_set(f)
        pose = {}
        for n in names:  # parents first (skel-obj.md joint order)
            b = bones[n]
            if n in offset:
                pose[n] = a_inv @ src.matrix_world @ src.pose.bones[n].matrix @ offset[n]
            elif b.parent:
                pose[n] = pose[b.parent.name] @ b.parent.matrix_local.inverted() @ b.matrix_local
            else:
                pose[n] = b.matrix_local.copy()
            if b.parent:
                rel = b.parent.matrix_local.inverted() @ b.matrix_local
                basis = rel.inverted() @ pose[b.parent.name].inverted() @ pose[n]
            else:
                basis = b.matrix_local.inverted() @ pose[n]
            pb = arm.pose.bones[n]
            pb.rotation_mode = 'QUATERNION'
            pb.matrix_basis = basis
            for path in ("location", "rotation_quaternion", "scale"):
                pb.keyframe_insert(path, frame=f)
    scene.frame_set(frame)


def _assign(ob, act):
    """Action onto another object (Blender 4.4+ slotted actions need a slot)."""
    ad = ob.animation_data_create()
    ad.action = act
    if hasattr(ad, "action_slot") and ad.action_slot is None and len(act.slots):
        ad.action_slot = act.slots[0]


def _build_armature(bpy, context, sk, conv):
    """Armature whose rest pose is the inline bind; pose = skel_rest (if any)."""
    inv = conv.inverted()
    binds = [inv @ from_text(j.bind) for j in sk.joints]
    arm_data = bpy.data.armatures.new("Skeleton")
    arm = bpy.data.objects.new("Skeleton", arm_data)
    context.collection.objects.link(arm)
    context.view_layer.objects.active = arm
    bpy.ops.object.mode_set(mode='EDIT')
    bones = []
    for i, j in enumerate(sk.joints):
        eb = arm_data.edit_bones.new(j.name)
        loc, rot, _ = binds[i].decompose()
        kids = [binds[k].translation for k, c in enumerate(sk.joints) if c.parent == i]
        length = max([(c - loc).length for c in kids] + [0.0])
        eb.head, eb.tail = (0, 0, 0), (0, max(length, 0.05), 0)
        eb.matrix = Matrix.Translation(loc) @ rot.to_matrix().to_4x4()
        if j.parent >= 0:
            eb.parent = bones[j.parent]
        bones.append(eb)
    bpy.ops.object.mode_set(mode='OBJECT')
    if any(j.rest for j in sk.joints):
        # posed world (Blender space) from the rest locals; joints without one
        # keep their bind-relative local transform
        world = []
        for i, j in enumerate(sk.joints):
            pw = world[j.parent] if j.parent >= 0 else Matrix.Identity(4)
            if j.rest:
                local = from_text(j.rest)
                world.append(inv @ ((conv @ pw) @ local) if j.parent >= 0 else inv @ local)
            else:
                pb = binds[j.parent] if j.parent >= 0 else Matrix.Identity(4)
                world.append(pw @ pb.inverted() @ binds[i])
        for i, j in enumerate(sk.joints):
            b = arm_data.bones[j.name]
            B = b.matrix_local
            if j.parent >= 0:
                Bp = arm_data.bones[sk.joints[j.parent].name].matrix_local
                basis = (Bp.inverted() @ B).inverted() @ world[j.parent].inverted() @ world[i]
            else:
                basis = B.inverted() @ world[i]
            arm.pose.bones[j.name].matrix_basis = basis
    return arm


def apply_to_objects(bpy, context, data, objects, mesh_maps, base, convert, warn):
    """data: obj_io.ObjData; objects/mesh_maps: imported mesh objects and their
    {file vertex number: local index}. Returns the armature object or None."""
    max_id = max((j for ws in data.weights.values() for j, _ in ws), default=-1)
    if not data.skel_lines:
        return None
    sk = skel.parse_lines(data.skel_lines, max_id)
    if not sk.ok:
        warn("skeleton ignored (skin weights kept as vertex groups): " +
             "; ".join(sorted(set(sk.errors))))
        return None
    conv = axes(convert)
    inline = all(j.bind is not None for j in sk.joints)
    arm = None
    if inline:
        arm = _build_armature(bpy, context, sk, conv)
    elif is_sidecar(sk.lib):
        arm = _fbx_armature(bpy, context, os.path.join(base, sk.lib), warn, sk.lib_skeleton)
        if arm is not None:
            missing = [j.name for j in sk.joints if j.name not in arm.data.bones]
            if missing:
                warn("joints missing from the skeleton sidecar: " + ", ".join(missing))
    else:
        warn(f"skel_lib {sk.lib}: only .fbx and USD sidecars are supported here")
    if arm is None:
        return None
    if sk.anim:
        if not is_sidecar(sk.anim):
            warn(f"skel_anim {sk.anim}: only .fbx and USD sidecars are supported here")
        elif not inline and sk.anim == sk.lib:
            act = _pick_action(bpy, arm, sk.anim_name)
            if act is not None:
                _assign(arm, act)
        else:
            usd = sk.anim.lower().endswith(USD_EXTS)
            src = _fbx_armature(bpy, context, os.path.join(base, sk.anim), warn)
            act = _pick_action(bpy, src, None if usd else sk.anim_name)
            if act is not None:
                # the sidecar's bones may rest elsewhere (other orientations):
                # bake its world-space pose onto our armature, frame by frame
                _assign(src, act)
                _retarget(bpy, context, src, arm, [j.name for j in sk.joints], act)
            else:
                warn(f"skel_anim {sk.anim}: no animation")
            while src is not None:
                parent = src.parent
                bpy.data.objects.remove(src)
                src = parent
    names = [j.name for j in sk.joints]
    for ob, local_of in zip(objects, mesh_maps):
        groups = {}
        for g, ws in data.weights.items():
            i = local_of.get(g)
            if i is None:
                continue
            for jid, w in ws:
                if w <= 0:
                    continue
                if jid not in groups:
                    groups[jid] = ob.vertex_groups.new(name=names[jid])
                groups[jid].add([i], w, 'REPLACE')
        if groups:
            mod = ob.modifiers.new("Armature", 'ARMATURE')
            mod.object = arm
    return arm


# ---------------------------------------------------------------- export

def armature_of(ob):
    for m in ob.modifiers:
        if m.type == 'ARMATURE' and m.object is not None:
            return m.object
    return None


def joint_order(arm):
    """Bones parents-first (depth-first in Blender's bone order)."""
    out = []

    def visit(b):
        out.append(b)
        for c in b.children:
            visit(c)
    for b in arm.data.bones:
        if b.parent is None:
            visit(b)
    return out


def identifier(name, used):
    s = re.sub(r"[^A-Za-z0-9_]", "_", name) or "_"
    if not ("a" <= s[0].lower() <= "z" or s[0] == "_"):
        s = "_" + s
    base, k = s, 1
    while s in used:
        s, k = f"{base}_{k}", k + 1
    used.add(s)
    return s


class Export:
    """Skeleton of one armature: joint ids and the skel_* lines."""

    def __init__(self, arm, convert, warn):
        self.arm = arm
        self.bones = joint_order(arm)
        used = set()
        self.names = {b.name: identifier(b.name, used) for b in self.bones}
        renamed = [b.name for b in self.bones if self.names[b.name] != b.name]
        if renamed:
            warn("bone names made into identifiers: " + ", ".join(renamed))
        self.ids = {b.name: i for i, b in enumerate(self.bones)}
        self.conv = axes(convert)
        self.anim_file = None

    def weights(self, ob, me):
        gname = {g.index: g.name for g in ob.vertex_groups}
        out = []
        for v in me.vertices:
            w = [(self.ids[gname[g.group]], g.weight) for g in v.groups
                 if gname.get(g.group) in self.ids and g.weight > 0]
            out.append(w)
        return out

    def lines(self):
        sk = skel.Skel()
        sk.ext = True
        world = self.conv @ self.arm.matrix_world
        for b in self.bones:
            parent = self.ids[b.parent.name] if b.parent else -1
            j = skel.Joint(self.names[b.name], parent, to_text(world @ b.matrix_local))
            local = b.parent.matrix_local.inverted() @ b.matrix_local if b.parent else \
                world @ b.matrix_local
            j.rest = to_text(local)
            sk.joints.append(j)
        if self.anim_file:
            sk.anim = self.anim_file
        return sk

    def write_usd(self, context, path, action):
        """USD sidecar written directly, in OBJ space: a Skeleton (joints, bind and
        rest transforms) and a SkelAnimation sampled per frame of the action. No
        transform above the Skeleton (skel-obj.md: sidecar animations are applied
        in the OBJ's skeleton space)."""
        from .obj_io import fmt as num
        scene = context.scene
        f0, f1 = (int(round(x)) for x in action.frame_range)
        world = self.conv @ self.arm.matrix_world
        paths = []
        for b in self.bones:
            n = self.names[b.name]
            paths.append(paths[self.ids[b.parent.name]] + "/" + n if b.parent else n)

        def mat(m):
            t = m.transposed()
            return "(" + ", ".join("(" + ", ".join(num(t[r][c]) for c in range(4)) + ")"
                                   for r in range(4)) + ")"

        def tup(v):
            return "(" + ", ".join(num(x) for x in v) + ")"
        binds = [world @ b.matrix_local for b in self.bones]
        rests = [b.parent.matrix_local.inverted() @ b.matrix_local if b.parent else binds[i]
                 for i, b in enumerate(self.bones)]
        frame = scene.frame_current
        tr, ro, sc = [], [], []
        for f in range(f0, f1 + 1):
            scene.frame_set(f)
            poses = [world @ self.arm.pose.bones[b.name].matrix for b in self.bones]
            t, r, s = [], [], []
            for i, b in enumerate(self.bones):
                local = poses[self.ids[b.parent.name]].inverted() @ poses[i] if b.parent else poses[i]
                loc, q, scale = local.decompose()
                t.append(tup(loc))
                r.append(tup((q.w, q.x, q.y, q.z)))
                s.append(tup(scale))
            tr.append(f"{f}: [{', '.join(t)}]")
            ro.append(f"{f}: [{', '.join(r)}]")
            sc.append(f"{f}: [{', '.join(s)}]")
        scene.frame_set(frame)
        joints = "[" + ", ".join(f'"{p}"' for p in paths) + "]"
        sep = ",\n                "
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(f"""#usda 1.0
(
    defaultPrim = "Rig"
    timeCodesPerSecond = {num(scene.render.fps / scene.render.fps_base)}
    startTimeCode = {f0}
    endTimeCode = {f1}
    upAxis = "{'Y' if self.conv != Matrix.Identity(4) else 'Z'}"
)

# skeleton + animation sidecar of an OBJ (tinyobjloader skel-obj.md), OBJ space
def SkelRoot "Rig"
{{
    def Skeleton "Skel" (
        prepend apiSchemas = ["SkelBindingAPI"]
    )
    {{
        uniform token[] joints = {joints}
        uniform matrix4d[] bindTransforms = [{", ".join(mat(m) for m in binds)}]
        uniform matrix4d[] restTransforms = [{", ".join(mat(m) for m in rests)}]
        rel skel:animationSource = </Rig/Skel/Anim>

        def SkelAnimation "Anim"
        {{
            uniform token[] joints = {joints}
            float3[] translations.timeSamples = {{
                {sep.join(tr)}
            }}
            quatf[] rotations.timeSamples = {{
                {sep.join(ro)}
            }}
            half3[] scales.timeSamples = {{
                {sep.join(sc)}
            }}
        }}
    }}
}}
""")

    def write_sidecar(self, bpy, context, obj_path, warn, fmt="fbx"):
        """Armature + its action -> <stem>_skel.fbx or .usda (Blender's exporters)."""
        ad = self.arm.animation_data
        if ad is None or ad.action is None:
            return
        name = os.path.splitext(os.path.basename(obj_path))[0] + "_skel." + \
            ("usda" if fmt == "usd" else "fbx")
        path = os.path.join(os.path.dirname(obj_path), name)
        if any(self.names[b.name] != b.name for b in self.bones):
            warn("skeleton sidecar not written: bone names are not identifiers")
            return
        sel = [(o, o.select_get()) for o in context.view_layer.objects]
        active = context.view_layer.objects.active
        for o, _ in sel:
            o.select_set(o is self.arm)
        context.view_layer.objects.active = self.arm
        try:
            if fmt == "usd":
                self.write_usd(context, path, ad.action)
                self.anim_file = name
                return
            bpy.ops.export_scene.fbx(filepath=path, use_selection=True, object_types={'ARMATURE'},
                                     add_leaf_bones=False, bake_anim=True,
                                     bake_anim_use_all_actions=False,
                                     bake_anim_use_nla_strips=False, axis_forward='-Z',
                                     axis_up='Y', apply_scale_options='FBX_SCALE_ALL')
            self.anim_file = name
        except Exception as e:  # noqa: BLE001
            warn(f"skeleton sidecar not written: {e}")
        finally:
            for o, s in sel:
                o.select_set(s)
            context.view_layer.objects.active = active
