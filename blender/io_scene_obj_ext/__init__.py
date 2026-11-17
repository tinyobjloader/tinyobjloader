"""OBJ import/export with subdivision tags and MaterialX-in-MTL.

Extensions of tinyobjloader (https://github.com/tinyobjloader/tinyobjloader):
  subd-obj.md   OpenSubdiv `t` tags: scheme, boundaries, creases, corners, holes
  mtlx-mtl.md   MaterialX node graphs in .mtl (`mtlx_*` lines)
  skel-obj.md   skeletons for the `vw` skin weights (`skel_*` lines; armatures,
                vertex groups, optional .fbx sidecar for skeleton/animation)
All are parsed and checked by pure-Python ports of the reference C code
(`subd.py`, `mtlx.py`), so the add-on needs no compiled module.

Axes: OBJ is Y-up; Blender is Z-up. By default positions are converted
(x, y, z)_obj <-> (x, -z, y)_blender, like Blender's own OBJ add-on.
"""
bl_info = {
    "name": "OBJ (subdivision + MaterialX extensions)",
    "author": "tinyobjloader contributors",
    "version": (0, 2, 0),
    "blender": (4, 2, 0),
    "location": "File > Import-Export",
    "description": "OBJ/MTL with OpenSubdiv subdivision tags, MaterialX-in-MTL and skeletons",
    "category": "Import-Export",
}

import os

if "bpy" in locals():
    import importlib
    from . import subd, mtlx, skel, obj_io, subd_blender, materials_blender, skel_blender
    for _m in (subd, mtlx, skel, obj_io, subd_blender, materials_blender, skel_blender):
        importlib.reload(_m)
else:
    from . import subd, mtlx, skel, obj_io, subd_blender, materials_blender, skel_blender

import bpy
from bpy.props import BoolProperty, EnumProperty, StringProperty
from bpy_extras.io_utils import ExportHelper, ImportHelper


def _to_blender(v, convert):
    return (v[0], -v[2], v[1]) if convert else v


def _to_obj(v, convert):
    return (v[0], v[2], -v[1]) if convert else v


# ---------------------------------------------------------------- import

def import_obj(context, path, convert_axes=True, report=None):
    warnings = []
    warn = warnings.append
    data = obj_io.read_obj(path)
    warnings += data.warnings
    base = os.path.dirname(path)

    mtl = {}
    for lib in data.mtllibs:
        p = os.path.join(base, lib)
        if os.path.exists(p):
            mtl.update(obj_io.read_mtl(p))
        else:
            warn(f"material library not found: {lib}")
    materials = {}

    def material(name):
        if name is None:
            return None
        if name not in materials:
            mat = bpy.data.materials.new(name)
            classic, ext = mtl.get(name, ({}, None))
            if ext is not None and ext.ext and not ext.ok:
                warn(f"{name}: MaterialX-in-MTL extension is ill-formed; using the classic keys")
            materials_blender.build_material(bpy, mat, ext if ext is not None and ext.ok else None,
                                             classic, base, warn)
            materials[name] = mat
        return materials[name]

    objects, maps = [], []
    for m in data.meshes:
        used = sorted({v for vs, _ in m.faces for v in vs})
        local_of = {g: i for i, g in enumerate(used)}
        me = bpy.data.meshes.new(m.name or "mesh")
        me.from_pydata([_to_blender(data.vertices[g], convert_axes) for g in used], [],
                       [[local_of[v] for v in vs] for vs, _ in m.faces])
        me.validate()
        if any(ts is not None for _, ts in m.faces):
            uv = me.uv_layers.new(name="UVMap")
            li = 0
            for (vs, ts) in m.faces:
                for k in range(len(vs)):
                    uv.data[li].uv = data.texcoords[ts[k]] if ts is not None else (0.0, 0.0)
                    li += 1
        names = []
        for fm in m.face_mat:
            if fm is not None and fm not in names:
                names.append(fm)
        for n in names:
            me.materials.append(material(n))
        for p, fm, sm in zip(me.polygons, m.face_mat, m.face_smooth):
            p.material_index = names.index(fm) if fm in names else 0
            p.use_smooth = sm or bool(m.tag_lines)
        ob = bpy.data.objects.new(m.name or "mesh", me)
        context.collection.objects.link(ob)
        if m.tag_lines:
            s = subd.parse_lines(m.tag_lines, [vs for vs, _ in m.faces])
            if s.ok:
                subd_blender.apply_to_object(ob, s, local_of, warn)
            else:
                warn(f"{ob.name}: subdivision tags ignored: " + "; ".join(sorted(set(s.errors))))
        objects.append(ob)
        maps.append(local_of)
    skel_blender.apply_to_objects(bpy, context, data, objects, maps, base, convert_axes, warn)
    for w in warnings:
        if report:
            report({'WARNING'}, w)
        else:
            print("obj_ext:", w)
    return objects, warnings


# ---------------------------------------------------------------- export

def export_obj(context, path, objects, convert_axes=True, apply_transform=True, report=None,
               skel_sidecar=True, sidecar_format="fbx"):
    warnings = []
    warn = warnings.append
    out_dir = os.path.dirname(path)
    mtl_name = os.path.splitext(os.path.basename(path))[0] + ".mtl"
    meshes, mats = [], []
    skeleton = None
    for ob in objects:
        if ob.type != 'MESH':
            continue
        me = ob.data
        em = obj_io.ExportMesh(ob.name.replace(" ", "_"))
        arm = skel_blender.armature_of(ob)
        if arm is not None:
            if skeleton is None:
                skeleton = skel_blender.Export(arm, convert_axes, warn)
            if arm is skeleton.arm:
                em.weights = skeleton.weights(ob, me)
            else:
                warn(f"{ob.name}: second armature {arm.name} not written (one skeleton per file)")
        mw = ob.matrix_world if apply_transform else None
        for v in me.vertices:
            co = mw @ v.co if mw is not None else v.co
            em.vertices.append(_to_obj(tuple(co), convert_axes))
        uv = me.uv_layers.active
        uvidx = {}
        for p in me.polygons:
            vs = list(p.vertices)
            ts = None
            if uv is not None:
                ts = []
                for li in p.loop_indices:
                    key = tuple(round(c, 6) for c in uv.data[li].uv)
                    if key not in uvidx:
                        uvidx[key] = len(em.uvs)
                        em.uvs.append(key)
                    ts.append(uvidx[key])
            em.faces.append((vs, ts))
            slot = me.materials[p.material_index] if p.material_index < len(me.materials) else None
            em.face_mat.append(slot.name if slot else None)
            em.face_smooth.append(p.use_smooth)
            if slot is not None and slot not in mats:
                mats.append(slot)
        lines_at = subd_blender.tag_lines_for(ob, me)
        if lines_at is not None:
            # canonical form, checked like a loader would (offset 0: local faces)
            s = subd.parse_lines(lines_at(0), [vs for vs, _ in em.faces])
            if s.ok:
                em.tag_lines = lambda off, s=s, lines_at=lines_at: subd.parse_lines(
                    lines_at(off), [[off + v for v in vs] for vs, _ in em.faces]).to_lines()
            else:
                warn(f"{ob.name}: subdivision data not written: " + "; ".join(sorted(set(s.errors))))
        meshes.append(em)

    out_mats = []
    for mat in mats:
        classic, ext = materials_blender.material_lines(bpy, mat, out_dir, warn)
        if ext:
            m = mtlx.parse_mtl("newmtl x\n" + "\n".join(ext) + "\n")[0]
            if m.ok:
                ext = m.to_lines()
            else:
                warn(f"{mat.name}: generated MaterialX lines are not well-formed; writing classic keys only")
                ext = []
        out_mats.append((mat.name, classic, ext))
    skel_lines = []
    if skeleton is not None:
        if skel_sidecar:
            skeleton.write_sidecar(bpy, context, path, warn, sidecar_format)
        sk = skeleton.lines()
        max_id = max((j for em in meshes for ws in em.weights for j, _ in ws), default=-1)
        checked = skel.parse_lines(sk.to_lines(), max_id)  # checked like a loader would
        if checked.ok:
            skel_lines = checked.to_lines()
        else:
            warn("skeleton not written: " + "; ".join(sorted(set(checked.errors))))
    obj_io.write_obj(path, meshes, mtl_name if out_mats else None, skel_lines)
    if out_mats:
        obj_io.write_mtl(os.path.join(out_dir, mtl_name), out_mats)
    for w in warnings:
        if report:
            report({'WARNING'}, w)
        else:
            print("obj_ext:", w)
    return warnings


# ---------------------------------------------------------------- operators

class IMPORT_SCENE_OT_obj_ext(bpy.types.Operator, ImportHelper):
    """Import OBJ with subdivision tags and MaterialX-in-MTL"""
    bl_idname = "import_scene.obj_ext"
    bl_label = "Import OBJ (subd + MaterialX)"
    bl_options = {'UNDO'}
    filename_ext = ".obj"
    filter_glob: StringProperty(default="*.obj", options={'HIDDEN'})
    convert_axes: BoolProperty(name="Y-up to Z-up", default=True)

    def execute(self, context):
        import_obj(context, self.filepath, self.convert_axes, self.report)
        return {'FINISHED'}


class EXPORT_SCENE_OT_obj_ext(bpy.types.Operator, ExportHelper):
    """Export OBJ with subdivision tags and MaterialX-in-MTL"""
    bl_idname = "export_scene.obj_ext"
    bl_label = "Export OBJ (subd + MaterialX)"
    filename_ext = ".obj"
    filter_glob: StringProperty(default="*.obj", options={'HIDDEN'})
    convert_axes: BoolProperty(name="Z-up to Y-up", default=True)
    apply_transform: BoolProperty(name="Apply object transform", default=True)
    selection_only: BoolProperty(name="Selection only", default=False)
    skel_sidecar: BoolProperty(name="Animation sidecar", default=True,
                               description="Write the armature's action to <name>_skel.fbx/.usda (skel_anim)")
    sidecar_format: EnumProperty(name="Sidecar format", default='fbx',
                                 items=(('fbx', "FBX", "Blender's FBX exporter"),
                                        ('usd', "USD", "Blender's USD exporter (.usda)")))

    def execute(self, context):
        obs = context.selected_objects if self.selection_only else context.scene.objects
        export_obj(context, self.filepath, list(obs), self.convert_axes, self.apply_transform,
                   self.report, self.skel_sidecar, self.sidecar_format)
        return {'FINISHED'}


def _menu_import(self, context):
    self.layout.operator(IMPORT_SCENE_OT_obj_ext.bl_idname, text="OBJ with subd + MaterialX + skeleton (.obj)")


def _menu_export(self, context):
    self.layout.operator(EXPORT_SCENE_OT_obj_ext.bl_idname, text="OBJ with subd + MaterialX + skeleton (.obj)")


_classes = (IMPORT_SCENE_OT_obj_ext, EXPORT_SCENE_OT_obj_ext)


def register():
    for c in _classes:
        bpy.utils.register_class(c)
    bpy.types.TOPBAR_MT_file_import.append(_menu_import)
    bpy.types.TOPBAR_MT_file_export.append(_menu_export)


def unregister():
    bpy.types.TOPBAR_MT_file_export.remove(_menu_export)
    bpy.types.TOPBAR_MT_file_import.remove(_menu_import)
    for c in reversed(_classes):
        bpy.utils.unregister_class(c)
