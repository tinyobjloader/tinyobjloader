"""Subdivision tags <-> Blender (Subdivision Surface modifier + crease attributes).

Blender's OpenSubdiv bridge uses sharpness = 10 * crease**2 (checked by
experiment: at level L a crease of sqrt(L/10) and above is exactly as sharp as
an infinite crease, anything below is not), so a tag sharpness s becomes the
crease value sqrt(min(s, 10) / 10).

What Blender cannot represent is kept in object custom properties and written
back on export:
  obj_subd_present     scalar tags present in the file (comma-separated)
  obj_subd_scheme      "loop" (imported as Catmull-Clark)
  obj_subd_boundary    0 (vertex boundary "none"; Blender has no equivalent)
  obj_subd_creasemethod, obj_subd_smoothtriangles
  obj_subd_unknown     unknown tag lines, verbatim
and the face attribute `obj_subd_hole` (holes are not rendered by Blender).
"""
import math

from . import subd

# facevaryinginterpolateboundary value <-> Subdivision Surface `uv_smooth`
FVAR_TO_UV_SMOOTH = ["SMOOTH_ALL", "PRESERVE_CORNERS", "PRESERVE_CORNERS_AND_JUNCTIONS",
                     "PRESERVE_CORNERS_JUNCTIONS_AND_CONCAVE", "PRESERVE_BOUNDARIES", "NONE"]
# interpolateboundary value <-> `boundary_smooth` (0 = none has no equivalent)
BOUNDARY_TO_SMOOTH = {1: "PRESERVE_CORNERS", 2: "ALL"}
HOLE_ATTR = "obj_subd_hole"


def crease_from_sharpness(s):
    return math.sqrt(min(max(s, 0.0), 10.0) / 10.0)


def sharpness_from_crease(c):
    return 10.0 * c * c


def sharp_text(x):
    return "10" if x >= 10.0 else f"{x:.6g}"



def apply_to_object(ob, s, local_of, warn):
    """Set up `ob` (mesh object) from an accepted subd.Subd; `local_of` maps
    file vertex numbers to the object's vertex indices."""
    me = ob.data
    present = []
    mod = ob.modifiers.new("Subdivision", 'SUBSURF')
    mod.levels = mod.render_levels = 2
    mod.use_creases = True
    if s.scheme is not None:
        present.append("scheme")
        if s.scheme == 2:
            mod.subdivision_type = 'SIMPLE'
        elif s.scheme == 1:
            ob["obj_subd_scheme"] = "loop"
            warn(f"{ob.name}: Blender has no Loop subdivision; using Catmull-Clark")
    if s.interp_boundary is not None:
        present.append("interpolateboundary")
        if s.interp_boundary == 0:
            ob["obj_subd_boundary"] = 0
            warn(f"{ob.name}: vertex boundary 'none' has no Blender equivalent")
        else:
            mod.boundary_smooth = BOUNDARY_TO_SMOOTH[s.interp_boundary]
    else:
        # absent: OpenSubdiv OBJ-reader default, edge only (subd-obj.md)
        mod.boundary_smooth = 'ALL'
    if s.fvar_interp_boundary is not None:
        present.append("facevaryinginterpolateboundary")
        mod.uv_smooth = FVAR_TO_UV_SMOOTH[s.fvar_interp_boundary]
    else:
        # absent: default "all" (fully linear UVs)
        mod.uv_smooth = 'NONE'
    if s.crease_method is not None:
        present.append("creasemethod")
        ob["obj_subd_creasemethod"] = subd.CREASE_METHODS[s.crease_method]
        if s.crease_method == 1:
            warn(f"{ob.name}: Chaikin creasing is not supported by Blender")
    if s.smooth_triangles is not None:
        present.append("smoothtriangles")
        ob["obj_subd_smoothtriangles"] = subd.TRI_SUBDIV[s.smooth_triangles]
    ob["obj_subd_present"] = ",".join(present)
    if s.unknown:
        ob["obj_subd_unknown"] = "\n".join(s.unknown)

    if s.creases:
        attr = me.attributes.get("crease_edge") or me.attributes.new("crease_edge", 'FLOAT', 'EDGE')
        index = {tuple(sorted(e.vertices)): e.index for e in me.edges}
        for (a, b), text in s.creases.items():
            key = tuple(sorted((local_of[a], local_of[b])))
            attr.data[index[key]].value = crease_from_sharpness(subd.sharpness(text))
    if s.corners:
        attr = me.attributes.get("crease_vert") or me.attributes.new("crease_vert", 'FLOAT', 'POINT')
        for v, text in s.corners.items():
            attr.data[local_of[v]].value = crease_from_sharpness(subd.sharpness(text))
    if s.holes:
        attr = me.attributes.new(HOLE_ATTR, 'BOOLEAN', 'FACE')
        for h in s.holes:
            attr.data[h].value = True
        warn(f"{ob.name}: {len(s.holes)} hole face(s) kept as attribute '{HOLE_ATTR}' "
             "(Blender does not render subdivision holes)")


def tag_lines_for(ob, me):
    """Canonical `t` lines for an exported mesh, as a function of the vertex
    offset. `me` is the exported (base) mesh of `ob`; None if no subd data."""
    mod = next((m for m in ob.modifiers if m.type == 'SUBSURF'), None)
    ce, cv = me.attributes.get("crease_edge"), me.attributes.get("crease_vert")
    holes = me.attributes.get(HOLE_ATTR)
    if mod is None and ce is None and cv is None:
        return None
    present = set(filter(None, str(ob.get("obj_subd_present", "")).split(",")))
    authored = "obj_subd_present" not in ob  # made in Blender: write all scalars
    lines = []
    if mod is not None:
        if mod.subdivision_type == 'SIMPLE':
            scheme = "bilinear"
        else:
            scheme = "loop" if ob.get("obj_subd_scheme") == "loop" else "catmark"
        if authored or "scheme" in present or scheme != "catmark":
            lines.append(f"t scheme 0/0/1 {scheme}")
        ib = {"PRESERVE_CORNERS": 1, "ALL": 2}[mod.boundary_smooth]
        if ob.get("obj_subd_boundary") == 0 and mod.boundary_smooth == 'ALL':
            ib = 0
        if authored or "interpolateboundary" in present or mod.boundary_smooth != 'ALL':
            lines.append(f"t interpolateboundary 1/0/0 {ib}")
        if authored or "facevaryinginterpolateboundary" in present or mod.uv_smooth != 'NONE':
            lines.append(f"t facevaryinginterpolateboundary 1/0/0 {FVAR_TO_UV_SMOOTH.index(mod.uv_smooth)}")
        if "obj_subd_creasemethod" in ob:
            lines.append(f"t creasemethod 0/0/1 {ob['obj_subd_creasemethod']}")
        if "obj_subd_smoothtriangles" in ob and scheme == "catmark":
            lines.append(f"t smoothtriangles 0/0/1 {ob['obj_subd_smoothtriangles']}")
    creases = []
    if ce is not None:
        for e in me.edges:
            c = ce.data[e.index].value
            if c > 0:
                a, b = sorted(e.vertices)
                creases.append((a, b, sharp_text(sharpness_from_crease(c))))
    corners = []
    if cv is not None:
        for v in me.vertices:
            c = cv.data[v.index].value
            if c > 0:
                corners.append((v.index, sharp_text(sharpness_from_crease(c))))
    hole_faces = [p.index for p in me.polygons if holes is not None and holes.data[p.index].value]
    unknown = [l for l in str(ob.get("obj_subd_unknown", "")).split("\n") if l]

    def at(offset):
        out = list(lines)
        out += [f"t crease 2/1/0 {offset + a} {offset + b} {s}" for a, b, s in creases]
        out += [f"t corner 1/1/0 {offset + v} {s}" for v, s in corners]
        if hole_faces:
            out.append(f"t hole {len(hole_faces)}/0/0 " + " ".join(map(str, hole_faces)))
        return out + unknown
    return at
