"""Plain OBJ/MTL reading and writing (no Blender dependency).

The reader keeps what the add-on needs: positions, texture coordinates,
faces (as written, never triangulated), per-face materials, smoothing, the
`t` lines of each mesh, and the `mtllib` files. A new mesh starts at every
`o` or `g` line, which is also the scope of `t` tags (subd-obj.md).
"""
import os

from . import mtlx


class ObjMesh:
    def __init__(self, name):
        self.name = name
        self.faces = []        # [(file vertex numbers, texcoord numbers or None)], 0-based
        self.face_mat = []     # material name or None, per face
        self.face_smooth = []  # bool per face
        self.tag_lines = []


class ObjData:
    def __init__(self):
        self.vertices, self.texcoords = [], []
        self.meshes = [ObjMesh("")]
        self.mtllibs = []
        self.skel_lines = []   # file scope (skel-obj.md), verbatim
        self.weights = {}      # file vertex number (0-based) -> [(joint id, weight)]
        self.warnings = []


def _index(tok, count):
    v = int(tok)
    i = v - 1 if v > 0 else count + v
    if v == 0 or not 0 <= i < count:
        raise ValueError(tok)
    return i


def read_obj(path):
    d = ObjData()
    mat, smooth = None, False
    with open(path, "r", encoding="utf-8", errors="surrogateescape") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.rstrip("\n").rstrip("\r")
            tk = line.split()
            if not tk or tk[0].startswith("#"):
                continue
            kw = tk[0]
            try:
                if kw == "v":
                    d.vertices.append(tuple(float(x) for x in tk[1:4]))
                elif kw == "vt":
                    uv = [float(x) for x in tk[1:3]] + [0.0] * (2 - len(tk[1:3]))
                    d.texcoords.append(tuple(uv))
                elif kw in ("o", "g"):
                    d.meshes.append(ObjMesh(line.split(None, 1)[1].strip() if len(tk) > 1 else ""))
                elif kw == "f":
                    vs, ts = [], []
                    for c in tk[1:]:
                        parts = c.split("/")
                        vs.append(_index(parts[0], len(d.vertices)))
                        ts.append(_index(parts[1], len(d.texcoords))
                                  if len(parts) > 1 and parts[1] else None)
                    if len(vs) < 3:
                        raise ValueError("face with fewer than 3 vertices")
                    m = d.meshes[-1]
                    m.faces.append((vs, ts if all(t is not None for t in ts) else None))
                    m.face_mat.append(mat)
                    m.face_smooth.append(smooth)
                elif kw in ("skel_joint", "skel_rest", "skel_lib", "skel_anim"):
                    d.skel_lines.append(line)
                elif kw == "vw":
                    v = int(tk[1])
                    if v < 0 or len(tk) % 2:
                        raise ValueError("expected vw <vertex> (<joint> <weight>)...")
                    d.weights[v] = [(int(tk[k]), float(tk[k + 1])) for k in range(2, len(tk), 2)]
                elif kw == "t":
                    d.meshes[-1].tag_lines.append(line.strip(" \t"))
                elif kw == "usemtl":
                    mat = line.split(None, 1)[1].strip() if len(tk) > 1 else None
                elif kw == "s":
                    smooth = len(tk) > 1 and tk[1] not in ("off", "0")
                elif kw == "mtllib":
                    d.mtllibs += tk[1:]
            except (ValueError, IndexError) as e:
                d.warnings.append(f"{os.path.basename(path)}:{lineno}: skipped `{kw}` line ({e})")
    d.meshes = [m for m in d.meshes if m.faces]
    return d


# ---------------------------------------------------------------- .mtl

CLASSIC_KEYS = ("Kd", "Ks", "Ke", "Ns", "Ni", "d", "Tr", "Pr", "Pm", "illum",
                "map_Kd", "map_Ks", "map_Pr", "map_Pm", "map_Ke", "map_d",
                "norm", "map_Bump", "bump")


def read_mtl(path):
    """{name: (classic {key: [tokens]}, mtlx.Material)} in file order."""
    with open(path, "r", encoding="utf-8", errors="surrogateescape") as f:
        text = f.read()
    ext = {m.name: m for m in mtlx.parse_mtl(text)}
    out, cur = {}, None
    for raw in text.split("\n"):
        line = raw.rstrip("\r")
        tk = line.split()
        if not tk or tk[0].startswith("#"):
            continue
        if tk[0] == "newmtl":
            cur = mtlx.rest_after_keyword(line)
            out[cur] = ({}, ext.get(cur))
        elif cur is not None and tk[0] in CLASSIC_KEYS:
            out[cur][0][tk[0]] = tk[1:]
    return out


# ---------------------------------------------------------------- writing

def fmt(x):
    s = f"{x:.6f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


class ExportMesh:
    def __init__(self, name):
        self.name = name
        self.vertices = []   # (x, y, z)
        self.uvs = []        # (u, v)
        self.faces = []      # [(local vertex indices, local uv indices or None)]
        self.face_mat = []   # material name or None
        self.face_smooth = []
        self.tag_lines = lambda offset: []  # canonical `t` lines given the vertex offset
        self.weights = []    # per local vertex: [(joint id, weight)] (empty: no vw line)


def write_obj(path, meshes, mtl_name=None, skel_lines=()):
    voff = toff = 0
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("# tinyobjloader io_scene_obj_ext (subd-obj.md, mtlx-mtl.md, skel-obj.md)\n")
        for line in skel_lines:
            f.write(line + "\n")
        if mtl_name:
            f.write(f"mtllib {mtl_name}\n")
        for m in meshes:
            f.write(f"o {m.name}\n")
            for v in m.vertices:
                f.write("v " + " ".join(fmt(c) for c in v) + "\n")
            for i, w in enumerate(m.weights):
                if w:
                    f.write(f"vw {voff + i} " + " ".join(f"{j} {fmt(x)}" for j, x in w) + "\n")
            for t in m.uvs:
                f.write("vt " + " ".join(fmt(c) for c in t) + "\n")
            mat = smooth = object()
            for (vs, ts), fm, sm in zip(m.faces, m.face_mat, m.face_smooth):
                if fm != mat:
                    f.write(f"usemtl {fm}\n" if fm else "usemtl\n")
                    mat = fm
                if sm != smooth:
                    f.write("s 1\n" if sm else "s off\n")
                    smooth = sm
                if ts is None:
                    f.write("f " + " ".join(str(voff + v + 1) for v in vs) + "\n")
                else:
                    f.write("f " + " ".join(f"{voff + v + 1}/{toff + t + 1}" for v, t in zip(vs, ts)) + "\n")
            for line in m.tag_lines(voff):
                f.write(line + "\n")
            voff += len(m.vertices)
            toff += len(m.uvs)


def write_mtl(path, materials):
    """materials: [(name, classic [(key, value text)], mtlx lines)]"""
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("# tinyobjloader io_scene_obj_ext (mtlx-mtl.md)\n")
        for name, classic, ext in materials:
            f.write(f"\nnewmtl {name}\n")
            for k, v in classic:
                f.write(f"{k} {v}\n")
            for line in ext:
                f.write(line + "\n")
