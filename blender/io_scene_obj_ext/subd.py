"""Subdivision-surface tags (`t` lines) in .obj -- pure Python.

Port of tobj_subd.c / the Lean model formal/Subd (see subd-obj.md). `dump_obj`
produces the same text as `tests/subd_dump` and the Lean `subdobj`, which the
add-on tests use to check this port against the C implementation.

Vertex numbers in tags are 0-based over the whole file; hole numbers are
0-based over the mesh's faces.
"""

MAX_COUNT = 8192
SCHEMES = ["catmark", "loop", "bilinear"]
CREASE_METHODS = ["normal", "chaikin"]
TRI_SUBDIV = ["catmark", "smooth"]


def tokens(line):
    """Maximal runs of characters other than space and tab."""
    return [t for t in line.replace("\t", " ").split(" ") if t]


def drop_cr(line):
    return line[:-1] if line.endswith("\r") else line


def parse_int(s):
    """`[+-]?[0-9]+` -> int, or None."""
    body = s[1:] if s[:1] in ("+", "-") else s
    if not body or not all("0" <= c <= "9" for c in body):
        return None
    v = int(body)
    return -v if s[:1] == "-" else v


def is_decimal(s):
    """`[+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][+-]?[0-9]+)?`"""
    i, n, d = 0, len(s), 0
    if i < n and s[i] in "+-":
        i += 1
    while i < n and "0" <= s[i] <= "9":
        i, d = i + 1, d + 1
    if i < n and s[i] == ".":
        i += 1
        while i < n and "0" <= s[i] <= "9":
            i, d = i + 1, d + 1
    if d == 0:
        return False
    if i < n and s[i] in "eE":
        i += 1
        if i < n and s[i] in "+-":
            i += 1
        e = 0
        while i < n and "0" <= s[i] <= "9":
            i, e = i + 1, e + 1
        if e == 0:
            return False
    return i == n


def parse_counts(s):
    parts = s.split("/")
    if len(parts) != 3:
        return None
    out = []
    for p in parts:
        if not p or not all("0" <= c <= "9" for c in p) or int(p) > MAX_COUNT:
            return None
        out.append(int(p))
    return tuple(out)


def sharp_text(t):
    """Negative sharpness counts as 0."""
    return "0" if t.startswith("-") else t


def sharpness(text):
    """Sharpness as a number (>= 0; 10 or more is infinitely sharp)."""
    try:
        v = float(text)
    except ValueError:
        return 0.0
    return v if v > 0 else 0.0


class Subd:
    """Typed tags of one mesh. Scalars are None when the tag is absent."""

    def __init__(self):
        self.scheme = None             # index into SCHEMES
        self.interp_boundary = None    # 0..2
        self.fvar_interp_boundary = None  # 0..5
        self.crease_method = None      # index into CREASE_METHODS
        self.smooth_triangles = None   # index into TRI_SUBDIV
        self.creases = {}              # (v0, v1) with v0 < v1 -> sharpness text (insertion order)
        self.corners = {}              # v -> sharpness text
        self.holes = []                # face numbers, no repeats
        self.unknown = []              # canonical lines of unknown tags
        self.errors = []

    @property
    def ok(self):
        return not self.errors

    def to_lines(self):
        """Canonical tag lines (subd-obj.md); empty when not ok."""
        if not self.ok:
            return []
        out = []
        if self.scheme is not None:
            out.append(f"t scheme 0/0/1 {SCHEMES[self.scheme]}")
        if self.interp_boundary is not None:
            out.append(f"t interpolateboundary 1/0/0 {self.interp_boundary}")
        if self.fvar_interp_boundary is not None:
            out.append(f"t facevaryinginterpolateboundary 1/0/0 {self.fvar_interp_boundary}")
        if self.crease_method is not None:
            out.append(f"t creasemethod 0/0/1 {CREASE_METHODS[self.crease_method]}")
        if self.smooth_triangles is not None:
            out.append(f"t smoothtriangles 0/0/1 {TRI_SUBDIV[self.smooth_triangles]}")
        for (a, b), s in self.creases.items():
            out.append(f"t crease 2/1/0 {a} {b} {s}")
        for v, s in self.corners.items():
            out.append(f"t corner 1/1/0 {v} {s}")
        for i in range(0, len(self.holes), MAX_COUNT):
            hs = self.holes[i:i + MAX_COUNT]
            out.append(f"t hole {len(hs)}/0/0 " + " ".join(map(str, hs)))
        out += self.unknown
        return out


def _topology(faces):
    edges, verts = set(), set()
    for f in faces:
        n = len(f)
        for k in range(n):
            a, b = f[k], f[(k + 1) % n]
            edges.add((min(a, b), max(a, b)))
            verts.add(a)
    return edges, verts


def parse_lines(lines, faces):
    """Parse and check a mesh's `t` lines against its faces (lists of 0-based
    file vertex numbers, as written; not triangulated)."""
    s = Subd()
    edges, verts = _topology(faces)
    nfaces = len(faces)

    def err(msg):
        s.errors.append(msg)

    def scalar(attr, v):
        if getattr(s, attr) is not None:
            err("repeated scalar tag")
        else:
            setattr(s, attr, v)

    for raw in lines:
        tk = tokens(drop_cr(raw))
        if not tk or tk[0] != "t":
            continue
        a = tk[1:]
        if len(a) < 2:
            err("t: expected <name> <ni>/<nf>/<ns>")
            continue
        name, c = a[0], parse_counts(a[1])
        if c is None:
            err("t: bad counts")
            continue
        ni, nf, ns = c
        rest = a[2:]
        if len(rest) != ni + nf + ns:
            err("t: argument count")
            continue
        ints = [parse_int(x) for x in rest[:ni]]
        if any(x is None for x in ints):
            err("t: bad integer")
            continue
        flts = rest[ni:ni + nf]
        if not all(is_decimal(x) for x in flts):
            err("t: bad decimal")
            continue
        strs = rest[ni + nf:]
        if name == "crease":
            if not (ni >= 2 and ni % 2 == 0 and ns == 0 and (nf == 1 or nf == ni // 2)):
                err("crease: counts")
                continue
            for k in range(ni // 2):
                x, y = ints[2 * k], ints[2 * k + 1]
                if x < 0 or y < 0 or x == y:
                    err("crease: bad edge")
                    continue
                key = (min(x, y), max(x, y))
                if key not in edges:
                    err("crease: not an edge of the mesh")
                    continue
                s.creases[key] = sharp_text(flts[0 if nf == 1 else k])
        elif name == "corner":
            if not (ni >= 1 and ns == 0 and (nf == 1 or nf == ni)):
                err("corner: counts")
                continue
            for k, x in enumerate(ints):
                if x < 0 or x not in verts:
                    err("corner: vertex not in the mesh")
                    continue
                s.corners[x] = sharp_text(flts[0 if nf == 1 else k])
        elif name == "hole":
            if not (ni >= 1 and nf == 0 and ns == 0):
                err("hole: counts")
                continue
            for x in ints:
                if x < 0 or x >= nfaces:
                    err("hole: not a face of the mesh")
                elif x not in s.holes:
                    s.holes.append(x)
        elif name in ("interpolateboundary", "facevaryinginterpolateboundary",
                      "facevaryingpropagatecorners"):
            if (ni, nf, ns) != (1, 0, 0):
                err("t: expected 1/0/0")
                continue
            if name == "facevaryingpropagatecorners":
                continue  # obsolete
            fv = name == "facevaryinginterpolateboundary"
            x = ints[0]
            if x < 0 or x > (5 if fv else 2):
                err("t: value out of range")
                continue
            scalar("fvar_interp_boundary" if fv else "interp_boundary", x)
        elif name in ("scheme", "creasemethod", "smoothtriangles"):
            if (ni, nf, ns) != (0, 0, 1):
                err("t: expected 0/0/1")
                continue
            table, attr = {"scheme": (SCHEMES, "scheme"),
                           "creasemethod": (CREASE_METHODS, "crease_method"),
                           "smoothtriangles": (TRI_SUBDIV, "smooth_triangles")}[name]
            if strs[0] not in table:
                err("t: unknown value")
                continue
            scalar(attr, table.index(strs[0]))
        else:
            s.unknown.append(" ".join(["t"] + a))

    if s.smooth_triangles is not None and s.scheme is not None and s.scheme != 0:
        err("smoothtriangles: catmark scheme only")
    if s.scheme == 1 and not all(len(f) == 3 for f in faces):
        err("scheme loop: all faces must be triangles")
    return s


def _face_vertex(tok, nverts):
    v = parse_int(tok.split("/", 1)[0])
    if v is None or v == 0:
        return None
    idx = v - 1 if v > 0 else nverts + v
    return idx if 0 <= idx < nverts else None


def dump_obj(text):
    """Same output as tobj_subd_dump_obj (the .obj subset used for testing)."""
    meshes, nverts = [{"lines": [], "faces": []}], 0
    for raw in text.split("\n"):
        line = drop_cr(raw)
        tk = tokens(line)
        if not tk:
            continue
        kw, cur = tk[0], meshes[-1]
        if kw == "v":
            nverts += 1
        elif kw in ("o", "g"):
            meshes.append({"lines": [], "faces": []})
        elif kw == "t":
            cur["lines"].append(line)
        elif kw == "f" and len(tk) >= 4:
            f = [_face_vertex(t, nverts) for t in tk[1:]]
            if all(x is not None for x in f):
                cur["faces"].append(f)
    out = []
    for i, m in enumerate(meshes):
        if not m["faces"] and not m["lines"]:
            continue
        s = parse_lines(m["lines"], m["faces"])
        out.append(f"mesh {i} ok={1 if s.ok else 0}\n")
        out += [l + "\n" for l in s.to_lines()]
    return "".join(out)
