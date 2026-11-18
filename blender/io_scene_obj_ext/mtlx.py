"""MaterialX-in-MTL (`mtlx_*` lines) -- pure Python.

Port of tobj_mtlx.c / the Lean model formal/Mtlx (see mtlx-mtl.md): tokenizer,
per-material parse, the well-formedness check and the canonical writer.
`verdicts` gives the `mat <name> ext= ok=` lines of `tests/mtlx_dump`, which the
add-on tests use to check this port against the C implementation.
"""

KEYWORDS = ("mtlx_version", "mtlx_surface", "mtlx_node", "mtlx_input",
            "mtlx_include", "mtlx_colorspace")

# type -> (fixed arity, float-array stride)
TYPES = {
    "integer": (0, 0), "boolean": (0, 0), "float": (0, 0), "color3": (3, 0),
    "color4": (4, 0), "vector2": (2, 0), "vector3": (3, 0), "vector4": (4, 0),
    "matrix33": (9, 0), "matrix44": (16, 0), "string": (0, 0), "filename": (0, 0),
    "integerarray": (0, 0), "floatarray": (0, 1), "color3array": (0, 3),
    "color4array": (0, 4), "vector2array": (0, 2), "vector3array": (0, 3),
    "vector4array": (0, 4), "stringarray": (0, 0)}


class UnterminatedQuote(Exception):
    pass


def tokenize(line):
    out, i, n = [], 0, len(line)
    while i < n:
        c = line[i]
        if c in " \t":
            i += 1
        elif c == '"':
            j = line.find('"', i + 1)
            if j < 0:
                raise UnterminatedQuote()
            out.append(line[i + 1:j])
            i = j + 1
        else:
            j = i
            while j < n and line[j] not in " \t":
                j += 1
            out.append(line[i:j])
            i = j
    return out


def _digits(s):
    return bool(s) and all("0" <= c <= "9" for c in s)


def _int_ok(s):
    return _digits(s[1:] if s[:1] in "+-" and s else s)


def _float_ok(s):
    body = s[1:] if s[:1] in ("+", "-") else s
    e = next((i for i, c in enumerate(body) if c in "eE"), len(body))
    mant, dot = body[:e], body[:e].find(".")
    digits = [c for i, c in enumerate(mant) if i != dot]
    if not digits or not all("0" <= c <= "9" for c in digits):
        return False
    return e == len(body) or _int_ok(body[e + 1:])


def _strip(s):
    return s.strip(" \t\n\r")


def _fields(s, f, array):
    if array and not _strip(s):
        return 0
    parts = s.split(",")
    return len(parts) if all(f(_strip(p)) for p in parts) else -1


def value_ok(ty, v):
    if ty not in TYPES:
        return False
    arity, stride = TYPES[ty]
    if ty == "integer":
        return _int_ok(_strip(v))
    if ty == "boolean":
        return v in ("true", "false")
    if ty == "float":
        return _float_ok(_strip(v))
    if ty in ("string", "filename", "stringarray"):
        return True
    if ty == "integerarray":
        return _fields(v, _int_ok, True) >= 0
    if arity:
        return _fields(v, _float_ok, False) == arity
    n = _fields(v, _float_ok, True)
    return n >= 0 and n % stride == 0


def valid_name(s):
    return bool(s) and (s[0].isascii() and (s[0].isalpha() or s[0] == "_")) and all(
        c.isascii() and (c.isalnum() or c == "_") for c in s)


def is_ref(t):
    return t.startswith("@") and not t.startswith("@@")


def unescape(t):
    return t[1:] if t.startswith("@@") else t


class Material:
    def __init__(self, name):
        self.name = name
        self.versions, self.surface, self.nodes = [], [], []  # nodes: (name, cat, type)
        self.inputs = []       # (node, port, type, value text)
        self.conns = []        # (src, src_out or None, dst, port, type)
        self.colorspaces = []  # (node, port, colorspace)
        self.includes, self.errors = [], []
        self.ext = False

    # ---- parse (Lean `step`)
    def step(self, tk):
        kw, a = tk[0], tk[1:]
        self.ext = True
        if kw == "mtlx_version":
            if len(a) != 1:
                return self.errors.append("mtlx_version: expected 1 argument")
            self.versions.append(a[0])
        elif kw == "mtlx_surface":
            if len(a) != 2:
                return self.errors.append("mtlx_surface: expected <name> <category>")
            self.surface.append((a[0], a[1]))
        elif kw == "mtlx_node":
            if len(a) != 3:
                return self.errors.append("mtlx_node: expected <name> <category> <type>")
            self.nodes.append(tuple(a))
        elif kw == "mtlx_input":
            msg = "mtlx_input: expected <node>.<input> <type> <value>"
            if len(a) < 2:
                return self.errors.append(msg)
            d = a[0].find(".")
            if len(a) == 3 and is_ref(a[2]):
                if d < 0:
                    return self.errors.append(msg)
                r = a[2][1:]
                ds = r.find(".")
                src, out = (r, None) if ds < 0 else (r[:ds], r[ds + 1:])
                self.conns.append((src, out, a[0][:d], a[0][d + 1:], a[1]))
                return
            vs = a[2:]
            if d < 0 or any(is_ref(v) for v in vs):
                return self.errors.append(msg)
            if a[1] in ("string", "filename"):
                if len(vs) != 1:
                    return self.errors.append(msg)
                value = unescape(vs[0])
            else:
                if not vs:
                    return self.errors.append(msg)
                value = ", ".join(unescape(v) for v in vs)
            self.inputs.append((a[0][:d], a[0][d + 1:], a[1], value))
        elif kw == "mtlx_colorspace":
            msg = "mtlx_colorspace: expected <node>.<input> <colorspace>"
            if len(a) != 2 or "." not in a[0]:
                return self.errors.append(msg)
            d = a[0].find(".")
            self.colorspaces.append((a[0][:d], a[0][d + 1:], a[1]))
        elif kw == "mtlx_include":
            if len(a) != 1:
                return self.errors.append("mtlx_include: expected 1 argument")
            self.includes.append(a[0])

    # ---- check (Lean `check`)
    def node_ty(self, n):
        return next((t for (nm, _, t) in self.nodes if nm == n), None)

    @property
    def surf_name(self):
        return self.surface[0][0] if self.surface else ""

    def has_name(self, n):
        return n == self.surf_name or self.node_ty(n) is not None

    def acyclic(self):
        order = [self.surf_name] + [n for (n, _, _) in self.nodes]
        idx = {}
        for i, n in enumerate(order):
            idx.setdefault(n, i)
        col = [0] * len(order)
        for s0 in range(len(order)):
            if col[s0]:
                continue
            col[s0] = 1
            stack = [(s0, 0)]
            while stack:
                v, e = stack[-1]
                vn = order[v]
                pushed = False
                while e < len(self.conns):
                    src, _, dst, _, _ = self.conns[e]
                    e += 1
                    if dst != vn or src not in idx:
                        continue
                    w = idx[src]
                    if col[w] == 1:
                        return False
                    if col[w] == 0:
                        stack[-1] = (v, e)
                        col[w] = 1
                        stack.append((w, 0))
                        pushed = True
                        break
                if pushed:
                    continue
                col[v] = 2
                stack.pop()
        return True

    @property
    def ok(self):
        if not self.ext or self.errors or len(self.surface) != 1 or len(self.versions) > 1:
            return False
        for v in self.versions:
            p = v.split(".")
            if len(p) != 2 or not _digits(p[0]) or not _digits(p[1]):
                return False
        names = [self.surf_name] + [n for (n, _, _) in self.nodes]
        if not all(valid_name(n) for n in names) or len(set(names)) != len(names):
            return False
        if not valid_name(self.surface[0][1]):
            return False
        if not all(valid_name(c) and t in TYPES for (_, c, t) in self.nodes):
            return False
        bound = set()
        for (n, p, t, v) in self.inputs:
            if not self.has_name(n) or not valid_name(p) or t not in TYPES or not value_ok(t, v):
                return False
            if (n, p) in bound:
                return False
            bound.add((n, p))
        consts = set(bound)
        for (src, out, dst, p, t) in self.conns:
            st = self.node_ty(src)
            if st is None or (out is not None and out != "out"):
                return False
            if not self.has_name(dst) or not valid_name(p) or st != t:
                return False
            if (dst, p) in bound:
                return False
            bound.add((dst, p))
        seen = set()
        for (n, p, cs) in self.colorspaces:
            if (n, p) not in consts or not valid_name(cs) or (n, p) in seen:
                return False
            seen.add((n, p))
        return self.acyclic()

    # ---- canonical writer (tobj_mtlx_to_mtl)
    def to_lines(self):
        def tok(s, esc):
            q = s == "" or s.startswith('"') or any(c in " \t\r" for c in s)
            if esc and s.startswith("@"):
                s = "@" + s
            return f'"{s}"' if q else s
        if not self.ok:
            return []
        out = [f"mtlx_version {tok(v, False)}" for v in self.versions]
        out.append(f"mtlx_surface {self.surface[0][0]} {self.surface[0][1]}")
        out += [f"mtlx_node {n} {c} {t}" for (n, c, t) in self.nodes]
        for (n, p, t, v) in self.inputs:
            if t in ("string", "filename"):
                out.append(f"mtlx_input {n}.{p} {t} {tok(v, True)}")
            else:
                out.append(f"mtlx_input {n}.{p} {t} " + " ".join(tok(x, True) for x in v.split(", ")))
        out += [f"mtlx_colorspace {n}.{p} {tok(cs, False)}" for (n, p, cs) in self.colorspaces]
        for (src, o, dst, p, t) in self.conns:
            out.append(f"mtlx_input {dst}.{p} {t} @{src}" + (f".{o}" if o else ""))
        out += [f"mtlx_include {tok(i, False)}" for i in self.includes]
        return out


def rest_after_keyword(line):
    s = line.strip(" \t")
    i = 0
    while i < len(s) and s[i] not in " \t":
        i += 1
    return s[i:].strip(" \t")


def parse_mtl(text):
    """All materials of a .mtl text, in order (Lean `parseMtl`)."""
    mats = []
    for raw in text.split("\n"):
        line = raw[:-1] if raw.endswith("\r") else raw
        s = line.lstrip(" \t")
        if s.startswith("#"):
            continue
        kw = s.split(" ", 1)[0].split("\t", 1)[0]
        if kw == "newmtl":
            mats.append(Material(rest_after_keyword(line)))
        elif kw in KEYWORDS and mats:
            m = mats[-1]
            try:
                tk = tokenize(line)
            except UnterminatedQuote:
                m.ext = True
                m.errors.append("unterminated quote")
                continue
            m.step(tk)
    return mats


def verdicts(text):
    return "".join(f"mat {m.name} ext={int(m.ext)} ok={int(m.ok)}\n" for m in parse_mtl(text))
