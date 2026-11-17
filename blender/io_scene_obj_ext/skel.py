"""Skeleton lines of skel-obj.md: a pure-Python port of tobj_skel.c.

`parse_lines(lines, max_joint_id)` checks the `skel_*` lines the way the C
core (and the Lean model formal/Skel) does; `Skel.to_lines()` is the canonical
writer and `dump_obj(text)` the differential-test output (`skel_dump`).
"""
from .subd import drop_cr, is_decimal, parse_int, tokens

KEYWORDS = ("skel_joint", "skel_rest", "skel_lib", "skel_anim")


def valid_name(s):
    """`[A-Za-z_][A-Za-z0-9_]*` (ASCII)"""
    def alpha(c):
        return "a" <= c <= "z" or "A" <= c <= "Z" or c == "_"
    return bool(s) and alpha(s[0]) and all(alpha(c) or "0" <= c <= "9" for c in s[1:])


class Joint:
    def __init__(self, name, parent, bind):
        self.name = name
        self.parent = parent  # index, or -1 for a root
        self.bind = bind      # 16 decimal texts (row-major world matrix) or None
        self.rest = None      # 16 decimal texts (row-major local matrix) or None


class Skel:
    def __init__(self):
        self.joints = []
        self.lib = self.lib_skeleton = self.anim = self.anim_name = None
        self.errors = []
        self.ext = False

    @property
    def ok(self):
        return self.ext and not self.errors

    def index(self, name):
        for i, j in enumerate(self.joints):
            if j.name == name:
                return i
        return -1

    def to_lines(self):
        if not self.ok:
            return []
        out = []
        for j in self.joints:
            parent = "-" if j.parent < 0 else self.joints[j.parent].name
            out.append(" ".join(["skel_joint", j.name, parent] + (j.bind or [])))
        for j in self.joints:
            if j.rest:
                out.append(" ".join(["skel_rest", j.name] + j.rest))
        if self.lib:
            out.append(" ".join(["skel_lib", self.lib] + ([self.lib_skeleton] if self.lib_skeleton else [])))
        if self.anim:
            out.append(" ".join(["skel_anim", self.anim] + ([self.anim_name] if self.anim_name else [])))
        return out


def _step(s, kw, a):
    def matrix(t):
        return list(t) if all(is_decimal(x) for x in t) else None

    if kw == "skel_joint":
        if len(a) not in (2, 18):
            return "skel_joint: expected <name> <parent> [16]"
        if not valid_name(a[0]):
            return "skel_joint: invalid name"
        if s.index(a[0]) >= 0:
            return "skel_joint: repeated name"
        parent = -1
        if a[1] != "-":
            parent = s.index(a[1])
            if parent < 0:
                return "skel_joint: parent not declared earlier"
        bind = None
        if len(a) == 18:
            bind = matrix(a[2:])
            if bind is None:
                return "skel_joint: bad matrix"
        s.joints.append(Joint(a[0], parent, bind))
        return None
    if kw == "skel_rest":
        if len(a) != 17:
            return "skel_rest: expected <name> [16]"
        j = s.index(a[0])
        if j < 0:
            return "skel_rest: joint not declared earlier"
        if s.joints[j].rest:
            return "skel_rest: repeated"
        m = matrix(a[1:])
        if m is None:
            return "skel_rest: bad matrix"
        s.joints[j].rest = m
        return None
    lib = kw == "skel_lib"
    if len(a) not in (1, 2):
        return f"{kw}: expected <path> [<name>]"
    if (s.lib if lib else s.anim) is not None:
        return f"{kw}: repeated"
    name = a[1] if len(a) == 2 else None
    if lib:
        s.lib, s.lib_skeleton = a[0], name
    else:
        s.anim, s.anim_name = a[0], name
    return None


def parse_lines(lines, max_joint_id=-1):
    s = Skel()
    for line in lines:
        tk = tokens(drop_cr(line))
        if not tk or tk[0] not in KEYWORDS:
            continue
        s.ext = True
        e = _step(s, tk[0], tk[1:])
        if e:
            s.errors.append(e)
    if s.ext:
        if any(j.bind is None for j in s.joints) and s.lib is None:
            s.errors.append("joint without bind matrix and no skel_lib")
        if max_joint_id >= 0 and max_joint_id >= len(s.joints):
            s.errors.append("vw: joint id without a skel_joint")
    return s


def dump_obj(text):
    """Same output as tobj_skel_dump_obj / tests/skel_dump."""
    lines, max_id = [], -1
    for line in text.split("\n"):
        tk = tokens(drop_cr(line))
        if tk and tk[0] in KEYWORDS:
            lines.append(line)
        elif tk and tk[0] == "vw":
            for t in tk[2::2]:
                v = parse_int(t)
                if v is not None and v > max_id:
                    max_id = v
    s = parse_lines(lines, max_id)
    if not s.ext:
        return "skel none\n"
    out = f"skel ok={1 if s.ok else 0} joints={len(s.joints)}\n"
    return out + "".join(l + "\n" for l in s.to_lines())
