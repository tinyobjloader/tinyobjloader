#!/usr/bin/env python3
"""Random .obj files with subdivision tags for the Lean/C differential.
usage: gen.py SEED"""
import random
import sys

NAMES = ["crease", "corner", "hole", "interpolateboundary", "facevaryinginterpolateboundary",
         "facevaryingpropagatecorners", "creasemethod", "smoothtriangles", "scheme", "foo"]
STRS = ["catmark", "loop", "bilinear", "normal", "chaikin", "smooth", "x", ""]
DECS = ["1", "2.5", "-1", "-0", "0", ".5", "1.", "1e1", "1E-2", "+3", "10", "inf", "nan", "1e", "x", "."]


def num(r, hi):
    k = r.random()
    if k < 0.7:
        return str(r.randrange(0, hi + 1))
    return r.choice(["-1", "+1", "x", "99999999999999999999", "0", "-0", ""])


def tag(r, nv, nf):
    name = r.choice(NAMES)
    if r.random() < 0.6:  # mostly well-formed shapes
        if name == "crease":
            k = r.randint(1, 3); ni, nf_, ns = 2 * k, r.choice([1, k]), 0
        elif name == "corner":
            k = r.randint(1, 3); ni, nf_, ns = k, r.choice([1, k]), 0
        elif name == "hole":
            ni, nf_, ns = r.randint(1, 3), 0, 0
        elif name in ("creasemethod", "smoothtriangles", "scheme"):
            ni, nf_, ns = 0, 0, 1
        else:
            ni, nf_, ns = 1, 0, 0
    else:
        ni, nf_, ns = r.randint(0, 3), r.randint(0, 2), r.randint(0, 2)
    args = [num(r, max(nv, nf)) for _ in range(ni)]
    args += [r.choice(DECS) for _ in range(nf_)]
    args += [r.choice(STRS) or "y" for _ in range(ns)]
    if r.random() < 0.1 and args:
        args.pop()
    cnt = f"{ni}/{nf_}/{ns}"
    if r.random() < 0.05:
        cnt = r.choice(["1/1", "a/0/0", "9000/0/0", "1/0/0/0", "01/0/0", "//"])
    sep = r.choice([" ", "\t", "  "])
    line = sep.join(["t", name, cnt] + args)
    if r.random() < 0.05:
        line = r.choice(["t", "t crease", "  t\tcorner 1/1/0 0 1  "])
    return line


def main():
    r = random.Random(int(sys.argv[1]))
    out, nv = [], 0
    for _ in range(r.randint(1, 4)):
        if r.random() < 0.8:
            out.append(r.choice(["o", "g"]) + " m")
        for _ in range(r.randint(0, 6)):
            out.append("v 0 0 0"); nv += 1
        nf = 0
        for _ in range(r.randint(0, 5)):
            if nv == 0:
                break
            k = r.choice([3, 3, 4, 4, 5, 2])
            vs = []
            for _ in range(k):
                i = r.randrange(nv)
                vs.append(str(i + 1) if r.random() < 0.8 else str(i - nv))
            if r.random() < 0.05:
                vs[0] = "0"
            vs = [v + r.choice(["", "/1", "//1", "/1/1"]) for v in vs]
            out.append("f " + " ".join(vs)); nf += 1
        for _ in range(r.randint(0, 6)):
            out.append(tag(r, nv, nf))
    text = "\n".join(l + ("\r" if r.random() < 0.05 else "") for l in out)
    sys.stdout.write(text + ("\n" if r.random() < 0.8 else ""))


main()
