#!/usr/bin/env python3
"""Random MaterialX-in-MTL generator for the Lean-vs-C differential (tools/diff.sh)."""
import random, sys

NAMES = ["s", "a", "b", "c", "tex", "n_1", "1x", "", "a.b", "_u"]
CATS = ["standard_surface", "open_pbr_surface", "image", "multiply", "add", "bad-cat", "UsdPreviewSurface"]
TYS = ["float", "color3", "vector2", "integer", "boolean", "string", "filename", "floatarray",
       "color3array", "matrix33", "surfaceshader", "colour3"]
VALS = ["0.5", "1", "-2", "1e3", ".5", "5.", "1.2.3", "x", "true", "false", "1,2", "\"a b\"",
        "\"un", "tex.png", "1,", "+3", "e5", "0x1"]
PORTS = ["base", "base_color", "in1", "in2", "file", "1p", "out"]

def ep(r, dot=True):
    n = r.choice(NAMES)
    if dot and r.random() < 0.9:
        return n + "." + r.choice(PORTS)
    return n

def line(r):
    k = r.randrange(12)
    if k == 0: return f"newmtl {r.choice(['m', 'm 2', 'Mat.001', 'ü', ''])}"
    if k == 1: return f"mtlx_version {r.choice(['1.39', '1.38', '1', '1.x', '1.3.9'])}"
    if k in (2, 3): return f"mtlx_surface {r.choice(NAMES)} {r.choice(CATS)}" + (" extra" if r.random() < 0.05 else "")
    if k in (4, 5): return f"mtlx_node {r.choice(NAMES)} {r.choice(CATS)} {r.choice(TYS)}"
    if k in (6, 7):
        return f"mtlx_input {ep(r)} {r.choice(TYS)} " + " ".join(r.choice(VALS) for _ in range(r.randrange(5)))
    if k in (8, 9): return f"mtlx_input {ep(r)} {r.choice(TYS[:4])} @{ep(r, r.random() < 0.3)}"
    if k == 11 and r.random() < 0.5: return f"mtlx_colorspace {ep(r)} {r.choice(['srgb_texture', 'lin_rec709', 'bad-cs'])}"
    if k == 10: return f"mtlx_include {r.choice(['lib.mtlx', '\"a b.mtlx\"'])}"
    return r.choice(["# c", "Kd 1 1 1", "  \tmtlx_surface s standard_surface  ", "", "mtlx_input a.b float @", "mtlx_input a.b string @@x", "mtlx_input a"])

def main():
    seed = int(sys.argv[1]); r = random.Random(seed)
    out = []
    for _ in range(r.randrange(1, 4)):
        out.append(f"newmtl m{r.randrange(3)}")
        out.append(f"mtlx_surface s {r.choice(CATS[:2])}")
        for _ in range(r.randrange(2, 5)):
            out.append(f"mtlx_node {r.choice(NAMES[1:5])} {r.choice(CATS)} {r.choice(TYS[:3])}")
        if r.random() < 0.5:
            out.append("mtlx_input s.base_color color3 1 1 1")
            out.append(f"mtlx_colorspace s.base_color {r.choice(['srgb_texture', 'lin_rec709'])}")
        out.extend(line(r) for _ in range(r.randrange(0, 14)))
    sep = "\r\n" if r.random() < 0.1 else "\n"
    sys.stdout.write(sep.join(out) + (sep if r.random() < 0.8 else ""))

main()
