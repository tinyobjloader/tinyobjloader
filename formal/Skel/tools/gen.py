#!/usr/bin/env python3
"""Random .obj files with skel_* and vw lines for the Lean/C differential.
usage: gen.py SEED"""
import random
import sys

DECS = ["0", "1", "-1", "0.5", ".5", "1.", "1e3", "-2E-1", "+3", "x", "1e", "inf", "nan", "-0"]
NAMES = ["hips", "spine", "head", "arm_L", "_x", "j1", "1bad", "a-b", "", "hips"]


def mat(r):
    return [r.choice(DECS) if r.random() < 0.01 else r.choice(["0", "1", "0.5", "-1", "2.25"])
            for _ in range(16 if r.random() < 0.97 else r.choice([15, 17]))]


def main():
    r = random.Random(int(sys.argv[1]))
    out, names = [], []
    for _ in range(r.randint(0, 10)):
        k = r.random()
        if k < 0.45:
            n = r.choice(NAMES) if r.random() < 0.05 else f"j{len(names)}"
            par = "-" if not names or r.random() < 0.2 else (r.choice(names) if r.random() < 0.97 else "nope")
            line = ["skel_joint", n, par] + (mat(r) if r.random() < 0.9 else [])
            names.append(n)
        elif k < 0.6:
            line = ["skel_rest", (r.choice(names) if r.random() < 0.9 else "nope") if names else "nope"] + mat(r)
        elif k < 0.7:
            line = [r.choice(["skel_lib", "skel_anim"]), r.choice(["rig.fbx", "a.usda"])] + \
                   ([r.choice(["walk", "/Skel"])] if r.random() < 0.5 else []) + \
                   (["extra"] if r.random() < 0.02 else [])
        elif k < 0.95:
            line = ["vw", str(r.randint(0, 9))]
            for _ in range(r.randint(0, 3)):
                line += [str(r.randint(0, max(len(names) - 1, 0))) if r.random() < 0.95 else r.choice([str(len(names) + 1), "-1", "x"]), "0.5"]
        elif r.random() < 0.3:
            line = [r.choice(["skel_joint", "skel_rest", "skel_lib", "v 0 0 0", "# c"])]
        else:
            line = ["v", "0", "0", "0"]
        if line and line[-1] == "":
            line[-1] = "e"
        sep = r.choice([" ", "\t", "  "])
        text = sep.join(t for t in line if t != "")
        if r.random() < 0.05:
            text += "\r"
        out.append(text)
    sys.stdout.write("\n".join(out) + ("\n" if r.random() < 0.8 else ""))


main()
