#!/usr/bin/env python3
"""Three-way differential test of the verified core:

  real C (compiled)  ==  MiniC semantics of the translated C  ==  Lean spec

Validates the trusted parts of the C-to-Lean pipeline (translator and MiniC
semantics) against the real compiler, and the spec against both.

Usage: python3 formal/tools/cdiff.py [--n N] [--seed S]
"""
import os
import random
import struct
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FORMAL = os.path.join(ROOT, "formal")


def u32(v):
    return struct.pack("<I", v & 0xFFFFFFFF)


def u64(v):
    return struct.pack("<Q", v & 0xFFFFFFFFFFFFFFFF)


def glb(rng, version):
    hdr = 12 if version == 3 else 8
    chunks = b""
    for _ in range(rng.randint(0, 4)):
        ln = rng.choice([0, 1, 3, 4, 5, 8, rng.randint(0, 40)])
        typ = rng.choice([0x4E4F534A, 0x004E4942, 0x12345678])
        payload = bytes(rng.randint(0, 255) for _ in range(ln))
        pad = (-ln) % 4 if rng.random() < 0.8 else rng.randint(0, 3)
        declared = ln if rng.random() < 0.85 else rng.choice([ln + 1, ln + 100, 2**32 - 1, 2**64 - 16])
        head = (u64(declared) if version == 3 else u32(declared)) + u32(typ)
        chunks += head + payload + b"\x20" * pad
    start = 16 if version == 3 else 12
    total = start + len(chunks)
    if rng.random() < 0.1:
        total += rng.choice([-1, 1, 4])
    head = b"glTF" + u32(version) + (u64(total) if version == 3 else u32(total))
    data = head + chunks
    if rng.random() < 0.15 and data:
        data = data[: rng.randint(0, len(data))]
    if rng.random() < 0.05:
        data = bytearray(data)
        if data:
            data[rng.randrange(len(data))] ^= 1 << rng.randrange(8)
        data = bytes(data)
    return data


def cases(rng, n):
    out = []
    fixed = [b"", b"glTF", b"glTF" + u32(3) + b"\0" * 4, b"glTF" + u32(3) + b"\0" * 7,
             b"glTF" + u32(1) + u32(12), b"BAD!" + u32(2) + u32(12)]
    for d in fixed:
        out.append("frame " + d.hex())
    for _ in range(n):
        out.append("frame " + glb(rng, rng.choice([2, 2, 3, 3, 1])).hex())
    edge = [0, 1, 3, 4, 2**32 - 1 - 20, 2**32 - 1 - 19, 2**32 - 4, 2**32, 2**64 - 1, 2**64 - 4,
            2**64 - 32, 2**64 - 29, 2**63]
    for _ in range(n):
        jl = rng.choice(edge + [rng.randint(0, 2**40)])
        bl = rng.choice(edge + [rng.randint(0, 2**40)])
        out.append(f"layout {jl} {bl} {rng.randint(0, 1)}")
    return out


def main():
    n = 300
    seed = 1
    args = sys.argv[1:]
    if "--n" in args:
        n = int(args[args.index("--n") + 1])
    if "--seed" in args:
        seed = int(args[args.index("--seed") + 1])
    rng = random.Random(seed)
    lines = cases(rng, n)
    inp = "\n".join(lines) + "\n"
    with tempfile.TemporaryDirectory() as d:
        exe = os.path.join(d, "cdiff_c")
        subprocess.check_call([os.environ.get("CC", "cc"), "-std=c11", "-O1", "-w",
                               "-fsanitize=address,undefined", "-fno-sanitize-recover=all",
                               "-o", exe, os.path.join(FORMAL, "tools", "cdiff_c.c")])
        c_out = subprocess.run([exe], input=inp.encode(), capture_output=True, check=True).stdout.decode().splitlines()
    subprocess.check_call(["lake", "build", "cdiff"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    lean_out = subprocess.run([os.path.join(FORMAL, ".lake", "build", "bin", "cdiff")], input=inp.encode(),
                              capture_output=True, check=True).stdout.decode().splitlines()
    bad = 0
    for line, c, l in zip(lines, c_out, lean_out):
        minic, spec = [x.strip() for x in l.split("|")]
        if not (c == minic == spec):
            bad += 1
            if bad <= 10:
                print(f"MISMATCH {line[:120]}\n  C:     {c}\n  MiniC: {minic}\n  spec:  {spec}")
    if len(c_out) != len(lines) or len(lean_out) != len(lines):
        print("output length mismatch")
        return 1
    print(f"cdiff: {len(lines)} cases, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
