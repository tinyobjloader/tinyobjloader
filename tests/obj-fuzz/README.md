# Structured OBJ Fuzzer

This directory contains a standalone randomized OBJ generator and verifier.

The goal is different from libFuzzer:

- generate reproducible, somewhat coherent OBJ text
- exercise faces, groups, objects, smoothing groups, vertex colors, weights,
  texcoord `w`, comments, and relative indices
- compare successful parses across `LoadObj`, `ObjReader`,
  `LoadObjOpt`, and the experimental stream loader

The runner is deterministic for a given seed and prints the exact failing OBJ
text when a mismatch is found.

By default the differential checks are:

- `LoadObj` vs `ObjReader`
- `LoadObj` vs experimental stream loader

`LoadObjOpt` is always executed for stability coverage, and can be promoted to a
strict differential target with `--strict-opt`.

## Build

```bash
cd tests/obj-fuzz
make
```

## Run

```bash
cd tests/obj-fuzz
./obj_fuzz --iterations 5000 --seed 12345
./obj_fuzz --iterations 1000 --seed 12345 --strict-opt
```

Optional material coverage:

```bash
./obj_fuzz --iterations 2000 --seed 99 --allow-mtllib
```

`--allow-mtllib` keeps the run useful for the legacy, `ObjReader`, and stream
paths, but the standalone cross-check against `LoadObjOpt` is skipped because
the optimized in-memory API does not accept a custom material reader.
