# LLVM libFuzzer Harness

This directory contains a libFuzzer entry point for the main parser paths:

- `tinyobj::ObjReader::ParseFromString`
- `tinyobj::LoadObj`
- `tinyobj::LoadObjOpt`
- `tinyobj::experimental_stream::LoadObjStreamExperimental`

The harness accepts a single mutated byte stream.

- Bytes before the first `NUL` are treated as OBJ text.
- Bytes after the first `NUL` are treated as MTL text.
- Parser configs are varied from the first few bytes to cover different
  thread counts and parser settings.

For inputs in the shared supported subset (`v`, `vn`, `vt`, `f`, `g`, `o`,
`usemtl`, `s`, comments), the harness cross-checks successful parses between
the legacy and stream loaders. `LoadObjOpt` is still exercised on every input
for stability coverage, but is not the default differential oracle here.

## Build

```bash
cd tests/llvm-fuzz
make
```

## Run

```bash
cd tests/llvm-fuzz
./fuzz_loaders corpus -rss_limit_mb=2048
```

## Seed corpus

`corpus/` contains small valid OBJ seeds so the fuzzer starts from structured
inputs instead of pure random bytes.

## Other applicable fuzzing

- Differential fuzzing against another OBJ parser implementation.
- Sanitizer matrix runs with `address`, `undefined`, `thread`, and `memory`.
- Structure-aware mutation based on OBJ grammar instead of raw-byte mutation.
- File-path fuzzing for mmap/file overloads and material search path handling.
