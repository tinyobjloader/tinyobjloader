# Experimental code for .obj loader.

* Streaming experimental parser : `stream/stream_obj_loader.h`

## Requirements

* C++-11 compiler

## Streaming parser

`stream/` holds a line-by-line OBJ parser that reduces peak input buffering
compared with the whole-buffer optimized parser: it reads from a
`std::istream` instead of materialising the entire file. See
[stream/README.md](stream/README.md) for its scope and design.

It is consumed by the C++ test suite and the fuzzers:

* `tests/tester.cc`
* `tests/obj-fuzz/obj_fuzz.cc`
* `tests/llvm-fuzz/fuzz_loaders.cc`

Build it through the test harness rather than standalone:

```
cd tests && make
```

The multi-threaded optimized parser that used to live here
(`tinyobj_loader_opt.h`, plus its viewer and `lfpAlloc` dependency) has been
removed; use `LoadObjOpt` / `LoadObjOptTyped` from `tiny_obj_loader.h` instead
(see the "Optimized loader" section of the top-level README).
