# Experimental code for .obj loader.

* Multi-threaded optimized parser : tinyobj_loader_opt.h
* Streaming experimental parser : stream/stream_obj_loader.h

## Requirements

* C++-11 compiler

## How to build

```
$ premak5 gmake
```

## Compile options

* zstd compressed .obj support. `--with-zstd` premake option.
* gzip compressed .obj support. `--with-zlib` premake option.

## Notes on AMD GPU + Linux

You may need to link with libdrm(`-ldrm`).

## Licenses

* lfpAlloc : MIT license.
