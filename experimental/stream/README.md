# Experimental Stream OBJ Parser

This directory contains an experimental line-by-line OBJ parser intended to
reduce peak input buffering compared with the whole-buffer optimized parser.

The design is split into two layers:

- `StreamHandler`: callback-style incremental parser interface.
- `LoadObjStreamExperimental(...)`: convenience wrapper that builds
  `tinyobj::attrib_t`, `tinyobj::shape_t`, and `tinyobj::material_t`.
- Ordered multithreaded chunk mode: read bounded batches of lines, parse those
  chunks in parallel, then replay parsed events in original order.

## Goals

- Parse OBJ from `std::istream` without reading the whole file into one buffer.
- Preserve support for relative face indices.
- Allow applications to consume faces incrementally without materializing a
  full mesh.

## Current Scope

Implemented records:

- `v`
- `vn`
- `vt`
- `f`
- `g`
- `o`
- `usemtl`
- `mtllib`
- `s`

Ignored for now:

- `l`
- `p`
- free-form curves/surfaces
- tags and skinning extensions
- advanced vertex color fallback behavior matching the legacy loader exactly

## Notes

This parser is intentionally separate from `LoadObjOpt`.
`LoadObjOpt` is built around random-access whole-buffer processing and
multithreaded partitioning, while this module is focused on low intermediate
buffer usage and incremental consumption.

The current multithreaded design uses a bounded in-flight chunk window rather
than a true LRU chunk cache. That matches OBJ's mostly sequential access
pattern better and keeps ordering/state management simple.
