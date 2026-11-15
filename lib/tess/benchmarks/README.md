# Reproducible engineering benchmarks

The fixture coordinates, target, budgets and seed policy are frozen in
[`tools/benchmark.c`](../tools/benchmark.c). [`results.json`](results.json)
contains the complete before/after statistics, edit and rejection counts,
operation counts, memory, timings and hashes of the actual accepted artifacts.
No threshold was relaxed for constrained fixtures. The release runner requires
successful binary64 export and both exact and rounded certificates for every
fixture. A missing artifact or failed checker is a hard failure.

```sh
cmake -S lib/tess -B /tmp/tess-release -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/tess-release -j4
(cd formal && lake build Tess tesscheck)
python3 lib/tess/benchmarks/run.py --executable /tmp/tess-release/tess_benchmark \
  --checker formal/.lake/build/bin/tesscheck --output /tmp/tess-results.json
python3 lib/tess/benchmarks/resources.py \
  --executable /tmp/tess-release/tess_resource_sweep --output /tmp/tess-resources.json
```

Measured 2026-11-14 on Linux x86_64, GCC 15.2 Release, strict C11, no fast-math.
The C process took 6.96 seconds wall time and 2,528 KiB peak RSS in this run;
Lean checker times are separately recorded per artifact. Timings vary with
machine load. The target-count 128 gates are CV≤0.30, target band≥0.90 and
fifth-percentile minimum angle≥20°. Count specifies the fixed area target,
not a requirement to return exactly 128 faces.

| Fixture | Faces | CV | Fraction in target band | Angle p05 (degrees) | Core peak bytes | Remesh CPU seconds | Result |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| Unit square | 128 | 0 | 1 | 45 | 121782 | 0.841 | targets met |
| Concave L | 88 | 0.263523 | 0.909091 | 45 | 115846 | 2.840 | targets met |
| Interior fixed features | 12 | 0.333333 | 0 | 18.4349 | 17736 | 0.060 | valid, bounded run |
| Warped, exact | 27 | 0.377595 | 0.777778 | 5.78416 | 34036 | 0.597 | valid, bounded run |
| Warped, tolerance 0.5 | 8 | 0 | 0 | 35.2644 | 12938 | 0.026 | valid, bounded run |
| Thin fixed channel | 14 | 0.256756 | 0.285714 | 1.02002 | 20208 | 0.142 | valid, bounded run |
| Hole, fixed boundary | 16 | 0.333333 | 0.5 | 11.3099 | 20968 | 0.117 | valid, bounded run |
| Acute fixed triangle | 1 | 0 | 1 | 0.057296 | 6508 | 0.001 | valid, constraint-limited |

The interior fixture tags all seed interior diagonals and fixes boundaries;
four interior centroid splits reduce mean squared log area ratio from
4.20273565 to 0.97008244, a 76.9% improvement, exceeding the separate 25% gate.
The acute fixture makes no accepted edit and reports constraint-limited targets
unmet. Neither the warped nor constrained fixtures is advertised as satisfying
the square/L quality gate. All eight exact outputs and all eight actual rounded
outputs passed Lean. Their measured maximum reference deviation is zero, even
on the approximate run: authorization to approximate does not require changing
the surface. A separate crossing-diagonal fixture proves acceptance at exactly
1/2 and rejection at 1/3 and zero, so positive-bound behavior is also exercised.

Areas use 3D cross products. Hard comparisons use exact squared quantities;
engineering statistics use long-double intermediates and checked binary64
reports. Quantiles use Type 7 linear interpolation at `(n-1)*p`. Ratios are
against the fixed target, and target-band endpoints are inclusive [0.5,1.5].
Peak core storage is allocator-accounted per result and staging, not process RSS;
RSS includes the complete C process but excludes external Lean subprocesses.

## Practical budget boundary

[`resources.json`](resources.json) records a separate default-budget sweep of
convex planar rings `(i,i²,0)`, chart axis 2, using 100 million operation units.
Eight through 128 vertices succeed; 128 consumes 97,804,448 units. The 160- and
192-vertex rings stop at the cap with `TESS_RESOURCE_LIMIT` and no output mesh.
This is one deterministic fixture family, not a universal size guarantee.
The very small storage figures do not make the exact high-order baseline
suitable for large production meshes. See [ALGORITHM.md](../docs/ALGORITHM.md)
for asymptotic costs and resource scope.

CGAL comparison was not run because CGAL headers are unavailable in this
environment. It is optional and outside the production dependency chain.
[Research notes](../docs/RESEARCH.md) record the comparison semantics and consulted
primary sources; different chart metrics and warped reference surfaces must not
be treated as interchangeable ground truth.
