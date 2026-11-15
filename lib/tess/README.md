# tess

Standalone C11 exact n-gon triangulation and bounded physical-area remeshing.
The core has no mesh-library dependency. The optional OBJ driver reuses the
repository's tinyobjloader double loader and writer. The implementation and
verification acceptance ledger is [STATUS.md](STATUS.md). See the
[algorithm and resource contract](docs/ALGORITHM.md),
[certificate format and trust boundary](docs/CERTIFICATES.md),
[proof-to-code matrix](docs/PROOF_MATRIX.md), and
[measured benchmarks](benchmarks/README.md).

```sh
cmake -S lib/tess -B /tmp/tess-build
cmake --build /tmp/tess-build -j4
ctest --test-dir /tmp/tess-build --output-on-failure
/tmp/tess-build/tess_obj input.obj output.obj
/tmp/tess-build/tess_obj --target-count 128 --subdivide-boundary input.obj output.obj
(cd formal && lake build Tess tesscheck)
/tmp/tess-build/tess_obj --target-count 128 --subdivide-boundary \
  --lean-checker "$PWD/formal/.lake/build/bin/tesscheck" input.obj output.obj
python3 lib/tess/tools/verify_asset.py --source input.obj \
  --request output.obj.tess-request --bundle output.obj.tess --obj output.obj \
  --lean-checker formal/.lake/build/bin/tesscheck --audit-exe /tmp/tess-build/tess_obj_audit
```

`-DTESS_BUILD_OBJ=OFF` builds the core independently. A source copy without the
repository loader defaults to that configuration. The parent repository can
opt in with `-DTINYOBJLOADER_BUILD_TESS=ON`. Only C11 and the platform math library
are required for the core. Python is used for independent oracles; Lean is an
optional build dependency for artifact verification.

The driver loads OBJ without input triangulation. It merges exactly coplanar,
consistently oriented, edge-connected faces sharing source vertex IDs, including
holed patches. Warped faces remain separate deterministic graph patches. No
coordinates are welded. Output is geometry-only: original attributes are
omitted. Interpatch shared edges remain fixed, including when exterior boundary
subdivision is authorized. `--planar` requires exact planarity; `--graph` is the
default. The tools opt into a bounded hosted `strtod` numeric scanner (4,096-character
stack token limit, finite values only). This preserves finite subnormal values
and rejects nonfinite input instead of the default loader's clamping behavior.
The repository loader's default numeric behavior is unchanged. Numeric parsing
is part of the trusted adapter boundary. Count mode derives one area target
from the complete source surface.
`--target-area A` instead supplies a physical area. `--height-tolerance H` allows
an explicit dropped-coordinate error; default zero preserves the frozen PL
reference exactly.

Results own exact rational coordinates, stable vertex/face IDs, oriented
constraints, source IDs, owner IDs, tags and ordered affine chain parameters.
`tess_set_seed_features` accepts tagged existing seed edges and seed vertex pins
before `tess_prepare_remesh`; general constraint insertion is outside this API.
Seed vertices are already pinned. Save a caller-held version-2 request after
prepare, then call `tess_remesh(result,NULL,...)`. Each result supports one run.
See [include/tess.h](include/tess.h) for the complete ownership and status API.

The driver writes the OBJ plus `.tess` and `.tess-request` framed sidecars. Each
patch includes the frozen request, exact output, independently validated actual
binary64 coordinates, global vertex/face maps and statistics. The original OBJ
bytes and actual output bytes are bound in the bundle. Save the request outside
the producer's control when checking untrusted results. The Python verifier
checks the association to the actual OBJ, runs the Lean executable on each
patch and invokes the independent assembled 3D auditor; it is not a formal proof of the OBJ parser or assembly adapter.

An existing destination is replaced only after source, patch, assembled mesh,
checked rounding and writer/reload validation. Temporary files use exclusive
creation; sidecars are published before the primary OBJ. Publication is atomic
per file, not a multi-file filesystem transaction. Exit 0 means success/targets
met; exit 4 means a valid output with targets unmet; exit 2 is usage error.
Other failures return nonzero and do not publish the primary OBJ.

Binary64 inputs denote their exact dyadic values. No epsilon decides topology.
The arithmetic checks layout, sizes, limb growth, allocation, memory and
operation fuel. Budget exhaustion never supplies an invented predicate sign.
Independent results can run concurrently; callers must synchronize access to
the same result. Allocator callbacks must remain valid until destruction.

The baseline uses exact all-pairs tests with conservative closed AABB culling
and dense incidence accounting. It is intended for bounded patches, not large
production meshes. Chart Delaunay legality uses the axis-drop metric. The seed
legality completion getter concerns the seed only; remeshing does not claim CDT
or guaranteed angle/quality convergence. Acute corners, fixed edges, creases and
small budgets can prevent requested targets. Quality metrics use long-double
intermediates, binary64 reports and Type-7 percentiles.

Lean reuses the existing MiniC semantics and c2lean translator. The version-1
checker has a kernel-checked coverage, shared-simplex, graph-homeomorphism and
exact-reference soundness theorem. Version-2 soundness covers subdivided chains, pinned inputs, full caller-held
frozen-seed binding, positive height tolerance and symmetric Euclidean distance.
Symbolic refinement proofs cover the actual translated limb multiply-add
and signed-magnitude helpers, including INT64_MIN. Segment membership is proved
equivalent to rational and real closed-segment membership, including degenerate
segments. This does not make the C geometry library machine-verified. See the
acceptance ledger for the precise completed proof and test scope.

A public-header-only example is [examples/square.c](examples/square.c). Build it
with `-DTESS_BUILD_EXAMPLES=ON`; `tess_square /tmp/square` saves a held request,
exact result and checked rounded result. `cmake --install /tmp/tess-build
--prefix /tmp/tess-install` installs `include/tess.h` and `lib/libtess.a` for a
static build. Link hosted clients with the platform math library. The exact
maximum height deviation is available through `tess_reference_deviation` after
final overlay measurement; report metrics remain approximate engineering values.


The explicit release file set is [RELEASE_FILES.txt](RELEASE_FILES.txt). It includes
the reused formal project and its companion C source/refactors required by the
existing c2lean freshness check. From the repository root, stage only that set:

```sh
git add --pathspec-from-file=lib/tess/RELEASE_FILES.txt
git diff --cached --check
git diff --cached --stat
```

Build caches, generated binaries, private workspace files and unrelated models
are excluded. Review the staged diff before committing.
