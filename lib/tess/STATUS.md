# Acceptance ledger

Implemented against `../../robust-ngon-remeshing-c11-lean4-prompt.md`.
Release evidence below was collected on 2026-11-14. The deliverable is a bounded
reference library, not a convergence guarantee or full C refinement proof.

## Milestones delivered

1. **Contract/arithmetic:** standalone strict C11 public API; exact binary64 and
   rational input, checked signed limbs/normalized rationals, bounded operations,
   custom allocators, typed failure statuses, diagnostics and independent oracles.
2. **Seed/reference:** exact chart/ring/hole validation, deterministic visibility
   graph/left-witness rotation triangulation, bounded Lawson legalization,
   planar and frozen-graph modes, independent projected/topology/3D validation.
3. **Certified output:** pinned Lean/mathlib, executable bounded V1/V2 decoders,
   full checker soundness, coverage/shared-simplex/graph-homeomorphism proofs,
   exact ordered feature-chain preservation and symmetric Euclidean height bound,
   caller-held frozen-seed/run binding and actual rounded-coordinate artifacts.
4. **Physical-area remeshing:** target-area/count modes, certified fixed count
   target, implicit creases, tagged user seed edges, bounded split/collapse/flip/
   relocation schedule, local objective deltas and full candidate validation,
   exact overlays, transactional rollback, checked binary64 export and reports.
5. **Release/performance:** conservative exact closed AABB acceleration with slow
   differential references; GCC/Clang/sanitizer/proof checks; fuzz/adversarial/
   corruption/fault tests; optional tinyobjloader OBJ loader/writer adapter;
   assembled-asset audit and sidecar verification; examples, CI, measured quality
   and resource reports, research notes and explicit proof-to-code/trust matrix.

The full native matrix passes: GCC Release **22/22** (66.48 seconds, including
Lean and actual OBJ certificate association), Clang Release **20/20** (21.77
seconds). Clang AddressSanitizer/UndefinedBehaviorSanitizer passes **20/20**
(319.64 seconds), with no sanitizer findings. Standalone source-copy, installed-public-header
client and parent opt-in builds pass. The installed example's actual exact and
rounded certificates both pass Lean.

The proof command passes both generation freshness checks, the kernel build and
the compiled dependency audit of **855 Tess declarations**, allowing only
`propext`, `Classical.choice`, `Quot.sound`. No incomplete proof or new axiom is
accepted. The actual translated limb multiply-add has a symbolic MiniC proof;
this does not refine the full C library. See [PROOF_MATRIX.md](docs/PROOF_MATRIX.md).

## Gates and regression evidence

- 15,625 declared small-grid orientation triples, 1,905 Python Fraction exact
  arithmetic/binary64 cases and 11,293 independent incircle/orient3 cases.
- Convex/concave/reversed/collinear/holed/warped fixtures, exact chart ties and
  fallback tie order, overhang rejection, affine transformations, touching/
  nested/outside holes and all shared-simplex pair cases.
- Close disjoint sheets at 2^-1000 survive OBJ loading and assembled audit.
  The tools use a bounded finite-only hosted numeric override; default repository
  loader behavior is unchanged. Nonfinite and malformed tokens reject.
- Reference crossing fixture with equal endpoint heights but maximum diagonal
  crossing error 1/2: zero and 1/3 reject; 1/2 accepts in C and Lean.
- Fixed/subdividable boundaries, tagged user constraints, crease and pin
  preservation, thin channels, holes, small caps, infeasible and stagnant runs.
- Seed/optimizer/input/certificate parser fuzz with fixed seeds, conservative
  broadphase versus exact all-pairs checks, randomized edit sequences and
  allocation-failure tests, including failure after an accepted edit and live
  allocation-count teardown checks.
- Certificate corruption/truncation/oversize/request mismatch, changing both
  frozen/output diagonals, invalid UTF-8, constraint/stable-ID mutations, actual
  OBJ byte/coordinate/face-map changes and coincident unused-vertex provenance
  substitution reject. Negative record lengths reject; file reads are bounded.
- Export fails explicitly when rational pins or rounded geometry cannot preserve
  the contract; metric overflow reports resource failure without corrupting a
  validated mesh. Invalid metric queries likewise preserve the result.

The square returns 128 faces, CV 0, target-band fraction 1, angle p05 45°.
The concave L returns 88 faces against target-count 128, CV 0.263523, target-band
fraction 0.909091, angle p05 45°. Both satisfy the prescribed numeric gates.
The fixed-feature interior fixture performs four centroid splits and reduces
mean squared log area ratio by 76.9%, exceeding its 25% gate. Eight benchmark
fixtures emit sixteen actual exact/rounded artifacts, all accepted by Lean.
Constrained/warped failures to meet quality targets are recorded honestly in
[benchmarks/README.md](benchmarks/README.md) and [results.json](benchmarks/results.json).

The default 100-million-work-unit convex-ring sweep succeeds at 128 vertices
(97,804,448 units) and reports resource exhaustion with no mesh at 160 and 192.
Practical caps depend heavily on geometry and limb sizes; nominal vertex caps
are not throughput promises. See [ALGORITHM.md](docs/ALGORITHM.md).

## Reproduce

```sh
cmake -S lib/tess -B /tmp/tess-release -DCMAKE_BUILD_TYPE=Release \
  -DTESS_BUILD_EXAMPLES=ON -DTESS_TEST_LEAN=ON
cmake --build /tmp/tess-release -j4
ctest --test-dir /tmp/tess-release --output-on-failure
python3 formal/tools/check_tess_proofs.py
python3 lib/tess/benchmarks/run.py --executable /tmp/tess-release/tess_benchmark \
  --checker formal/.lake/build/bin/tesscheck --output /tmp/tess-results.json
python3 lib/tess/benchmarks/resources.py \
  --executable /tmp/tess-release/tess_resource_sweep --output /tmp/tess-resources.json
```

Build the pinned Lean checker first when using `TESS_TEST_LEAN`; its setup and
trust boundary are in [CERTIFICATES.md](docs/CERTIFICATES.md). For a native-only
build omit that option. Repeat with `-DCMAKE_C_COMPILER=clang`. For sanitizers:

```sh
cmake -S lib/tess -B /tmp/tess-san -DCMAKE_C_COMPILER=clang \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_C_FLAGS='-O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer' \
  -DCMAKE_EXE_LINKER_FLAGS='-fsanitize=address,undefined'
cmake --build /tmp/tess-san -j4
ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
  ctest --test-dir /tmp/tess-san --output-on-failure
```

LeakSanitizer cannot run under this environment's tracing/ptrace, so the local
run disables that component. Live allocation counts are independently checked
under injected failures. CI enables LeakSanitizer on an ordinary Ubuntu runner;
remote CI execution is not claimed. The core and new tools compile with strict
C11 and warnings as errors; reused legacy adapter sources retain their existing
build warning policy.

## Deliberate limitations

- No whole-C machine verification, certified floating filters, general interior
  constraint insertion, automatic features, arbitrary multichart surfaces,
  physical-plane CDT or guaranteed shape/quality convergence.
- Geometry-only OBJ output; exact shared-index coplanar merging, no welding.
  Interpatch shared boundaries stay fixed. Native assembled-asset audit is
  mandatory, but has no Lean refinement theorem.
- C/Lean decoder caps differ; a valid large C artifact can exceed Lean budgets.
  Numeric parsing, wire parsing, adapter associations, request custody, native
  execution/compiler and runtime remain explicit trust boundaries.
- Each file publication is atomic, but OBJ and sidecars are not a multi-file
  filesystem transaction. A failed later rename can leave new sidecars without
  replacing the primary OBJ; verification detects mismatched bundles.
- CGAL comparisons were optional and not run: headers are unavailable. Research
  primary sources and design implications are in [RESEARCH.md](docs/RESEARCH.md).


## Pre-push fixes (2026-11-15)

- The benchmark release gate now requires both exact and actual rounded
  certificates for every fixture, and rejects failed binary64 export. Missing
  files cannot silently skip Lean. Regression cases run with ordinary Python
  and `python -O`, and confirm that a complete run invokes all sixteen checks.
- The asset verifier preserves exit 3 from both Lean and the independent asset
  auditor as a resource failure. Explicit dependency exit-1/exit-3 regressions
  check rejection remains distinct from resource exhaustion.
- The release is staged using the explicit `RELEASE_FILES.txt` manifest,
  including inherited formal/C dependencies and excluding unrelated workspace
  files. A clean staged-tree export builds successfully. The updated working
  suite passes 23/23; the staged export is independently tested with the same
  executable Lean checker. All sixteen actual benchmark artifacts pass the
  corrected release gate. No geometry algorithm or proof claim changed.

## Further formalization and validation (2026-11-15)

- `Tess.C.magnitude_refines` now proves the actual translated `tess_mag`
  returns the absolute magnitude of every int64 input, including INT64_MIN,
  without UB and with the entire MiniC state unchanged. It reuses the existing
  loader's signed-decoding lemma. No production C change was needed.
- `Tess.C.limb_madd_digits` proves both low/high output limbs fit uint32 and
  reconstruct the exact multiply-add result. The existing universal helper
  refinement proof remains in place.
- `Tess.onSegment_iff_rational` and `Tess.onSegment_iff_real` establish both
  soundness and completeness of exact segment membership, including zero-length
  segments and endpoints. Closed-intersection soundness remains a separate
  result; intersection completeness is not newly claimed.
- A direct oracle for the actual included arithmetic helper source checks
  4,688 signed magnitudes and 10,657 multiply-add/output-digit cases. A separate
  line-parameter Fraction oracle checks 7,615 C closed-segment contact cases,
  including exhaustive 3x3-grid quadruples, degenerate edges, interval overlaps,
  nearly touching endpoints and extreme dyadic exponents. Both seeds are fixed.
- The complete generation/kernel/axiom audit passes for 878 Tess declarations,
  allowing only the same three standard Lean axioms. The full GCC suite passes
  25/25 (74.73 seconds); Clang passes 23/23 native tests (30.83 seconds).
  Five selected new/existing oracle and gate tests pass under ASan/UBSan
  (66.89 seconds), with local leak detection disabled for the previously
  documented tracing limitation. A standalone source-copy build without the
  repository OBJ adapter passes 20/20 tests (35.27 seconds).
