# Acceptance ledger

Implemented against `../../robust-ngon-remeshing-c11-lean4-prompt.md`.
Release evidence below was collected on 2026-11-14. The deliverable is a bounded
reference library, not a convergence guarantee or full C refinement proof.

**Current authoritative proof-audit count: 3770 Tess declarations** (re-run

Sanitizer note: the full Clang ASan/UBSan suite (leak detection on) passes 25/25 after fixing a pre-existing
leak in `domain_valid` (edge tangents were dropped by `m->ne = 0` when the domain check ran more than once,
e.g. across chart-axis attempts).
2026-11-16 after `C/I64Import`; standard axioms only). `C/I64Import` refines the pure
kernels (`i64_limb_count`, `i64_fill`) factored out of `zi_i64` (LimbGen ids 8, 9; behavior
unchanged, 28/28 tests pass); the written limbs denote the int64 magnitude and the sign field is ±1. Declaration counts quoted in the dated
sections below are historical snapshots.

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

## Closed-intersection completeness and direct executable validation (2026-11-15)

- `Tess.closedIntersection_iff_real` and `closedIntersection_iff_rational`
  characterize true results by real and rational common segment points.
  `closedIntersection_false_iff` proves false means real disjointness. The
  completeness proof covers point segments, endpoints and collinear intervals
  without general-position assumptions. Rational witness soundness is exposed
  separately as `closedIntersection_rational`.
- A bounded `tesspredicates` executable evaluates the actual Lean orientation,
  corrected incircle, membership and intersection definitions. The C/Lean/
  Fraction suite passes 16,036 shared exact-dyadic cases. Independent Python
  constructions use homogeneous Gaussian determinants and line parameters.
- The new fixture parser passes malformed, zero-denominator, UTF-8, NUL,
  missing-field, usage, count/line/digit/byte-limit tests and 64 deterministic
  mutations. Accepted mutations are checked against Fraction. Newline limits
  are checked before splitting records. This validation protocol does not
  replace certificates or claim a proved parser/compiler refinement.
- A frozen extreme mixed-exponent incircle fixture returns the expected default
  C resource status with no sign; Lean and Fraction agree on its exact result.
  Error paths in the C test probe now release the mesh before returning, with
  byte-accounting teardown checks. A native-only resource regression also runs
  in the sanitizer CI job without requiring Lean.
- Complete proof/generation/axiom audit passes: 905 Tess declarations, standard
  allowlist only. GCC passes 27/27 tests (84.19 seconds), Clang 24/24 (30.81
  seconds). A standalone source-copy build passes 21/21 (35.25 seconds).
  The full 16,036-case direct workload, frozen C resource error and
  parser campaigns also pass with the C executable under ASan/UBSan; local leak
  detection remains disabled for the documented tracing limitation.
- `TESS_TEST_LEAN` requires the two executable targets `tesscheck` and
  `tesspredicates`; build commands and CI now build both. The OBJ/geometry core
  and artifact-checker definitions are unchanged. See
  [PREDICATE_VALIDATION.md](docs/PREDICATE_VALIDATION.md) for exact conventions,
  protocol limits, trust boundary and reproduction commands.

## Indexed segment-conflict semantics and shared-ID validation (2026-11-15)

- The exact computational `segmentConflict` definition now lives in the light
  `formal/Tess/SegmentConflict.lean` module so executable validation can call
  the same code as the checker. `Check.lean` uses that module; the artifact
  checker behavior is unchanged.
- `formal/Tess/IndexedConflict.lean` proves that an indexed conflict is a real
  closed geometric intersection and that ordinary closed intersection is
  equivalent to indexed conflict for valid indices, nondegenerate projected
  edges and disjoint edge endpoint-ID sets. Identical unordered indexed edges
  are explicitly expected shared simplices. For edges sharing only `a=c`, the
  result characterizes precisely the unexpected endpoint contacts, including
  collinear overlap beyond the common indexed vertex; proper crossing is
  impossible there. These are Lean executable-specification proofs, not a C
  refinement.
- `tesspredicates` and the C probe now support `indexedsegments`, with binary64
  coordinates plus four vertex IDs for C and exact rationals plus IDs for Lean.
  Non-1024 IDs are rejected, repeated IDs must carry equal coordinates, and the
  Lean fixture rejects inconsistent shared-ID fixtures. The Python oracle models
  exact IDs, line parameters and interval overlap.
- The direct comparison now covers **19,982** C/Lean/Fraction cases: ordinary
  disjoint-overlap checks, every shared endpoint position, identical and reversed
  indexed edges, larger IDs, collinear/degenerate data and mixed dyadic exponents.
  Accepted Lean parser mutations are still checked against Fraction and include
  inconsistent repeated-ID fixtures.
- The complete regeneration/kernel/axiom audit passes for **971** Tess declarations
  with only `propext`, `Classical.choice` and `Quot.sound` allowed. GCC Release
  passes 27/27 tests (84.95 seconds); Clang Release passes 27/27 tests (77.55
  seconds). The full 19,982-case workload passes with the C probe under
  ASan/UBSan, with local leak detection disabled for the documented tracing
  limitation. The frozen resource-exhaustion fixture and parser campaign also pass.

## Exact 3D orientation and plane-value bridge (2026-11-15)

- `formal/Tess/Orient3.lean` defines the actual exact determinant in the same
  row order as `tg_orient3` (`a-d`, `b-d`, `c-d`) without pulling in proof
  dependencies. `Tess.Orient3Bridge` proves its cast to the real scalar triple
  product, the zero/coplanarity equivalence (linear dependence, with no
  noncollinearity hypothesis), and exact equality with the checker's
  `planeValue` and plane-value coplanarity check.
- `tesspredicates` now supports `orient3` as twelve 3D coordinates. C receives
  four explicit vertices through the same `tg_orient3` row order; Lean calls the
  exact executable determinant; Python uses an independent homogeneous Gaussian
  determinant over exact Fractions.
- The direct suite now includes 512 3D cases (128 low-coordinate grid, 256
  bounded dyadic-exponent random and 128 axis-dominant extreme-exponent cases).
  These are sign comparisons under C's default work budget, not a C resource or
  allocator refinement. The proof claims remain statements about the executable
  Lean specification, not the C implementation.
- The regeneration/kernel/axiom audit passes for **971** declarations with the
  same three-standard-axiom allowlist. GCC and Clang Release pass 27/27 tests
  (84.95 and 77.55 seconds). The full **19,982-case** workload passes under
  ASan/UBSan; local leak detection remains disabled for the documented tracing
  limitation.


## Exact strict 3D plane cuts (2026-11-15)

- The exact computational `planeValue` determinant now lives in lightweight
  `formal/Tess/Plane.lean`, shared by the checker and future executable probes.
  `Check.lean` and the certificate artifact definitions are unchanged.
- `formal/Tess/PlaneCutBridge.lean` proves affine interpolation of `planeValue`
  and that the strict opposite-sign formula used by the 3D audit yields an exact
  rational point on the segment, on the supporting plane, and coplanar with the
  face vertices. Coplanar and endpoint-touching cases are intentionally not reclassified as strict cuts.
- `formal/Tess/TriangleContainsBridge.lean` proves the no-mixed-sign 2D
  containment test used by the auditor projection: for nonzero projected face
  orientation it is the closed triangle in either orientation, with the correct
  reversed edge order when the face is clockwise. This covers both face
  orientations without a nondegeneracy-free claim. `Projection.containsProject`
  instantiates that theorem for the auditor's own 3D projection axes and proves
  the real closed-triangle characterization in both orientations.
- These theorems connect the executable rational cut arithmetic to the 3D
  orientation/coplanarity bridge. They do not prove the full C auditor, native
  3D triangle containment or allocator/resource behavior.


## Exact noncoplanar triangle audits (2026-11-15)

- `formal/Tess/TriangleContact.lean` gives the exact noncoplanar 3D
  triangle-contact predicate built from the proved plane-cut and projected
  containment definitions. The first projection axis is selected explicitly and
  degenerate faces are rejected. The function is not the indexed shared-simplex
  path.
- `tesspredicates` and the C probe now support `tricontact` with six 3D points.
  C calls the native `tg_audit3` diagnostic checker and reports audit acceptance;
  Lean evaluates the exact executable predicate; Python uses an exact mixed-plane
  determinant and projected containment oracle. 64 nondegenerate noncoplanar
  pairs cover disjoint and contacting cases.
- These are bounded direct comparisons of exact executable paths, not a C
  refinement theorem for `tg_audit3`, nor coplanar or shared-index validation.

## Strict plane cuts, projected containment and diagnostic coplanar audits (2026-11-15)

- The strict-crossing branch of the 3D auditor is now a shared static
  `cut_from_plane_values` in `audit.c`, reused by `edges_against` and by the
  new diagnostic export `tg_plane_cut` (declared in `geometry.h`).
  `tg_projected_contains` exports the projected-containment half of the
  auditor for the probe. The production crossing path is unchanged in behavior;
  it is now exercised directly.
- `tesspredicates` gains `planecut` (face a b c plus edge endpoints x y as
  fifteen rationals; prints `1` with three exact cut rationals or `0`) and
  `contains2` (two 2D points; orientation-independent closed-triangle answer).
  The C probe answers `planecut` with exact rational cut coordinates encoded as
  `0x…/0x…` tokens and `contains2` with 0/1. Python parses both encodings into
  exact Fractions and checks the cut lies on the segment and the face plane.
- A separate C-only `triaudit` diagnostic mode covers the coplanar and
  shared-index two-face paths: coplanar containment on the face's own
  projection axis, indexed shared-simplex allowance (vertex equality and
  on-segment plus collinearity for two shared IDs), projected segment conflict
  with the indexed exception, and the identical-triangle rejection. The Lean
  fixture rejects `triaudit` explicitly; the differential compares C against an
  independently written exact Fraction replication of the auditor, including
  six hand-verified fixtures. This is bounded differential evidence, not a C
  auditor refinement proof.
- The direct differential now covers **21,923** C/Lean/Fraction predicate
  comparisons. It feeds each probe in 19,000-record chunks instead of raising
  Lean's per-invocation fixture cap. Parser campaigns cover truncations of the
  new records; 256 deterministic mutations are checked against Fraction.
- `predicate_resources.py` additionally freezes two new default-budget
  exhaustion fixtures: a mixed-exponent orient3 case (Lean sign −1) and a
  mixed-exponent tricontact case (Lean returns 1, no contact). The C probe
  deterministically reports library status 3 with no sign. Both were found by
  seeded random search over exact dyadics and are replayed exactly.
- The regeneration/kernel/axiom audit passes for **976** Tess declarations
  with only `propext`, `Classical.choice` and `Quot.sound` allowed. GCC Release
  and Clang Release pass 27/27 tests (86.65 s and 79.42 s). A standalone
  source-copy build without the repository OBJ adapter passes 21/21. The full
  21,923-case direct workload and `predicate_resources.py` pass with the C
  probe under ASan/UBSan, with local leak detection disabled for the
  documented tracing limitation.

These are executable differential checks. No claim is made that the C 3D
auditor is refined by the Lean specification, and the coplanar/shared-index
path now has the Lean executable specification `PairAudit.pairOk`.

## Big-integer limb-boundary differential (2026-11-16)

- New `tess_zi_oracle` runs the real `zi_add`, `zi_sub`, `zi_mul`, `zi_cmp`
  (via `tests/zi_probe.c`) against Python integers on limb-boundary values
  (2^(32k)±2, all-ones carry chains, single-limb-nonzero borrow ripples,
  zero normalization) plus 3,000 random pairs. A mutation of the borrow
  computation in `zi_add_mixed` is detected. Full GCC suite: 25/25 native
  tests pass without Lean. Differential evidence only; `zi_add`/`zi_mul`/`norm`
  remain unproved in Lean.

## Integer semantics of limb models (2026-11-16)

- `Tess.C.ZiValue` proves, with no new axioms, that the limb models behind the
  translated loops denote integer arithmetic: `ziAdd_value` (a+b including
  the overflow limb), `ziMixed_value` (a-b and zero final borrow when b ≤ a)
  and `ziMul_value` (a*b over a zero buffer of capacity ≥ |a|+|b|, using the
  fact that each row's overflow write replaces a zero). Audit: 1367 declarations.
  Open: composing with allocation, `norm`, sign dispatch and `move`.
- `Tess.C.ZiOrder` adds the order/sign layer: `acmp` outcomes imply the
  denoted-integer order (for normalized operands), `norm` trimming preserves
  value and normalizes, and `ziAdd_signed`/`ziMixed_signed` give the signed sum
  for the two `zi_add` branches. Audit: 1388 declarations.
- `Tess.C.ZiModel` assembles functional models of `zi_add`/`zi_sub`/`zi_mul`
  from the proved loop models and proves they denote signed integer
  addition/subtraction/multiplication with well-formed results (no sorry).
  Audit: 1442 declarations. Remaining gap to the C: allocation/budget/`move`
  and whole-function MiniC refinement.
- `Tess.C.QrModel` proves the rational layer models: Euclid loop = gcd,
  `reduce` canonical form and value preservation, `qr_add/sub/mul` denote
  rational arithmetic (the equal-denominator shortcut agrees with the general
  path). Audit: 1469 declarations. `zi_divrem` remains unproved.
- `Tess.C.DivModel` proves both `zi_divrem` paths compute floor division
  (radix-2^32 and binary compare/subtract), the bit-extraction identity and the
  signed truncated-division law. Audit: 1510 declarations.

Verification at commit "Prove zi_divrem long-division models" (2026-11-16): proof
audit 1510 declarations; GCC Release with Lean 28/28; Clang Release 25/25;
ASan/UBSan subset (zi/exact/arithmetic/predicate-resource/audit/resource) passes
with local leak detection disabled.
- `Tess.C.PredModel` ties the rational models to the Lean predicate
  specifications: `tg_orient_q` sign = sign of `Tess.orient`; `det3` equals
  `incircleDet`/`orient3`; incircle sign product ⇔ `illegalDelaunay`. `ZiM.WF`
  gained the `limbs = [] → sign = 0` field. Audit: 1539 declarations.
- `Tess.C.ShiftModel` proves the `shift` limb carry chain denotes `a*2^bits`;
  `QrModel.qrDoubleM_spec` proves `qr_double` returns the canonical exact value
  of a finite binary64 pattern. Audit: 1569 declarations.
- `Tess.C.ZiCmp` proves `acmp`/`zi_cmp` models equal the order of the denoted
  integers. Audit: 1636 declarations.

## Auditor pair specification and rational compare/divide (2026-11-16)

- `Tess.PairAudit.pairOk` is a Lean executable specification of the C auditor's
  pair decision (coplanar branch, `allowed`, `edges_against`). `tesspredicates`
  now evaluates `triaudit`, so the differential compares C, Lean and Fraction on
  all 201 pairs (21,923 total comparisons pass). `pairOk_noncoplanar_disjoint`
  proves it equals the negation of `noncoplanarTrianglesConflict` for
  noncoplanar faces without shared vertex IDs.
- `PredModel` gained `qrDivM_spec` and `qrCmpM_spec` (cmp = sign of the exact
  difference). Audit: 1675 declarations; GCC+Lean predicate/segment tests pass.
- `PairAuditAllowed.allowed_sound` proves the shared-simplex exception admits only
  shared vertices and exact rational points of the shared edge. Audit: 1682.
- `PairAuditCoplanar.coplanar_disjoint_accepted`: an accepted coplanar pair without
  shared IDs has no vertex inside the other projected triangle and no closed edge
  intersections. Audit: 1690.

## Targeted mutation check (2026-11-16)

- Twelve hand-written mutants of `exact.c`, `predicates.c`, `geometry.c` and
  `audit.c` (carry/borrow, sign handling, compare direction, subtract guard,
  incircle orientation correction, coplanar cross check, containment sign
  accumulation, identical-triangle test) were run against the `zi`, exact,
  predicate and C/Lean/Fraction differential oracles. Eleven were killed
  (one of them only after a test fix). The `zi_i64` mutant, ignoring the sign of negative inputs, exposed an
  untested path and survived initially; `tess_zi_oracle` now imports 76 int64 values (including
  `INT64_MIN`) and kills it. The remaining survivor (`z*w <= 0` in
  `tg_segments`) is an equivalent mutant: strict straddling plus an endpoint of
  one segment on the other's line already returns through the later branch.
- `Tess.TriangleMeet` proves in the real plane that a segment from a triangle point to an
  outside point exits through an edge, hence two meeting triangles with no vertex of one in
  the other have meeting edges. `PairAuditDisjoint.coplanar_disjoint_triangles_disjoint`
  concludes that an accepted coplanar pair without shared IDs has disjoint projected closed
  triangles (hypotheses: valid indices, nondegenerate projected edges and second face).
  Audit: 1715 declarations.
- `Tess.C.ZiCmpC.zi_cmp_refines`: the translated `zi_cmp` (including its call to `acmp`) is
  proved equal to the model `ziCmpM`, hence to the true integer order by `ziCmpM_spec`.
  `acmp_exs`/`acmp_exs_unequal` were generalized over the struct signs and the read-only flag
  (expression calls run read-only). `LimbGen` now also contains `zi_cmp` (function id 5).
  Audit: 1732 declarations.
- `BoxSeparation.boxes_separate_disjoint`: a strict gap between recorded AABB extrema excludes any common point of the two closed triangles, justifying the broadphase skip.
- `C/SegModel.tgSegmentsM_eq`: the `tg_segments` model equals `segmentConflict` (audit count in the header is kept current).
- The mutation campaign is reproducible: `python3 lib/tess/tools/mutation_check.py --lean
  formal/.lake/build/bin/tesspredicates` applies the twenty mutants to a scratch copy and reports
  nineteen killed plus the one documented equivalent mutant (not part of default ctest). Five mutants were
  added for the factored `shift_fill`/`div_single_fill` kernels and the binary division path.
- `NoncoplanarComplete.noncoplanar_gp_disjoint`: in general position, `noncoplanarTrianglesConflict = false`
  implies no common rational point of the two closed triangles (Case I: exit lemma in the plane of
  `A` for a point of `B ∩ plane A` outside `A`; Case II: strict cut of a `B` edge). Combined with
  `pairOk_noncoplanar_disjoint` this gives `PairAuditNoncoplanar.accepted_noncoplanar_gp_disjoint`.
  New supporting files: `TriangleExitQ` (rational exit lemma), `PlaneTransfer` (Hull3 ↔ projected
  `Tri2` on a plane, plane injectivity via coordinate rotation). Audit: 1816 declarations.
- `noncoplanar_edgefree_disjoint` strengthens the above: vertices of one face may lie on the other
  face's plane (flagged through `vertex_flag`), as long as the faces are noncoplanar and no edge of
  the first face lies in the second's plane; `accepted_noncoplanar_edgefree_disjoint` is the pair-level
  corollary.
- `conflict_swap` (the exact contact predicate is symmetric for noncoplanar faces) and
  `noncoplanar_disjoint_either` / `accepted_noncoplanar_either_disjoint`: the disjointness result holds as
  soon as either face has no edge in the other's plane. Audit: 1825 declarations.
- `SharedEdge.shared_edge_intersection`: noncoplanar triangles sharing an edge meet exactly in that edge.
- `InPlane`/`PlaneLine`: the last degenerate configuration (an edge of each triangle in the other's
  plane) is closed by a collinearity lemma for points on two nonparallel planes and a 1D interval
  argument. `noncoplanar_disjoint_complete` and `PairAuditNoncoplanarFull.accepted_noncoplanar_disjoint`
  now need no general-position hypothesis: an accepted noncoplanar pair without shared IDs has
  disjoint closed triangles (rational points).
- `SharedVertex`/`PairAuditShared.accepted_shared_vertex_only`: for noncoplanar faces sharing exactly one
  vertex, an accepted pair has no common point other than the shared vertex. `edgesAgainst_contact`
  extracts the auditor's per-edge acceptance condition in `allowed` form. Audit: 1852 declarations.
- `PairAuditCoplanarShared.accepted_coplanar_shared_vertex_only`: coplanar faces sharing one vertex meet only
  there when accepted; supported by `coplanar_contact_false` (an endpoint-free chord of a face forces an
  edge/edge conflict) and `segmentConflict_symm`. Audit: 1872 declarations.

Verification at HEAD of this session (2026-11-16): proof audit 1872 declarations; GCC Release with Lean
28/28; Clang Release 25/25; Clang ASan/UBSan full native suite 25/25 (209 s, local leak detection
disabled for the documented tracing limitation).
- `CoplanarSharedEdge.accepted_coplanar_shared_edge`: coplanar faces sharing an edge meet only in that edge when
  accepted (either traversal direction), via `shared_edge_exit` and the ID-level reduction
  `coplanar_shared_edge_of_conflicts`. With this the auditor spec's pairwise soundness covers every
  configuration of 0, 1 or 2 shared vertex IDs for both coplanar and noncoplanar faces. Audit: 1902 declarations.
- `C/TrimLen.trim_len_refines`: the length scan of `norm` was factored into the pure `trim_len` (behavior
  unchanged; GCC+Lean 28/28 still pass) and its translated loop is refined against `trimL`.
  `LimbGen` gained function id 6. Audit: 1932 declarations.
- `PairAuditComplete`: rejected pairs without shared IDs always have a genuine common point
  (`pairOk_false_noncoplanar_common`, `pairOk_false_coplanar_common`), giving
  `pairOk_iff_disjoint_noncoplanar`: for noncoplanar faces the exact decision equals disjointness.
- `pairOk_of_shared_edge_noncoplanar`: no false rejection for noncoplanar faces sharing an edge (their common
  points are on the edge and `allowed_of_edge_point` admits them); `edgesAgainst_false_contact'` extracts the
  non-allowed contact point of a rejected edge check.
- `pairOk_iff_shared_vertex_noncoplanar`: for noncoplanar faces with one shared vertex the auditor accepts exactly when the triangles meet only there.
- `C/DblDecode.dbl_decode_refines`: the binary64 field decode of `qr_double` was factored into the pure helper
  `dbl_decode` (behavior unchanged; 28/28 tests pass) and refined in MiniC against `dblMant`/`dblExp`.
  `LimbGen` gained function id 7. Audit: 1990 declarations.
