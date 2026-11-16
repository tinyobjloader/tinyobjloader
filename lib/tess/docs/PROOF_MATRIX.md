# Proof, implementation and evidence matrix

The public mathematical release claims are `Tess.check_sound` and
`Tess.check2_sound`. Their exact conclusions are in
[`Validity.lean`](../../../formal/Tess/Validity.lean) and
[`Validity2.lean`](../../../formal/Tess/Validity2.lean). Both have the form
`check request cert = true → Valid request cert`. They require checker
acceptance, not hypotheses assuming output domain coverage or embedding.
The domain is the closure/regularization of the positive oriented ring-winding
region after the recorded chart transform. Validated simple outer/hole rings
supply that prescribed domain. Quality statistics are separate engineering claims.

| Claim and assumptions | Lean definitions/proofs | C counterpart | Frozen/regression evidence |
| --- | --- | --- | --- |
| Exact determinant definitions, orientation soundness, sound and complete segment membership, sound/complete closed intersection and indexed segment-conflict semantics, including endpoints/collinearity and shared indexed simplices | `Predicates`, `PredicateGeometry.orient_realPoint2`, `inside_iff_closedTriangle`, `SegmentConflict`, `SegmentSoundness.onSegment_iff_rational`, `onSegment_iff_real`, `IntersectionCompleteness.closedIntersection_iff_real`, `closedIntersection_iff_rational`, `closedIntersection_false_iff`, `IndexedConflict.segmentConflict_closedIntersection`, `segmentConflict_iff_closedIntersection`, `segmentConflict_same_unordered`, `segmentConflict_shared_head` | `geometry.c`, `predicates.c`, `exact.c` | `test_predicate`, 15,625 integer grid triples; 1,905 Fraction cases; 11,293 incircle/orient3 cases; 7,615 independent line-parameter contact cases; 21,923 C/Lean/Fraction predicate comparisons including disjoint/shared indexed IDs, plane cuts, projected containment and exact 3D orientation; frozen resource exhaustion; adversarial ring tests |
| Exact executable 3D orientation, real determinant cast and determinant-coplanarity/planeValue bridge | `Orient3.orient3`, `Orient3Bridge.orient3_cast`, `orient3_zero_iff_coplanar`, `planeValue_eq_orient3`, `planeValue_zero_iff_coplanar` | `predicates.c`, `tg_orient3` | 512 low-coordinate/grid/bounded/extreme axis-dominant C/Lean/Fraction fixtures, with the exact row order of `tg_orient3` |
| Exact strict 3D plane cuts: rational interpolation lies on the segment and exactly on the supporting plane when endpoint plane values are strict opposites; touching/coplanar branches are outside this branch | `Plane.planeCut`, `planeValue_segment3Point`, `PlaneCutBridge.planeCut_spec`, `planeCut_spec_coplanar`, `planeCut_none_of_not_opposite`, `planeValue_eq_orient3` | the shared static `cut_from_plane_values` in `audit.c`, reused by `edges_against`; diagnostic `tg_plane_cut` wrapper used by the probe | 288 C/Lean/Fraction `planecut` fixtures (z-normal grids, reversed orientation, bounded random 3D dyadics); the production strict-cut branch is the same code path, not a test reimplementation; full C auditor refinement remains open |
| Exact noncoplanar triangle-contact executable and edge-contact soundness: true direct contacts produce rational points of the source edge, on the target plane, with nondegenerate projected containment; indexed shared-simplex exception deliberately excluded | `TriangleContact.pointPlaneValue`, `firstProjectionAxis`, `containsNondegenerate`, `noncoplanarTrianglesConflict`, `TriangleContactSoundness.RationalSegment3`, `orient3_segment`, `edgeAgainst_sound`, `containsNondegenerate_spec`, `containsNondegenerate_member`, `edgeAgainst_member`, `EdgeContact`, `EdgeMember`, `noncoplanarTrianglesConflict_sound`, `noncoplanarTrianglesConflict_member`, `edgeAgainst_complete` | `audit.c:plane(...)`, `edges_against` and `tg_audit3` | 64 nondegenerate noncoplanar C/Lean/Fraction fixtures; coplanar and shared-index two-face pairs are compared C-only against an exact Fraction replication of the auditor (`triaudit`, 201 pairs including hand-verified nested/touch/shared-edge/piercing cases and identical-triangle rejection); full C auditor refinement remains open |
| Exact 2D/projected-face containment with either nonzero orientation, used by the 3D audit projection branch | `TriangleContains.contains2`, `orient_sum`, `contains2_iff_closedTriangle_of_pos`, `contains2_iff_closedTriangle_of_neg`, `Projection.projectPoint3`, `Projection.containsProject`, `ProjectionBridge.containsProject_of_pos`, `containsProject_of_neg` | static `contains(...)` in `audit.c` | 1,458 integer-grid C/Lean/Fraction `contains2` fixtures in both face orientations; existing `test_audit` adjacent, touching, coplanar and crossing fixtures; orientation negative/positive cases are proved for the Lean specification, not C-refined |
| Oriented incircle sign equals circle power under the stated noncollinearity/circumcircle hypotheses; CDT legality is a separate property | `PredicateGeometry.incircle_circle_identity`, `illegalDelaunay_circle`; `Predicates.illegalDelaunay_sound` | `predicates.c`, `legalize.c` | cocircular/near-cocircular oracle; zero-Lawson-fuel incomplete flag; final local seed legality checks |
| Accepted positive triangles intersect exactly in their common indexed simplex | `Separation`, `SeparationSoundness.mesh_intersection_sound` | `audit.c`, `geometry.c` | shared-edge overlap, isolated contact, skew disjoint, noncoplanar crossings and randomized exact pair fixtures |
| Oriented interior-edge cancellation and prescribed ring-boundary equality imply domain coverage, including edges/vertices by density and closure | `Winding`, `RealTopology`, `Coverage`, `DomainCoverage`, `CertificateCoverage`, `BoundaryCoverage2.check2_domains` | `topology.c`, `geometry.c`, `certificate.c` | annulus, collinear chain, reversed winding, concave L; corrupted faces/boundaries rejected by C and Lean |
| Positive embedded projected complex and consistent heights define a continuous PL graph, homeomorphic to its projected domain | `Barycentric`, `Lift`, `Graph.graphHomeomorph` | graph lift in `geometry.c`; final audit | warped saddle, vertical chart, overhang rejection, frozen diagonal fixtures |
| V1 frozen caller-held request, full seed/output validity, exact reference and unchanged constraints | `Check`, `Soundness`, `ReferenceSoundness`, `Validity.check_sound` | `certificate.c` V1 | actual C certificates, changed seed+output diagonal rejection, request/options mutation and corruption |
| V2 stable/pinned original inputs, unique IDs, ordered exact 3D constraint chains with tags, orientation and full parameter interval [0,1]; fixed subdivision policy | `Subdivision`, `V2`, `ChainSoundness`, `ConstraintCoverage`, `Validity2.InputPreserved` | `features.c`, `edits.c`, `certificate.c` | feature tags 42/99, refinement chains, forbidden edge insertion, owner/parameter/tag/pin/stable-ID mutations |
| Complete affine height bound over the same domain, zero-tolerance equality and symmetric Euclidean distance via equal chart coordinates | `Reference`, `V2Check`, `AffineBound`, `AffineBoundSoundness`, `ReferenceBoundSoundness`, `Validity2.check2_sound` | `overlay.c`, `certificate.c` | opposite warped diagonals: equal input vertex heights but crossing error 1/2; exact 0 and 1/3 reject, 1/2 accepts; actual approximate outputs |
| Finite fuel scheduling and rejected-transaction preservation, for an abstract proposal function and accepted checks | `Schedule`, `Schedule2.schedule2_sound` | bounded loops/staging in `remesh.c` | deterministic repeated output; candidate caps; allocation faults before/after a committed edit; retained valid checkpoints |
| Actual translated uint32 multiply-add returns a*b+c+d < 2^64, no UB or memory/state mutation, for every four uint32 arguments and arbitrary MiniC state satisfying local bindings | `C/Gen`, `C/Arithmetic.limb_madd_bound`, `limb_madd_refines`, `limb_madd_digits`; reused `Obj/C/Semantics`, `Obj/C/Logic` | `exact_core.c:tess_limb_madd`, used in `exact.c` | generated-source freshness; 10,657 direct helper/carry oracle cases |
| Actual translated limb comparison `acmp` returns -1/0/1 exactly, with no UB or state mutation, for arbitrary limb vectors of equal or differing lengths satisfying zi-struct/limb block layouts (allocator excluded) | `C/LimbGen`, `C/Acmp.acmp_loop0`, `acmp_loop_impl`, `acmp_exs`, `acmp_exs_unequal`, `C/Arithmetic` | `exact.c:acmp`, reusing `ziBlock`, `limbBytes` memory model in `C/ZiMem.lean` | caught by incircle/orient3/insphere limb-conversion differential; frozen limb comparisons in grid-integer arithmetic tests |
| Actual translated same-sign limb summation `zi_add_equisign` and mixed-sign magnitudes subtraction `zi_add_mixed` — one iteration correctly lifts the carry/borrow; loop invariant proved against a limb-wise addition model (loop only); allocator, `norm`, `move`, `zi_add` excluded | `C/ZiAdd.ziAddEqui_loop_impl`, `C/ZiAddMixed.ziMixed_loop_impl`, `C/LimbGen`, `C/ZiMem` (limbBytes model) | `exact.c:zi_add_equisign`, `zi_add_mixed` | 1,905/1,905 `exact` stress rows match C exhaustive differential; exercised through the incircle/orient3 differential |
| Inner schoolbook-multiplication accumulation `zi_mul_accumulate_loop0` matches the limb-wise rewrite for every (i, j) position, reusing the proved `tess_limb_madd` spec; outer loop / allocator / norm remain explicit out of scope | `C/ZiMul.ziMulAcc`, `ziMulAccStep`, `ziMulAcc_invariants`, `ziMul_iCell`, `ziMul_inner_loop_impl` | `exact.c:zi_mul_accumulate` (inner loop body) | exact limb-product oracle cases mirrored in the predicate differential `lib/tess/tests/predicate_differential.py`, 10,657 cases for limb-madd |
| Actual translated signed magnitude is the absolute value for every int64 input, including INT64_MIN, with no UB or state change | `C/Magnitude.magnitude_refines`, reusing `Obj/C/Proofs/ObjFixIndex.toInt_i64_wrap` | `exact_core.c:tess_mag`, used in `exact.c` | 4,688 direct helper oracle cases, signed extrema and power-of-two neighbors |
| Integer semantics of the proved limb models: equisign addition denotes `a+b` (with overflow limb), mixed subtraction denotes `a-b` with zero final borrow when `b ≤ a`, schoolbook rows over a zero buffer of capacity ≥ |a|+|b| denote `a*b` | `C/ZiValue.ziAdd_value`, `ziMixed_value`, `ziMul_value` (via `ziAdd_prefix_value`, `ziMixed_prefix_value`, `ziMulAcc_value`, `ziMulRows_value`) | models of `exact.c:zi_add_equisign`, `zi_add_mixed`, `zi_mul_accumulate` | pure arithmetic over the limb models already tied to the translated loops; composing these with the loop refinements through allocation, `norm`, sign dispatch and `move` remains open |
| Order/normalization/sign layer above the limb loops: the proved `acmp` outcomes (equal, longer, top-limb mismatch) imply `lv b ≤ lv a` for normalized `a`; `norm`'s zero-limb trimming preserves the value and yields a normalized list; same-sign and mixed-sign sums have the right signed value | `C/ZiOrder.lv_gt_of_longer`, `lv_gt_of_mismatch`, `lv_le_of_acmp`, `lv_trimL`, `trimL_normalized`, `ziAdd_signed`, `ziMixed_signed` | `exact.c:acmp`, `norm` (length scan only), `zi_add` branch structure | pure model arithmetic; the C `norm` allocation/copy, `zi_add` early-outs for zero operands, the budget `tick` and `move` are not refined |\n
| Functional models of `zi_add`, `zi_sub`, `zi_mul` (zero early-outs, sign dispatch by the `acmp` order, `norm` trimming with zero-sign, schoolbook rows) denote signed integer `+`, `-`, `*` and return well-formed values (normalized, limbs < 2^32, sign 0 iff empty) | `C/ZiModel.ziAddM_val`, `ziSubM_val`, `ziMulM_val`, `zNorm_val`, `zNorm_wf`; dispatch condition discharged by `ZiOrder.lv_le_of_acmp` | `exact.c:zi_add`, `zi_sub`, `zi_mul` control flow | model-level only: allocator/`make` failure, `tick` budget, `move`, and the MiniC refinement of the whole functions are not proved; tied to C only through the loop refinements and differential `tess_zi_oracle` |\n
Both helpers have symbolic MiniC refinement proofs. The full arbitrary-precision
implementation, allocation/resource
handling, 3D auditor, numeric metrics, optimizer, OBJ parser/writer and C compiler
are not refined by these proofs. The abstract schedule theorem does not prove
that the C schedule implements the model. Deterministic seed choice is tested C
behavior, not replayed in Lean. No angle, quality-convergence, termination-with-
targets-met, physical-metric CDT or normal-deviation theorem is claimed.

Lean's executable overlay checker enumerates rational intersections and validates
independent nonnegative affine-dual identities for whole-cell bounds. Soundness
of accepted identities is proved; existence/search completeness is unnecessary
and not claimed. Resource-bounded checkers can reject valid geometry.

## Reproduce the proof audit

```sh
# Lean v4.35.0 and mathlib revision are pinned in formal/.
(cd formal && lake exe cache get)
python3 formal/tools/check_tess_proofs.py
```

The script checks default tinyobjloader generation freshness and selected tess
helper freshness, rejects incomplete-proof/axiom/native-decision tokens in Tess
sources, builds `Tess` and `tesscheck`, then runs `TessAudit.lean`. The audit scans
compiled dependencies of all public Tess declarations, not only the final two
theorems. The current audit covered 1302 declarations and permitted only
`propext`, `Classical.choice`, and `Quot.sound`. Compiler warnings about style or
deprecations do not weaken this kernel-backed dependency check. No incomplete
proof is accepted. The generated executable additionally depends on Lean's
runtime; decoding and external byte associations remain the documented trust
boundary in [CERTIFICATES.md](CERTIFICATES.md).

[Predicate validation commands and protocol](PREDICATE_VALIDATION.md) document
the direct executable comparison, including its indexed-contact convention
and explicit resource-exhaustion fixture.
