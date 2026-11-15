# Complete segment predicates and direct differential validation

`Tess.closedIntersection_iff_real` proves that the exact executable predicate is
true exactly when its two real closed segments have a common point.
`closedIntersection_iff_rational` gives the equivalent rational common-point
characterization. `closedIntersection_false_iff` proves that false means the
real closed segments are disjoint. There is no general-position hypothesis:
zero-length segments, endpoint touches, coincident intervals and reversed
endpoints are included. These complement the previously proved
`onSegment_iff_real` and `onSegment_iff_rational` membership equivalences.

The proof in `formal/Tess/IntersectionCompleteness.lean` separates collinear
interval contact from proper crossing. A rational supporting line has rational
parameters for all its rational points. Intersecting collinear intervals have
an endpoint contact; otherwise, strict interpolation parameters force opposite
orientation signs on both supporting lines. Soundness supplies an exact
rational crossing witness. This is a theorem about the executable Lean
specification, not a refinement of the C geometry implementation.

The exact 3D orientation determinant is the light executable specification in
`formal/Tess/Orient3.lean`. `Tess.Orient3Bridge` proves its exact cast to the
real scalar triple product, that vanishing means determinant coplanarity of the
four points (linear dependence, without a noncollinearity hypothesis), and that
the checker's `planeValue` is exactly this determinant in the executable row
order. These are claims about the Lean specification, not the C executable.

`Tess.segmentConflict` in `formal/Tess/SegmentConflict.lean` is the indexed
exception test used by exact face-pair and boundary validation. It returns
false for the same unordered indexed edge in either orientation. Otherwise it
reports either a geometric crossing, or a point from either edge lying on the
other edge while its vertex ID is not an endpoint of the supporting edge.
`formal/Tess/IndexedConflict.lean` proves:

- `segmentConflict_closedIntersection`: an indexed conflict is a real closed
  segment intersection;
- `segmentConflict_iff_closedIntersection`: with valid indices, nondegenerate
  projected edges and disjoint edge endpoint-ID sets, indexed conflict is
  equivalent to ordinary closed geometric intersection;
- `segmentConflict_same_unordered`: an identical edge, in either ID order, is an
  expected shared simplex rather than a conflict;
- `segmentConflict_shared_head`: for edges sharing only index `a`, a conflict
  has precisely the remaining unexpected endpoint contacts. Proper crossing is
  impossible at a shared indexed vertex; collinear overlap beyond that vertex
  is still reported.

Thus ordinary `closedIntersection` must not be identified with
`segmentConflict` when the two edges share an indexed vertex or are the same
unordered indexed edge. The valid-index and projected-nondegeneracy assumptions
are stated explicitly on the equivalence theorem. Projection disjointness is not
needed by the conflict branch definitions. These proofs also concern the
executable Lean specification, not the C implementation.

## Reproduce

```sh
(cd formal && lake build Tess tesscheck tesspredicates)
python3 formal/tools/check_tess_proofs.py
cmake -S lib/tess -B /tmp/tess-validation -DCMAKE_BUILD_TYPE=Release -DTESS_TEST_LEAN=ON
cmake --build /tmp/tess-validation -j4
ctest --test-dir /tmp/tess-validation -R 'tess_(lean_predicates|predicate_resources)' --output-on-failure
```

`TESS_TEST_LEAN` now requires both `tesscheck` and `tesspredicates`. Override
`TESS_LEAN_CHECKER` and `TESS_LEAN_PREDICATES` for binaries outside the default
`formal/.lake/build/bin` directory. Native-only builds do not require Lean.
The proof audit builds both executables and CI runs the differential test.

`tests/predicate_differential.py` compares C, executable Lean and an independent
Python Fraction oracle on 19,982 fixtures for orientation, orientation-correct
incircle, 3D orientation and noncoplanar triangle audits, segment membership and indexed/ordinary segment conflict. It uses exhaustive 3x3
integer grids, mixed dyadic exponents, collinear and degenerate data, near-contact
endpoints and cocircular perturbations. The Python circle oracle eliminates a
full 4x4 homogeneous matrix; C uses a translated 3x3 determinant. Ordinary segment contact
uses exact line parameters and interval overlap in Python, versus determinant
signs in the implementations.

For `orient3`, 128 low-coordinate grid points, 256 bounded dyadic-exponent
random points and 128 axis-dominant extreme-exponent cases are compared exactly.
The extreme cases stay within C's default work budget. `tricontact` additionally
covers 64 nondegenerate noncoplanar random/float pairs and 36 nested source-edge
fixtures where one edge lies in the other face's plane and only the middle
overlaps the target triangle; it is an acceptance test for the direct C/Lean/Fraction
path and excludes the indexed shared-simplex exception.

For the first 100 ordinary `segments` records, the executable C and Lean
`segments` probes are used. The remaining ordinary segment records exercise
`indexedsegments` with disjoint IDs `0,1,2,3`, whose indexed result is the same
closed geometric intersection. Shared-ID cases enumerate every endpoint-position
pairing, identical and reversed indexed edges, larger vertex IDs, and collinear
or mixed-exponent triples. Repeated IDs must carry equal coordinates; the Lean
fixture rejects inconsistent repetitions.

Non-dyadic rational parser mutations are compared between Lean and Fraction
only. C coordinates are binary64 values; their exact dyadics are sent to Lean and
Fraction without decimal rounding.

A frozen mixed-exponent incircle case exceeds C's default 100-million-unit work
cap. The resource regression requires an explicit library resource error, no
sign output, and complete teardown. Lean and Fraction agree on its exact sign.
This is an expected bounded outcome, not an accepted C predicate result. The
C test probe exits 5 while reporting library status 3; this convention is local
to the test executable and does not change the public API or OBJ CLI statuses.
`tests/predicate_resources.py` runs independently of Lean, including in sanitizer
CI. The probe releases the mesh on error paths before returning.

## Bounded validation protocol

`tesspredicates` is a test executable, separate from artifact certificates.
It reads standard input as LF-separated records. Ordinary records are an
operation (`orient2`, `incircle`, `onsegment`, `segments`) followed by eight
ASCII-space-separated exact rational coordinates, `ax ay bx by cx cy dx dy`.
`orient3` instead carries twelve 3D coordinates in the same point order.
`tricontact` carries six 3D points as eighteen coordinates. Both implementations
return 1 when the triangles do not conflict and 0 on geometric contact. The C
probe evaluates `tg_audit3` with two triangles and reports the audit result;
the Lean fixture evaluates `Tess.noncoplanarTrianglesConflict` exactly. Coplanar
pairs and indexed shared-simplex cases are not included in those fixtures.

The indexed conflict record is `indexedsegments ax ay bx by cx cy dx dy a b c d`:
the same eight coordinates followed by four vertex IDs. Repeated IDs denote the
same vertex, so every repetition must carry the same exact coordinates. IDs are
nonnegative and less than 1024. C uses the same twelve-coordinate `tg_orient3`
row order; exact huge arbitrary determinants may still exhaust the C budget and
are not accepted as results. A coordinate is a signed decimal integer
numerator, `/`, and a positive decimal denominator. Rationals normalize on
decoding. The last point of the eight-coordinate records is ignored for orientation and membership; keeping
eight coordinates gives those modes the same shape. `orient3` uses all twelve 3D coordinates, and `tricontact` uses all eighteen.

For example:

```sh
printf 'segments 0/1 0/1 1/1 1/1 0/1 1/1 1/1 0/1\n' | formal/.lake/build/bin/tesspredicates
# 1
printf 'indexedsegments 0/1 0/1 1/1 1/1 0/1 1/1 1/1 0/1 0 1 0 1\n' | formal/.lake/build/bin/tesspredicates
# 0
```

Orientation/incircle return -1, 0 or 1; membership/intersection return 0 or 1.
The byte limit is 8 MiB, record/newline limit 20,000, line limit 32,768 characters,
and numerator/denominator token limit 1,024 characters. Newline count is checked
before allocating split records. Exit 0 means all records evaluated, 1 malformed
input, 2 usage and 3 an explicit size limit. Partial stdout preceding a failed
record does not make a batch successful; callers must require exit 0.

Targeted malformed/oversized/UTF-8/NUL/usage tests and 128 deterministic byte
mutations exercise the parser. Accepted mutations are checked against
Fraction. Parser tests also cover the indexed operation's missing and negative
IDs, IDs at the explicit resource cap, and inconsistent repeated-ID coordinates.
This parser and native execution are validation boundaries, not newly proved serialization or compiler refinements. The existing artifact
checker remains unchanged.
