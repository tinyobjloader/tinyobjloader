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
Python Fraction oracle on 21,923 fixtures for orientation, orientation-correct
incircle, 3D orientation, strict plane cuts, 2D containment and noncoplanar
triangle audits, segment membership and indexed/ordinary segment conflict.
Coplanar and shared-index triangle pairs run C-only against the Fraction
oracle (operation `triaudit`). It uses exhaustive 3x3
integer grids, mixed dyadic exponents, collinear and degenerate data, near-contact
endpoints and cocircular perturbations. The Python circle oracle eliminates a
full 4x4 homogeneous matrix; C uses a translated 3x3 determinant. Ordinary segment contact
uses exact line parameters and interval overlap in Python, versus determinant
signs in the implementations. When the record count exceeds Lean's per-invocation
fixture cap, the differential feeds each probe in 19,000-record chunks rather
than weakening the cap; all records are still checked.

For `orient3`, 128 low-coordinate grid points, 256 bounded dyadic-exponent
random points and 128 axis-dominant extreme-exponent cases are compared exactly.
The extreme cases stay within C's default work budget. `tricontact` additionally
covers 64 nondegenerate noncoplanar random/float pairs and 36 nested source-edge
fixtures where one edge lies in the other face's plane and only the middle
overlaps the target triangle; it is an acceptance test for the direct C/Lean/Fraction
path and excludes the indexed shared-simplex exception.

`planecut` compares the strict-crossing branch of the 3D auditor. Both sides
receive a z-normal face grid in one batch (mixed strict, same-side, on-plane
and endpoint-touching configurations), 64 reversed-orientation cuts and 128
bounded random 3D dyadics. C prints the exact rational cut point with
hexadecimal numerator/denominator tokens (`0x` prefixes, `/` separator) or `0`;
Lean prints `1` plus the three rational coordinates in decimal
numerator/denominator form, or `0`; Python computes `dx/(dx-dy)` and the point
on the segment exactly. Lines are matched exactly as Fractions, so a reported
coordinate cannot be merely close. The C operands keep dyadic exponents within
±15 so the default C work budget is never exhausted; no planecut fixture
relies on resource exhaustion.

`contains2` compares the 2D no-mixed-sign closed-triangle projection test used
by the 3D auditor's projected branch (`contains` in `audit.c`), in both face
orientations. Fixtures enumerate integer triples over a 3x3x3 grid with two
probe points each; the clockwise case exercises the reversed edge order. The
Python oracle computes the three exact edge signs and accepts either all-
nonnegative or all-nonpositive. Coplanar degenerate faces are rejected by the
auditor separately and are not part of the fixture set.

`triaudit` is a separate C-only diagnostic mode covering the two paths that
`tricontact` deliberately excludes: coplanar face pairs (including identical,
reversed and shared-edge/vertex faces whose IDs are expected shared simplices,
and the identical-triangle rejection) and indexed shared-index fixtures. C
prints 1 when `tg_audit3` accepts the two-face mesh and 0 otherwise. The
Python oracle replicates the auditor's exact algorithm: coplanarity from
`planeValue`, projected containment on the face's own first nondegenerate
axis, per-ID shared-simplex allowance (point equality, and on-segment +
collinearity for two shared IDs), projected segment-conflict detection with the
indexed exception, and the identical-triangle (three shared IDs) rejection.
The Lean fixture has no executable specification for this path and rejects the
`triaudit` operation explicitly; the differential compares C against the
Fraction oracle only, and six hand-verified fixtures (nested coplanar,
disjoint, bottomed-out edge touch, shared edge, noncoplanar pierce, parallel
sheet) are asserted before the 195 random/constructed pairs.

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

Frozen mixed-exponent incircle, orient3 and tricontact fixtures exceed C's
default 100-million-unit work cap. The resource regression requires an explicit
library resource error, no sign output, and complete teardown for each. Lean
and Fraction agree on their exact signs. These are expected bounded outcomes,
not accepted C predicate results. The C test probe exits 5 while reporting
library status 3; this convention is local
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
`triaudit` carries six 3D points as eighteen coordinates followed by six face
vertex IDs (three for each face index triple, IDs less than 6), and prints
`tg_audit3`'s accept bit on the C side only; the Lean fixture rejects it.

`planecut` carries five 3D points as fifteen coordinates: face `a b c` then
the edge endpoints `x y`. Output is either `0` (endpoint plane signs not
strict opposites, no strict cut) or `1` with the three exact rational cut
coordinates. The C probe prints hexagonal numerator/denominator tokens
(`0x…/0x…`, sign prefix allowed); the Lean fixture prints decimal
`num/den` tokens. Python parses both encodings back to exact Fractions.

`contains2` carries two 2D points as eight coordinates and prints `1` when the
last point lies in the closed triangle with either orientation, `0` otherwise.

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

Orientation/incircle return -1, 0 or 1; membership/intersection return 0 or 1;
containment and audit modes return 0 or 1; `planecut` returns 0 or a `1` record
with three rationals.
The byte limit is 8 MiB, record/newline limit 20,000, line limit 32,768 characters,
and numerator/denominator token limit 1,024 characters. Newline count is checked
before allocating split records. Exit 0 means all records evaluated, 1 malformed
input, 2 usage and 3 an explicit size limit. Partial stdout preceding a failed
record does not make a batch successful; callers must require exit 0.

Targeted malformed/oversized/UTF-8/NUL/usage tests and 256 deterministic byte
mutations exercise the parser. Accepted mutations are checked against
Fraction. Parser tests also cover the indexed operation's missing and negative
IDs, IDs at the explicit resource cap, inconsistent repeated-ID coordinates,
and explicit rejections of truncated `planecut`, `contains2` and `triaudit`
records.
This parser and native execution are validation boundaries, not newly proved serialization or compiler refinements. The existing artifact
checker remains unchanged.
