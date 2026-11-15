# Geometry and optimization contract

All topological decisions use normalized rational arithmetic. The hosted
binary64 adapter copies bits and decodes finite normal, subnormal and zero
values exactly; signed zeros coincide. Integers use signed magnitudes with
uint32 limbs and uint64 multiply-add temporaries. Overflow, allocation failure,
limb growth and operation exhaustion propagate as errors. There are no floating
predicate filters in this release and no epsilon topology decisions.

## Charts and frozen surfaces

Dropping axis `a` uses the cyclic remaining axes `(a+1)%3,(a+2)%3`;
the recorded winding transform normalizes internal orientation. Automatic
selection sorts the absolute exact outer areas decreasingly, breaking ties by
axis index. It tries full ring validity in that order. Explicit selection tries
only that chart. A nonzero area alone does not establish a supported chart.
The exact tests reject repeated coordinates, backtracking, crossings, contacts,
overlapping edges and touching/nested/outside holes. Outer winding may be either
sign; holes must oppose it. Diagnostics retain source indices where available.

Planar mode requires exact coplanarity. Graph mode freezes the seed connectivity
and all input coordinates: changing a warped quadrilateral's diagonal can
change its surface. The metadata policy is
`SEED-VISIBILITY-ROTATION-LEFT1-LAWSON1`. The seed is a deterministic C behavior;
the checker certifies the supplied frozen seed without replaying that selection.
Axis-drop Delaunay legality is in the chart metric, including on sloped planes.

## Seed construction and independent validation

Boundary segments initialize a planar graph. Stable vertex pairs are added
when their open diagonal contains no third vertex, has no forbidden intersection
with any existing edge, and has an exact interior midpoint in the domain.
An exact half-plane/cross-product rotation system traverses all half-edge cycles.
A rational offset to the left of a directed edge is halved until the path from
the midpoint is disjoint from every other segment. This local witness classifies
the domain side; it does not use a nonconvex polygon's centroid.

A maximal visibility graph of an admitted polygonal domain has triangular domain
faces: a nontriangular polygonal face admits an interior diagonal between visible
vertices. Retained collinear vertices preclude diagonals through them; holes
must be connected by visibility edges before maximality. The implementation does
not rely on this argument for accepting its output: every selected domain cycle
must be a positive triangle, and a full independent validator checks the result.
Failure to construct that result is an explicit error or resource exhaustion.

Stable Lawson passes flip only unconstrained strictly convex quadrilaterals with
strictly positive orientation-correct incircle violation. Cocircular diagonals
remain. A separate final edge test sets the seed legalization-complete flag;
budget exhaustion may return a valid seed with that flag false. This flag never
claims that an optimized result is CDT.

Validation checks oriented incidence, duplicate faces, vertex links, connectivity,
Euler characteristic, full oriented boundary chains and exact pairwise shared
simplex intersections. A shared index permits only its geometric simplex, not
an overlap. The independent 3D audit rejects degenerate triangles, reduces
coplanar pairs to a supported planar chart, and intersects noncoplanar triangles
with their planes using exact rational cuts. Closed exact AABBs conservatively
cull pairs; all-pairs implementations remain differential-test references.

## Remeshing and measurements

Count mode bounds each physical area square root by exact rational intervals,
refines the sum until rounding is determined, and rounds reference-area/count
once to a positive dyadic with approximately 40 significant bits (nearest, ties
up). Explicit area mode uses the supplied exact rational or exact binary64 value.
The target remains fixed. Hard face thresholds compare exact squared physical
areas. The short-edge proposal uses the equilateral scale
`h²=4*A_target/sqrt(3)`; approximation is permitted for ranking, never topology.

The bounded schedule proposes conforming edge splits, exact triangle-centroid
splits, link-condition interior collapses, convex flips, and one-ring-average
relocations with bounded step reductions. Stable IDs and array order determine
ties. Local changed-face objective deltas pre-rank count-preserving proposals.
Every accepted proposal strictly improves the reported global objective:
mean squared log area ratio plus 0.02 times mean mean-ratio shape penalty.
The global comparison is strict on the checked binary64 report; engineering
floating metrics do not decide geometric validity. Split/collapse hysteresis,
pass/edit/candidate limits and operation fuel bound execution.

Every proposal lives in a staging mesh. Full projected topology, intersection,
constraint-chain and frozen-reference checks precede commit; final independent
3D auditing remains mandatory. Allocation/resource failures discard the stage
and retain the last validated checkpoint. A reserve of operation fuel is kept
for final validation. Reports distinguish validity rejection, objective rejection,
constraints, stagnation and resource/iteration budgets. Targets can remain unmet.

Exact mode preserves implicit crease edges separating unequal affine seed planes.
Original vertices are pinned. User features are tagged existing frozen-seed edges;
there is no general interior constraint insertion. Authorized subdivision stores
an ordered chain with exact segment parameters, original 3D image and tags.
Approximation may remove implicit creases, but not user features. New points lift
from the frozen reference. Exact overlay tests include contained vertices, proper
crossings and coincident endpoints; the maximum affine height difference occurs
at an overlay cell vertex. The exact maximum is exposed separately from the
approximate report. Height tolerance bounds dropped-coordinate displacement,
not normal error. Equal chart-coordinate correspondence gives a symmetric
Euclidean distance upper bound.

Binary64 export is a separate checked operation: round coordinates, decode them
back exactly, and revalidate the requested contract. A pinned rational such as
1/3 may have no valid binary64 export. Exact success never implies export success.

## Costs and resource scope

This is a bounded reference implementation. Visibility construction can require
O(V²) proposals against O(V²) edges, hence O(V⁴) exact tests in the conservative
worst case. Dense incidence uses O(V²) storage; face validation is O(F²), overlay
validation O(F_seed*F_output), and whole-patch candidate checks repeat these
costs. Limb sizes and arithmetic work add substantial data-dependent costs.
AABBs improve typical cases without changing worst-case complexity.

Default caps are 10,000 vertices, 20,000 faces, 4,096 limbs/integer, 256 MiB of
accounted result construction/staging storage, and 100 million arithmetic work
units. These are safety caps, not promised practical mesh sizes. Separate
checker/adapter contexts have their own caps; the cap is not total process RSS.
See the resource sweep and benchmark reports for measured limits on small patches.
