# Research and design record

Consulted 2026-11-14. These sources guide design; their algorithms and guarantees
are not incorporated as proofs of this implementation. No external geometry
library is linked into the production C11 core.

- [CGAL 6.2 remeshing manual](https://doc.cgal.org/6.2/PMP_Remeshing/index.html)
  describes support-plane face CDT and local split/collapse/flip/smoothing with
  projection to a reference. This implementation uses an exact axis-drop chart,
  frozen graph connectivity, physical 3D area and full candidate checks instead.
  Chart CDT has a different metric from physical planar CDT. The manual's
  triangulation visitor supports optional provenance comparisons; constrained
  boundary splitting must be configured consistently for fair comparisons.
- [CGAL 6.2 release notes](https://www.cgal.org/2026/06/11/cgal62/)
  confirm the package separation for meshing/remeshing and the compatibility of
  older PMP includes. Optional comparison tools must record the actual version.
- [CGAL's 2025 remeshing announcement](https://www.cgal.org/2025/05/22/Surface_remeshing/)
  distinguishes ACVD clustering with a vertex budget from almost-planar patch
  simplification. Neither is equivalent to this library's triangle-area target.
  Here patch merging requires exact coplanarity and shared source indices;
  near-planar diagnostics never silently change the reference surface.
- [Shewchuk's predicates page](https://www.cs.cmu.edu/~quake/robust.html)
  explains robust determinant signs and adaptive arithmetic assumptions. The
  baseline here uses checked limb/rational arithmetic throughout and has no
  floating filter whose correctness depends on floating execution assumptions.
  Binary64 is decoded as exact dyadics after explicit layout checks.
- [Shewchuk's refinement papers and thesis](https://www.cs.cmu.edu/~jrs/jrspapers.html)
  distinguish refinement theorems from bounded mesh-improvement heuristics. We
  implement no circumcenter insertion and claim no guaranteed minimum angle,
  edge-length bound or quality convergence. Seed Lawson flips retain cocircular
  ties and report incomplete legalization when their edit fuel is exhausted.
- [Lipschütz, Reitebuch, Polthier and Skrodzki, 2026](https://research.tudelft.nl/en/publications/feature-aware-manifold-meshing-and-remeshing-of-point-clouds-and-/)
  give manifold and smallest-edge guarantees under suitable input/parameter
  assumptions. The portal abstract was consulted; the linked extended PDF was
  too large for the browser fetch. We do not transfer those guarantees. Tagged
  seed edges and explicit pinning are hard constraints here, and short edges
  remain a diagnostic rather than a theorem-backed exclusion.
- [Liu, Ye and Chen's project page](https://ltrbless.github.io/projects/Remesh/)
  for *Fast Intersection-Free Remeshing of Triangular Meshes* identifies
  collision checking as a bottleneck and describes adaptive checking. The DOI
  endpoint was unavailable through the browser; the authors' abstract was used.
  Here exhaustive exact reference checks remain available and acceleration only
  culls pairs separated by conservative closed exact AABBs. Equality/contact is
  retained. Randomized regression compares accelerated and slow decisions.
- [Gabriel, Remacle and Geuzaine, 2026 preprint](https://arxiv.org/abs/2607.04989)
  constructs intrinsic edges along geodesic paths on watertight reference meshes.
  That representation could extend beyond a single chart, but these outputs are
  straight 3D triangles and have none of that intrinsic algorithm's guarantees.
- [BijectiveRemesh, 2026 preprint](https://arxiv.org/abs/2605.30744)
  composes local bijective maps for data transfer. General correspondence and
  attributes are future extensions here. Our correspondence matches equal chart
  coordinates; the Lean graph, coverage and symmetric distance theorems establish
  its validity on the admitted single-chart domain.

The Lean height proof uses exact overlay enumeration plus independently checked
affine dual witnesses for each triangle-pair cell: a nonnegative combination of
its six half-plane inequalities and the constant one proves each signed bound.
This avoids assuming enumeration completeness. The search is not trusted;
coefficients and exact identities are checked. Continuity extends bounds from
open overlap cells to closed boundaries and creases.
