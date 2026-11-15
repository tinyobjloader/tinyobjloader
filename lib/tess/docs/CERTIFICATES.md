# Certificates, requests and trust boundary

A mathematical certificate is accepted only after the executable Lean checker
accepts the actual emitted bytes against a separately retained canonical request:

```sh
(cd formal && lake build Tess tesscheck tesspredicates)
formal/.lake/build/bin/tesscheck held-request.tess actual-output.tess
# Alternatively: request bytes, one NUL byte, then result bytes on stdin.
formal/.lake/build/bin/tesscheck --stdin < request-NUL-result.bin
```

Exit codes are 0 accepted, 1 rejected/malformed, 2 usage, and 3 resource limit.
C certificate checking is useful independent validation but is not a Lean
certification. Preserve the request outside an untrusted producer's control.
Both versions bind the entire frozen seed, input rings, chart request and planar
mode; version 2 additionally binds run options and stable/provenance metadata.
An attacker cannot replace both seed and output diagonals to redefine a warped
reference while retaining a caller-held request.

## Line format

ASCII lines end with LF. Unsigned integers are canonical decimal. A rational is
`signedHexNumerator/positiveHexDenominator`: normalized gcd, no negative zero,
zero numerator `0`, other magnitudes as lowercase hexadecimal in groups of eight
hex digits per uint32 limb, most significant first. Writers emit a final LF.
The checker rejects unsupported versions, invalid fields and trailing data.

The common prefix is version (`TESS1` or `TESS2`), seed-policy string, requested
axis encoded as axis+1 (0 means automatic), strict-planar boolean, ring count,
and ring-count+1 cumulative vertex offsets, each on its own line. Version 2 then
has `RUN2`, followed by target count, exact target rational, exact tolerance,
boundary subdivision boolean, feature subdivision boolean, owner-list mode,
allowed owner count and that many owner IDs, three 16-hex-digit binary64 quality
threshold bit patterns, three pass/edit/candidate limits, and five resource caps
(vertices, faces, limbs, bytes, operations). There are 19+owner-count RUN2 lines
including its marker.

Two meshes follow: frozen seed then output. Each starts with eight lines:
vertex count, face count, constraint count, dropped axis, u axis, w axis,
orientation boolean, exact-planarity boolean. A V1 vertex is source+1 (0 means
no source), pinned boolean, x, y, z. V2 inserts stable vertex ID after pinned.
A V1 face is three vertex indices; V2 adds stable face ID. A V1 constraint is
a,b,kind,source. V2 adds owner, start parameter, end parameter and a 16-hex-digit
tag. Kinds are boundary=1, implicit crease=2, user=3. V2 constraints are sorted
by owner and start parameter. `END` terminates the certificate.

The canonical request is a pre-run certificate saved after `tess_prepare_remesh`;
its output equals its frozen seed. The result includes the same seed and options.
The actual exported-coordinate certificate replaces output coordinates with
exact dyadic decodings of the rounded binary64 array and rechecks it.

The Lean decoder imposes a 16 MiB file cap, 10,000 vertices, 20,000 faces,
1,024 hex digits per magnitude, and a one-million pair-work guard. These practical
limits can reject a C-valid artifact. An undecidable-in-budget search is a
rejection/resource outcome, never an invented geometric acceptance. Kernel
soundness is conditional on a successful decoded `check`/`check2` computation.

## OBJ assembly bundles

`tess_obj` writes `.obj`, `.obj.tess`, and `.obj.tess-request`. Bundle headers are
`TESS-ASSET1` and `TESS-ASSET-REQUEST1`. Each record is KIND LF, canonical decimal
byte count LF, then exactly that many payload bytes. `END` LF ends the stream.
The bundle contains SOURCE, OPTIONS, per-patch PATCH_REQUEST/PATCH_EXACT/
PATCH_ROUNDED/PATCH_MAP/PATCH_REPORT, then OBJ and REPORT. The held request
contains SOURCE, OPTIONS and per-patch PATCH_REQUEST/REQUEST_MAP.

Maps associate original source faces and input global vertices with output
vertex IDs, stable IDs and contiguous global face ranges. The Python verifier
binds source/options/request bytes, original global-ID prefixes, actual rounded
OBJ coordinates and oriented face tuples, and coverage of every output face.
It runs Lean on each exact and rounded patch, then invokes `tess_obj_audit` on
the assembled asset. This last step catches interpatch crossings and forbidden
contacts that individual patch certificates cannot exclude.

```sh
python3 lib/tess/tools/verify_asset.py --source input.obj \
  --request output.obj.tess-request --bundle output.obj.tess --obj output.obj \
  --lean-checker formal/.lake/build/bin/tesscheck --audit-exe /tmp/tess-build/tess_obj_audit
```

The Python verifier bounds each file before reading beyond 256 MiB, record count
at 200,000 and kind/length tokens. Negative, noncanonical and truncated lengths
reject. Exit 3 denotes an explicit resource/timeout failure, 1 malformed or
rejected content. Exit 3 from either the Lean checker or assembled auditor is
propagated as a resource failure. These limits are independent of the C result heap limit.

## What is and is not proved

`Tess.check_sound` and `Tess.check2_sound` prove properties of decoded exact
artifacts. The kernel audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, new axioms or native-decision shortcuts are
allowed in Tess proof sources. Lean's compiler/runtime, parser/serializer,
canonical-request custody, OBJ numeric parser, maps/assembly verifier, C audit,
host compiler and hardware remain trust boundaries. Native checker evaluation
uses Lean's runtime; a hostile runtime is outside this claim.

For positive height tolerance, Lean enumerates overlays and independently
validates nonnegative affine-dual identities over triangle halfplanes to bound
the complete overlap cell. Failed witness search safely rejects. Completeness
of the search is not claimed. Coverage is proved through oriented boundary
winding, cancellation, density and closure, rather than assumed in the theorem.

The existing MiniC/c2lean path translates the actual C limb multiply-add and
signed-magnitude helpers. Symbolic proofs cover their integer arithmetic,
return values and unchanged state, including INT64_MIN without signed overflow.
A separate limb-digit theorem bounds both output digits and their exact
reconstruction of the multiply-add value.
It does not refine the full integer/rational allocator or geometry library.
C validity and optimizer behavior are supported by independent checks, oracle,
fuzz and failure-injection tests. Quality/convergence and deterministic seed
replay are not conclusions of the artifact soundness theorem.
