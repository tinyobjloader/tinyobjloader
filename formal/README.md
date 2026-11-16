# tinyobjloader — formal specification and verification (Lean 4)

This directory holds the Lean 4 formalization for the tinyobjloader C11 OBJ
parser in `tiny_obj_c.c` / `tobj_tess.c` and the shared translation unit
`tiny_obj_verified.c`.

1. **MiniC**, a small operational semantics for the C subset used by the
   "verified core" of the loader (`Obj/C/Semantics.lean`), derived proof
   rules (`Obj/C/Logic.lean`, `Hoare.lean`), byte-splice algebra
   (`Splice.lean`), arithmetic lemmas (`Lemmas.lean`);
2. a translator `tools/c2lean.py` (clang AST → MiniC, rejecting anything
   outside the subset) whose output is `Obj/C/Gen.lean` (**generated**, do
   not edit);
3. the **verified core** of the OBJ tessellator and mesh builder: memory,
   size-arithmetic, cursor, index and tessellation helpers translated to
   MiniC (59 functions in `Gen.lean`, including `tobj_size_mul`,
   `tobj_next_token`, `tobj_tess_signed_area`, `tobj_tess_project_f/d`,
   `tobj_tess_run2d`, `tobj_tess_polygon_core_f/d` and `emit_face_core_f/d`);
4. **proofs** that the translated code has no undefined behaviour and matches
   the C intent, plus kernel-checked regression tests.

> Note: the format-specific model modules (`Validate`, `Glb`, `Model`,
> `B64`, `Safety`) and the old `CDiff.lean` tooling were carried over from an
> earlier formal library. They do not describe the OBJ loader. The model
> modules remain available as regression examples, while `Obj/Tests.lean`
> combines those examples with the ObjMiniC tests. The tinyobjloader
> specification (OBJ grammar, mesh well-formedness) is **not yet written**.

Everything builds with `lake build`; there is no `sorry`. Every theorem
depends only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). No Mathlib, no `native_decide`, no
`bv_decide`.

## Build and check

```sh
cd formal
lake build                                  # spec, tests, MiniC, all proofs
python3 tools/c2lean.py --check             # Obj/C/Gen.lean matches tiny_obj_verified.c
```

`tools/c2lean.py` needs `clang` (it reads `clang -Xclang -ast-dump=json`).
`tools/cdiff.py` is legacy tooling for a different C source and is not part
of the OBJ verification workflow.

`./tiny_obj_verified.c` (`#include tiny_obj_c.c` + `tobj_tess.c`) is the
translator input; keep it a valid single translation unit.

## Status

| Tier | C code | What is proven | Status |
|---|---|---|---|
| Translator | 59 functions across builder, cursor, index, size, tessellation helpers | c2lean translates the subset it understands and **verifies**; anything outside raises an error rather than guessing | in progress (more helpers need translation) |
| MiniC examples | `tobj_is_space`, `tobj_is_digit`, `tobj_is_pow2`, `fix_index_f`, `emit_face_core_f`, `tobj_size_mul`, `tobj_size_add` | kernel-checked `callFunc` examples (`decide +kernel`), including store-writing functions | done (`Obj/Tests.lean`, `Obj.Tests.ObjMiniC`...`ObjMiniC26`) |
| Invariant proofs | `tobj_is_space` | `tobj_is_space_space` / `tobj_is_space_tab` / `tobj_is_space_other`: for any input in the i8 range the translated code returns 1 iff c is `' '` or `'\t'`, 0 otherwise; no UB, terminates, no state change (`Obj/C/Proofs/ObjIsSpace.lean`, incl. `toInt_i32_wrap_i8` sign-extension helper and `evCast_i8_i32`) | done |
| Invariant proofs | `tobj_is_digit` | `tobj_is_digit_ge` (48 ≤ c ≤ 57 → 1), `tobj_is_digit_lo` (c < 48 → 0), `tobj_is_digit_hi` (57 < c → 0): for any i8-range input the translated code returns 1 iff c is in '0'..'9'; no UB, terminates, no state change (`Obj/C/Proofs/ObjIsDigit.lean`) | done |
| Invariant proofs | `tobj_is_pow2` | `tobj_is_pow2_zero` (0 → 0), `tobj_is_pow2_eight` (8 → 1), `tobj_is_pow2_six` (non-power of two → 0) (`Obj/C/Proofs/ObjIsPow2.lean`) | done |
| Invariant proofs | `fix_index_f` (store-writing control-flow) | `fix_index_f_pos`: for any i32 index `idx > 0`, the translated function stores `idx - 1` at `*out` (little-endian i32), never hits UB, returns 1; `fix_index_f_neg`: for `idx < 0` with `n + idx >= 0` (vertex counts below 2^31), stores `n + idx` (OBJ relative-index semantics), returns 1 (`Obj/C/Proofs/ObjFixIndex.lean`, incl. `toInt_i32_wrap`, `toInt_i64_wrap`, `toInt_i64_wrap_u64` helpers). Together: the translated code computes the correct relative OBJ index for every record of the `*out` buffer. | done |
| Spec ↔ C refinement | `fix_index_f` vs `Obj.resolveIndex` / `storedIndex` (pure spec in `Obj/Spec.lean`) | `fix_index_f_refines` (`Obj/C/Proofs/FixIndexRefines.lean`): for every i32 index and element count below 2^31, the function returns 1 iff the index resolves, and stores `storedIndex` at `*out`; the four case lemmas cover `idx > 0`, `idx = 0`, and negative in/out of range | done |
| Index semantics decision | Positive OBJ indices | `resolveIndex` follows `fix_index`: every positive i32 index resolves to `idx - 1`, even when that value is at least `n`; downstream access validation is responsible for bounds checking | decided |
| Scanner specification | `tobj_scan_int` | Pure `scanInt` / `scanDigits` model in `Obj/Spec.lean`: leading space and tab, optional sign, decimal digits, positive magnitude saturation at `INT_MAX`, and exact success/failure cursor behavior; digit/nondigit step lemmas, exact maximal digit-prefix count, folded magnitude, accumulator/count bounds, and whole-scanner exact value-fold/range/cursor plus failure value/cursor contracts support the loop; `scanInt_delimiter_failure` and its indexed form prove the pure `(false, 0, whitespace-count)` result for a first nonspace non-sign nondigit, regardless of trailing bytes; `scanInt_delimiter_refines_model` pairs that result with the translated `callFunc` failure result for the same buffer, including high bytes, and preserves a valid separate output block while committing only the whitespace cursor. The abstract C `(value, saturated)` update preserves the cap invariant and its fold over a maximal digit prefix computes the same value as the pure saturating fold (`scanCLoopStep_*`, `scanCLoopFold_*`); `scanCLoopFold_scanDigits` connects its initial state `(0, false)` directly to the recursive scanner. Translated `callFunc` results are kernel checked against the model for signed input, tabs, offsets, saturation, empty input, and non-digit failure (`Obj.Tests.ObjMiniC25`). The generated loop body is checked for every digit at accumulator 12, at `214748364` (with results compared directly to `scanCLoopStep`), and after saturation at `INT_MAX`. Range-proved typed i64 multiply/add and ASCII cast/subtract lemmas compose into an `EvE` proof of the generated accumulator expression and an `ExS` proof of its local assignment; `scanLoop_ast_factor` confirms the factored expression is definitionally the one in `Gen.tobj_scan_int_loop0`. `scanLoopStateAt` models an arbitrary byte block and cursor; `scanLoop_load_byte_at` proves an indexed byte loads from that state, and `scanLoop_digit_guard_at` proves the generated short-circuit guard succeeds for an ASCII digit at any cursor below its endpoint. `scanAccumulatorExpr_eval_at`, `scanAccumulatorAssign_exs_at`, and `scanLoop_accumulate_and_saturate_at` lift the arithmetic/cap transition to arbitrary buffers. These compose in `scanLoop_digit_iteration_at`, which proves one complete generated body iteration for any in-range scanner state and ASCII digit, including saturated and unsaturated cases. `scanLoop_takeWhile_digits` and `scanLoop_takeWhile_boundary` connect the explicit invariant to the pure maximal `takeWhile scanDigit` prefix; `scanLoop_takeWhile_count` proves this prefix length is the count returned by pure `scanDigits`. The postcondition form of the decreasing-loop proof preserves the break state. `scanLoop_terminates_takeWhile` proves termination and the final cursor/count relation for arbitrary byte buffers, including signed i8 exits at 128–255; its fold invariant also identifies the final `(value, saturated)` pair with `scanCLoopFold`. The zero-initial-state corollary `scanLoop_terminates_takeWhile_zero` proves the translated digit loop's final value and cursor equal `scanDigits`'s result. The new `scanLoop_digit_guard_state_at`, `scanAccumulatorExpr_eval_state_at`, `scanLoop_accumulate_and_saturate_state_at`, and `scanLoop_digit_iteration_state_at` preserve arbitrary scanner-frame locals through each digit transition. `scanLoopFrameAt`, `scanLoop_terminates_prefix_in_frame`, and `scanLoop_terminates_takeWhile_in_frame` prove termination from a real scanner frame at the maximal digit boundary, with the pure digit count and folded magnitude while retaining caller parameters and sign. `scanInt_successValue_eval_state` proves that the signed i64 magnitude selected after the loop casts to the corresponding wrapped i32 output value. `scanInt_successStores_exs` proves the generated output store, caller-pointer store, and true return compose when given the two store results; `scanInt_successRest_exs` composes those stores with the generated loop and preceding scratch-local initialization statements. The generated leading-space loop has the parallel `scanSkipSpace_terminates_takeWhile` proof, which reaches the maximal space/tab prefix boundary for arbitrary byte buffers (high bytes exit as non-space under signed i8 promotion). `scanIntSuccessPacked_load` and `skipSpacePacked_store_with_output` prove the helper’s packed cursor load and store in the scanner’s two-block layout. `skipSpacePacked_body_with_output` composes those with `scanSkipSpace_terminates_takeWhile`, whose state now accepts a memory frame, proving the full helper body while preserving output block 21. `scanInt_setup_after_whitespace_exs` composes that body with the scanner call and reload of `*pp`, proving local 3 points at the first non-space byte. The newer `scanIntActualPackedMem` layout treats block 20 as the complete packed buffer: `scanInt_actual_output_store` and `scanInt_actual_cursor_store` prove that both success stores are defined and that committing the cursor retains bytes after the pointer cell. `scanInt_successRest_actual_packed_exs`, `scanInt_success_after_framed_loop_actual_packed_exs`, `scanInt_success_after_digit_check_actual_packed_exs`, and `scanInt_success_no_sign_from_cursor_actual_packed_exs` compose a real no-sign success path with no contradictory memory premises. `skipSpacePackedBlock_drop` relates the helper’s packed buffer after the pointer cell to the raw input suffix. `scanInt_success_body_ast` identifies the factored success path with the generated scanner AST, and `scanInt_success_no_sign_after_whitespace_exs` now composes helper call, cursor reload, initial checks, no-sign branch, digit loop, and stores for a raw input whose first non-space byte is a digit. This proves the full no-sign success path, including the committed cursor and output memory. The corresponding signed success path is composed below; the remaining scanner work is to unify the success and failure contracts and extend failure calls to arbitrary starting offsets. Older `scanIntSuccessPackedMem` suffix lemmas still conflate raw and packed buffers and should be retired or repaired before reuse. `Obj.Tests.ObjMiniC28` executes the complete translated `tobj_skip_space` on finite inputs. `Obj.Tests.ObjMiniC29.skipSpacePacked_refines` proves its full body and `callFunc` result symbolically for arbitrary byte buffers under the MiniC 32-bit pointer-offset bound, using one block with the pointer cell at offset 0 and the scanned bytes after it; the body proof is exposed for reuse. `scanInt_whitespaceOnly_fails` composes the symbolic helper body proof into the scanner's all-whitespace early-failure branch from any valid starting offset in the original buffer: it returns false, advances the pointer cell to the endpoint, and preserves a valid separate output block; its pure tuple uses the absolute endpoint cursor. `scanInt_signGuard_at` evaluates the generated optional-sign guard and exposes the individual plus/minus comparisons for any ASCII byte at an arbitrary in-bounds scanner state; `scanInt_signGuard_any_at` extends this to every `UInt8`, including high bytes after signed i8 promotion. `scanInt_signBranch_ast` proves that the modeled branch is definitionally the branch selected from `Gen.tobj_scan_int.body`; `scanInt_signBranch_at` proves a `+` or `-` updates the sign local correctly, advances the cursor, and preserves memory. `scanInt_delimiter_fails` composes the guard at both sign-check points to prove the adjacent non-sign, non-digit failure path for every `UInt8` that is neither `+` nor `-` nor a decimal digit at the first non-space position, including bytes 128–255: sign handling leaves the cursor in place, the translated digit predicate rejects it, the scanner returns false, only the whitespace cursor is committed, and a valid separate output block is preserved. `scanInt_signOnly_end_failure_at` proves that a lone sign at the endpoint takes the generated short-circuit failure check while preserving memory and leaving the output untouched. `scanInt_loneSign_fails` composes this with the symbolic whitespace helper for any all-space/tab prefix followed by `+` or `-`: it returns false and commits the caller pointer just past the whitespace prefix, preserves a valid output block, and includes the pure tuple from `scanInt_lone_sign_failure`; the sign is consumed only by the scanner's local cursor. `scanInt_signDelimiter_fails` covers either optional sign followed by a non-digit byte and any trailing suffix under the MiniC pointer-offset bound: the generated sign branch advances its local cursor, the translated digit predicate rejects the next byte, the failure return leaves `*pp` at the post-whitespace position, a valid output block is preserved, and the theorem includes the pure tuple from `scanInt_sign_nondigit_failure`, confirming the trailing suffix is irrelevant. The actual packed-buffer success proofs now compose the whitespace helper and cursor reload through both no-sign and signed paths from raw bytes, including the digit loop and output/caller-pointer stores (`scanInt_success_no_sign_after_whitespace_exs`, `scanInt_success_sign_after_whitespace_exs`). Each theorem also establishes the corresponding pure `scanInt` success tuple for that input shape (`scanInt_no_sign_success_spec_from_bytes`, `scanInt_signed_success_spec_from_bytes`), now from an arbitrary valid input offset. `scanInt_success_no_sign_after_whitespace_callFunc` and `scanInt_success_sign_after_whitespace_callFunc` lift both body proofs through `callFunc`, including return value and final memory. The success contract is established for every successful input shape, and the failure contract now covers every input whose pure scan fails. `scanInt_delimiter_refines_model` connects the translated and pure results for the first-nonspace delimiter failure. `scanIntFailureShape` classifies the four concrete failure shapes; `scanInt_pure_failure_has_shape` proves every pure failure has one of them, and `scanInt_failure_refines_model` composes the classification with all translated branches to prove the failure `callFunc` result and pure tuple for arbitrary byte inputs under the valid output-block and pointer-offset bounds. `scanInt_failure_refines_model_of_failure` accepts an arbitrary pure false-result tuple and derives its canonical zero value and whitespace cursor. `scanInt_pure_failure_has_shape_at` classifies the suffix after any pure-model starting offset. `scanInt_whitespaceOnly_fails` now proves the translated all-whitespace failure from a nonzero pointer in the original backing block; the sign and delimiter failure branches still need that offset generalization. | success paths by input shape and arbitrary-input failure refinement proved; unified outcome theorem and arbitrary failure offsets remain |
| Spec ↔ C refinement | `tobj_tess_emit`, `tobj_tess_fan` vs `Obj.fanTris` | `emit_exs` (`Obj/C/Proofs/ObjTessEmit.lean`): the translated emit writes one `(a,b,c)` triple at slot `k` of a `u32` array and increments the counter cell, for any block layout satisfying the stated bounds. `tess_fan_refines_spec` (`Obj/C/Proofs/ObjTessFan.lean`): for any `n ≥ 3` the translated fan leaves the output block equal to the original with `triBytes` of every `fanTris n` triangle written from slot `k0` (`fanBlock_eq`), advances the counter by `n-2`, terminates without UB, and leaves all other blocks untouched | done (symbolic, arbitrary buffers) |
| Spec ↔ C refinement | `tobj_memcpy`, `emit_face_core_f` | `memcpy_exs` (`Obj/C/Proofs/ObjMemcpy.lean`): byte loop copies `n` bytes between distinct blocks (`splice dblk doff ((sblk.drop soff).take n)`), returns `dst`, touches nothing else. `emit_face_core_f_exs` (`Obj/C/Proofs/ObjEmitFace.lean`): for any layout satisfying the table/bounds hypotheses (`EfTab`), the translated function returns 1, writes `efBytes` (the selected 12-byte corner records) at `oo + 12*count0`, advances `*out_count` by `3*ntri`, no UB, other blocks untouched; `efBytes_eq_emitTris` identifies the bytes with the pure `Obj.emitTris`; `emit_face_core_f_cap_fail`: capacity overflow returns 0 with memory unchanged. The production `emit_face` now routes its triangulated corner copy through this core | done (symbolic, arbitrary buffers; `_d` variant is textually identical) |
| Spec ↔ C refinement | `tobj_fmt_uint` (writer core, `tobj_write_core.inc`) vs `Obj.decDigits` | `fmt_uint_exs` (`Obj/C/Proofs/ObjFmtUint.lean`): when the digits fit, the translated formatter returns the digit count, writes exactly `decBytes v` (= `decDigits v`) at the buffer offset and touches nothing else; `fmt_uint_fail`: too-small capacity returns 0, memory unchanged; `fmt_uint_scanInt`: the written bytes scan back to the same number through the pure scanner model. `tobj_write.c` uses this core for all integers | done (both digit loops, arbitrary buffers) |
| Spec ↔ C refinement | `tobj_scan_int` in the cursor layout; `parse_corner_n_f` vs `Obj.parseCornerN` | `Obj/C/Proofs/ObjScanIntCursor.lean`: `scan_int_cursor_failure` / `scan_int_cursor_success` (every input and offset agrees with pure `Obj.scanInt`: flag, committed `*pp`, i32 value stored to `*out`, other memory untouched; includes the saturating digit loop `sd_loop` and sign handling). `Obj/C/Proofs/ObjParseCorner.lean`: `parse_corner_n_f_refines` — for counts below 2^31 the C function returns the pure `ok` flag and writes exactly the pure `(vertex, normal, texcoord)` indices (all four forms `v`, `v/vt`, `v//vn`, `v/vt/vn`, malformed and out-of-range included); composes `tobj_cur_init`, the scanner, `fix_index_f_refines` and the optional `/vt`, `/vn` scans. **Both proofs are slice-general:** the cursor end is an arbitrary `e ≤ bytes.length` and the pure scanner/parser read `(bytes.take e)`, so a token held inside a larger input block (not just a dedicated block) is covered; passing `e = bytes.length` recovers the whole-buffer statement | done |
| Differential check | Lean parse model vs C loader | `formal/tools/objdiff.sh` runs `formal/ObjDiff.lean` (`Obj.parseObj`) and `tests/obj_dump.c` (tiny_obj_c, no triangulation) on `models/*.obj` and diffs face/index/smoothing-group/shape-name dumps: every model up to ~170 KB (61 files incl. `chr_knight.obj`) matches exactly, 5 are rejected by the C loader by design (invalid inputs); the 55-74 MB models (`living_room.obj`, `dragon.obj`) are not compared whole because the list-based Lean model does not scale to them; their first 60 000 lines (~1.9 MB each, cut at a line boundary) do match exactly | done |
| Writer float formatting | `tobj_write_real.inc` | libc-free, allocation-free `double` formatter: exact big-integer scaling, 17 significant digits (the classical binary64 round-trip bound), `%g` layout. Replaces `snprintf("%.17g")`. Validated byte-identical to `%.17g` on a 20-value corpus and 400 000 random doubles all round-trip; `tests/write_tester.c` passes under ASan+UBSan | done (validated, not refined) |
| Writer formatting model | `Obj/Real.lean` | pure `f64Parts`/`f64Rat` decode, `DecLit`/`DecLit.value`, `RoundsTo`; kernel-checked decomposition against the C behaviour in `Obj.Tests.FmtReal` | model done; the step "C digits satisfy `RoundsTo`" and the interval-uniqueness number theory are **open** |
| Writer validation | `tobj_write.c` | `tests/write_tester.c` loads, writes, reloads and compares scenes (raw and triangulated, all four corner forms, relative indices, corpus models), checks write idempotence and the Lean example byte-for-byte; build line in the file header; passes under ASan+UBSan | done |
| Unified scanner theorem | `tobj_scan_int` | `scanInt_success_shape` and `scanInt_refines_model` (end of `Obj/Tests.lean`): for any input at offset 0, a single theorem split on the pure `scanInt` flag gives value 0 + whitespace cursor + exact final memory on failure, and the wrapped i32 value + cursor-in-pointer-cell on success | done; `scanInt_refines_model_at` extends it to every start offset (all four failure shapes ported) |
| Spec ↔ C refinement | `tobj_skip_space`, `tobj_next_token` in the loader's cursor-struct layout vs `Obj.nextToken` | `Obj/C/Proofs/ObjNextToken.lean`: `skip_space_exs` (cursor cell ends at `skipStop`), `next_token_none` / `next_token_some` (return value, stored token start/length, cursor at token end, other blocks untouched) and `nextToken_eq` (the offsets are exactly `Obj.nextToken`) for arbitrary byte buffers and start offsets; the cursor end is an arbitrary `e ≤ bytes.length` and the pure side reads `(bytes.take e)` (slice-general); reusable `isSpace_call`, packed-pointer cell load/store lemmas, `tw_inside`/`tw_boundary` | done |
| Token scanner refinement (earlier, finite) | `tobj_next_token` | Pure `nextToken` / `nextTokenBytes` models leading spaces/tabs, maximal non-space run, length, cursor at token end, and no token output on failure; success contracts prove nonempty output, returned start after the leading whitespace prefix, cursor equals start plus length, returned length equals the slice length, and token bytes contain no whitespace. `nextTokenBytes_boundary` proves that when the token ends before the suffix, its next byte is whitespace. Translated executions are kernel checked against the spec for token, whitespace-only input, and nonzero start (`Obj.Tests.ObjMiniC26`). MiniC pointer subtraction models same-block `ptrdiff_t` results and rejects cross-block subtraction; both cases have kernel checks | spec properties and finite examples done; general refinement proof pending |
| Kernel tests | `parse_corner_n_f` (the `v[/vt][/vn]` corner parser) | `Obj.Tests.ObjMiniC24`: eight kernel-checked tokens (`1`, `1/2/3`, `1/2`, `1//3`, `-1/-2/-3`, `0`, out-of-range `5` and `-5`) checked against `Obj.storedIndex` for the stored indices and the return flag | done (tests, not a general proof) |
| Invariant proofs | `fix_index_f` zero and out-of-range cases | `fix_index_f_zero` (0 → stores -1, returns 0), `fix_index_f_oob` (negative index before array start → stores -1, returns 0) (`Obj/C/Proofs/ObjFixIndex.lean`) | done |
| Spec ↔ C refinement | `tobj_orient2d` (float arithmetic) | `tobj_orient2d_refines` (`Obj/C/Proofs/ObjOrient2d.lean`): for any three `double[2]` points held as 16-byte records, the translated body returns exactly the pure bit-level `orient2dGen` = `add(mul(b0-a0, c1-a1), neg(mul(b1-a1, c0-a0)))`, using the correctly-rounded `F64` model. First complete floating-point refinement in the development; the n=3/n=4 branches of `tobj_tess_polygon_core` call this function. Supporting lemmas: `load_f64_at`/`load_f64_splice` (double loads), `index_const0`/`index_const1` (double-array indexing), `evalBin_f64_{add,sub,mul}`, `evalUn_f64_neg` | done (symbolic, arbitrary bit patterns) |
| Spec ↔ C refinement | `tobj_dabs`, `tobj_tess_scale2d` | `tobj_dabs_refines` (`Obj/C/Proofs/ObjDabs.lean`): the translated `x < 0.0 ? -x : x` returns the pure bit-level `dabsBits` for any bit pattern, incl. `dabs(-0.0) = -0.0`. **`tobj_tess_scale2d_refines`** (`Obj/C/Proofs/ObjScale2d.lean`): the translated scan returns `scaleFold g 0 n` (the fold of `f64Max` over `|p2d|`) for a `double[2n]` array, via `ScaleInv` + `ExS.loop_decreasing_post`, and never writes memory | done |
| Semantics | fma (MiniC model) | `Expr.fma` + `F64.fmaBits` in `Obj/C/Semantics.lean`: IEEE-754 `fusedMultiplyAdd` (exact `a*b + c`, one rounding). x86-64 FMA3 `vfmadd*sd` and AArch64 `fmadd` implement the same IEEE operation, so a single model covers both. `c2lean.py` maps `fma`/`__builtin_fma` to `(.fma ...)` and passes `-ffp-contract=off` (clang otherwise contracts on AArch64 but not x86-64). C: `TOBJ_TESS_FMA` (default off) in `tobj_orient2d`/`tobj_tess_signed_area`; default-off path is bit-identical to the original expression. `Obj.Tests.ObjF64` pins ~17 `math.fma` vectors | done (model + opt-in C use) |
| Semantics | `double` arithmetic (MiniC model) | `namespace F64` in `Obj/C/Semantics.lean`: correctly-rounded IEEE-754 binary64 add/sub/mul/div/neg on bit patterns, via exact `Rat` decoding and ties-to-even rounding; IEEE NaN/±inf/±0 rules. `binF64` and `evalUn .neg` use it; `evalBinInt` dispatches float ops on operand type. `Obj.Tests.ObjF64` pins ~30 vectors by `decide +kernel` (incl. `0.1+0.2`, `1/3`, `2^53+1`, subnormals, overflow, signed zero, and 10 `tobj_orient2d` corpus values) | done (4 ops + neg; no `fma`/`sqrt`, which the C core does not use) |
| Invariant proofs | the rest of the verified core | not yet proven at the invariant level; heavier proofs (loops, mutation, monkeys' of memory) require further work | todo |
| Spec layers | mesh construction, triangulation contract, writer | pure specs and theorems in `Obj/Mesh.lean`, `Obj/Tess.lean`, `Obj/Write.lean` (above), no `sorry`. `Obj/Tess.lean` also specifies the polygon-core small-polygon branches: `polyTri` (n=3), `quadTris split02` (n=4), `polyTris`, with `TessValid` proofs, `polyTris_length`/`polyTris_corners`, and the emission lemmas `emitTris_polyTri`/`emitTris_quad02`/`emitTris_quad13`; kernel-checked tests in `Obj.Tests.ObjTessEmitK` confirm the translated `tobj_tess_emit` writes exactly these bytes | done at spec level; `emit_face_core_f` done; MiniC refinement of `tobj_tess_polygon_core_f` n=3/n=4 is now *unblocked* (f64 arithmetic is modelled) and remains proof work |
| End-to-end | full parser (`tiny_obj_load_*`) & tessellation refine the spec | blocked on spec + on verified-core coverage (allocation-heavy functions still translated only after refactoring into allocation-free cores) | todo |

Alignment with the C source matters: `c2lean.py --check` fails if
`Obj/C/Gen.lean` drifts from `tiny_obj_verified.c`. After changing any of
the 59 C functions, re-run `python3 tools/c2lean.py` and `lake build`.

## Verification-friendly refactorings in C

* `tobj_tess_scratch_size` now includes `tobj_tess_align(sizeof(tobj_tess_work), 16)` in the total so the bound it passes to callers covers the work-struct prefix.
* `tobj_dabs` compares with `0.0` (avoids an unused `IntegralToFloating` path in the translator).
* `tobj_tess_run2d` splits `++guard` into `guard += 1;` for translation.
* `emit_face_core_f/d` (new, `tiny_obj_c_impl.inc`) copies mapped triangle
  corners into a caller-provided output array without allocation or builder
  mutation — same output as the triangulating path of `emit_face`, but a
  translation-sized step.
* `tobj_tess_polygon_core_f/d` (new, `tobj_tess_impl.inc`) is an
  allocation-free variant of `tobj_tess_polygon` taking pre-resolved output
  and scratch buffers; the tessellation pipeline itself remains verified only
  via the pure helpers it calls.
* `tobj_tess_project_f/d` no longer uses a local array for `mn`/`mx`/`span`
  (individual locals instead).
* Full `emit_face_f` / `tobj_tess_polygon_f` remain blocked for MiniC:
  allocation, struct aggregates, address-of locals, function pointers and
  floating-point conversion still require larger translator extensions or
  hand-verified proofs.

## Layout

| File | Contents |
|---|---|
| `Obj/Basic.lean` | `F64` (IEEE-754 doubles as bit patterns, with C comparison semantics), byte strings, index helpers |
| `Obj/Model.lean`, `Validate.lean`, `Safety.lean`, `Glb.lean`, `B64.lean` | **inherited** glTF spec and proofs (kept; still build; not the OBJ loader spec) |
| `Obj/Tess.lean` | pure triangulation contract: `fanTris`, `TessValid` (exactly `n-2` triangles, indices `< n`), `emitTris`; fan validity/distinctness theorems |
| `Obj/Mesh.lean` | pure parse + mesh-construction model: `parseCornerN` (all `v`, `v/vt`, `v//vn`, `v/vt/vn` forms, with relative/out-of-range handling), `tokens`/`splitLines`, `parseTokens`/`parseObj` (v/vt/vn/f/g/o/s/usemtl, `finalize_shape`, optional triangulation). Theorems: `parseCornerN_ok`, `parseCornerN_neg_vertex`, `parseObj_wf` (every emitted shape has `fv.sum = idx.length`, equal per-face array lengths, every face ≥ 3 corners, indices ≥ -1), `emitFace_triangulates` (a valid tessellator turns an n-gon into exactly `n-2` triangle faces). Abstractions (documented in the file): float payloads are raw tokens, no allocator/caps/MT, tessellator is a parameter |
| `Obj/Write.lean` | pure `.obj` writer `writeObj` and its round trip. `decDigits`/`scanInt_decDigits` (decimal formatting reads back through the scanner), `parseCornerN_fmt` (corner formatting round-trips for every writable corner), `parse_write`: `parseObj tess mats false (writeObj mats vs vts vns shapes) = shapes` under explicit well-formedness hypotheses (`ShapeOk`, token validity, material-lookup consistency `MatOk`, indices and smoothing groups below `INT_MAX`). The C writer `tobj_write.c` follows this format (see `tests/write_tester.c`) |
| `Obj/Tests.lean` | kernel-checked regression tests (inherited glTF examples + `Obj.Tests.ObjMiniC`) |
| `Obj/C/Semantics.lean` | MiniC: syntax, values, byte-addressed memory, executable big-step semantics with explicit UB |
| `Obj/C/Gen.lean` | **generated** from `tiny_obj_verified.c` by `tools/c2lean.py` — do not edit |
| `Obj/C/Logic.lean`, `Hoare.lean` | proof rules (`EvE`, `ExS`, total-correctness triples), all derived from the semantics |
| `Obj/C/Lemmas.lean` | arithmetic / byte-encoding lemmas for symbolic execution |
| `Obj/C/Splice.lean` | byte-range rewrite algebra used by the writer (`splice*`, `read_*`, `store_int`) |
| `Obj/C/Proofs/*.lean` | invariant proofs (`ObjIsSpace`: space/tab/other incl. `toInt_i32_wrap_i8`, `evCast_i8_i32`; `ObjIsDigit`: ge/lo/hi; `ObjIsPow2`: zero/eight/six; `ObjFixIndex`: fix_index_f_pos/neg/zero/oob); `FixIndexRefines`: spec refinement; `Obj/Spec.lean`: pure OBJ index spec |
| `CDiff.lean`, `tools/cdiff*.{py,c}` | **inherited** three-way differential driver (glTF-specific; does not apply here) |

## What is trusted

A proof here is a statement about the MiniC semantics of the C source, so
the trusted base is:

* **the Lean kernel**;
* **the MiniC semantics** (`Obj/C/Semantics.lean`). Every operation that is
  undefined in C11 and can occur in the subset is `ub`: signed overflow,
  division by zero, oversized shifts, out-of-object loads, stores and pointer
  arithmetic, reading an uninitialised local. Memory is little-endian and byte
  addressed. Not modelled: strict aliasing, alignment, `volatile`, concurrency;
* **the translator** `tools/c2lean.py` and **clang's front end** (types and
  implicit conversions come from clang's AST; record layouts are measured by
  compiling a probe with the same compiler). The translator rejects anything
  outside the subset instead of guessing;
* **the target**: proofs assume an LP64, little-endian ABI (x86-64,
  AArch64, RISC-V 64 in practice) — the layout the probe measured;
* **the C compiler**: there is no link to compiled machine code.

There is no differential test runner for the OBJ core yet; `lake build`
(kernel-checked examples and proofs) plus `c2lean.py --check` are the
Lean-side validation. The C side is validated by the project's own suites,
which exercise the refactored verified-core code paths:

* `tests/tester_c` (pure C11 loader, acutest) — **SUCCESS: All unit tests have passed.**
* `tests/tess_tester` (tessellator unit/property tests, incl. ASan/UBSan) — **SUCCESS: All unit tests have passed.**
* `tests/tester_c_freestanding` (-ffreestanding, TOBJ_NO_LIBC) — links and exits 0.

### Scanner success-path progress

The packed success store path now has symbolic memory proofs for both writes:
`scanInt_success_output_store` writes the i32 value in block 21 while
preserving block 20, and `scanInt_success_cursor_store` commits the cursor to
the pointer cell in block 20 while preserving the output. The fold lemmas
`scanIntFold_le_cap` and `scanCLoopFold_zero_le_cap` bound the loop accumulator
from its zero initial state. `scanInt_sign_negative_eval_state` evaluates the
generated sign comparison, and `scanInt_successRest_packed_exs` combines the
loop and both stores in the exact success suffix. The framed-loop composition
`scanInt_success_after_framed_loop_packed_exs` derives the final cursor,
magnitude bound, sign/value locals, and packed-memory stores from the general
digit-loop termination theorem. The full wrapper success paths are now composed for both optional-sign
branches and connected to their pure scan tuples. `scanLoop_digit_call_true_at` proves the translated
digit predicate returns true for an in-range ASCII digit;
`scanInt_success_after_digit_check_packed_exs` composes that result with the
false failure guard and the framed loop. `scanInt_success_no_sign_packed_exs`
and `scanInt_success_after_sign_packed_exs` cover the no-sign and consumed-sign
branches through the same success suffix. `scanInt_success_no_sign_from_cursor_packed_exs`
also composes the initial cursor-at-end check and `sign = +1` initialization
with the no-sign success path. The complete whitespace/call setup and the
`scanInt_success_sign_from_cursor_packed_exs` does the same for a consumed `+`
or `-` followed by a digit. The complete failure refinement now covers the
all-whitespace, lone-sign, sign-delimiter, and generic delimiter cases for
arbitrary bytes; the success/failure theorems are not yet unified into one
result theorem.

## Design notes

* Doubles are bit patterns (`F64`) with comparison defined on the bits
  (`F64.key`), so comparisons are decidable and NaN fails every range check,
  exactly as in C.
* Loops in translated functions are hoisted into named `Stmt` definitions
  (`…_loopN`) so proofs can reason about them separately.
* `memcmp`/`strlen` are modelled by `Expr.memcmp`/`Expr.strlen` with their
  C-standard semantics.
* Pointers stored in memory are modelled as the packed pair
  `(block, offset)` in 8 bytes (`ptrPack`/`ptrUnpack`); the verified core
  never round-trips a pointer through integer representation.
* Expression-level calls run in a read-only mode (stores are UB); the
  translator only emits them for functions that do not write memory, and the
  semantics enforces it.


## Independent tess certificates

The standalone `lib/tess` project reuses this MiniC semantics and `c2lean`
translator. Its separate `Tess` target proves exact artifact checker soundness
for fixed and subdivided graph remeshing, while `tesscheck` checks actual emitted
certificates. This is distinct from the existing loader-refinement work above.
See [the proof-to-code matrix](../lib/tess/docs/PROOF_MATRIX.md) and
[certificate commands/trust boundary](../lib/tess/docs/CERTIFICATES.md).
Run `python3 formal/tools/check_tess_proofs.py` from the repository root for
regeneration freshness, kernel build and the complete Tess axiom dependency audit.

The `tesspredicates` executable supports bounded exact-rational predicate
fixtures for direct C/Lean/Fraction comparison. Build with
`lake build Tess tesscheck tesspredicates`. Segment membership and closed
intersection both have rational and real equivalence theorems, including
zero-length and collinear cases. The exact 3D orientation is also a light
executable definition whose cast, coplanarity and `planeValue` identities are
proved separately. Strict 3D plane cuts likewise have exact rational
interpolation and plane-zero theorems, while the no-mixed-sign 2D containment
test covers either face orientation. These are not refinements of the full
C auditor. The indexed shared-simplex exceptions are
proved separately: with disjoint endpoint IDs, `segmentConflict` is equivalent
to closed geometric intersection, while identical indexed edges are expected
shared simplices. See
[predicate validation](../lib/tess/docs/PREDICATE_VALIDATION.md).

## Tess (`lib/tess`) formalization overview

`Tess*.lean` formalize the exact C11 n-gon remeshing library in `lib/tess`. The authoritative claim-by-claim
table (what is proved, what is only differentially validated, and the trust boundary) is
[`lib/tess/docs/PROOF_MATRIX.md`](../lib/tess/docs/PROOF_MATRIX.md); the audited declaration count and
verification runs are in [`lib/tess/STATUS.md`](../lib/tess/STATUS.md). Reproduce with
`python3 formal/tools/check_tess_proofs.py` (generation freshness, kernel build, axiom audit).

Layers:

1. **Certificate soundness** (`Check`, `Validity`, `Validity2`, ...): an accepted V1/V2 certificate implies
   coverage, embedding, feature preservation and the height bound.
2. **MiniC refinements of translated C kernels** (`Tess/C/*`, generated `LimbGen.lean`): limb multiply-add,
   magnitude, `acmp`, `zi_cmp`, the add/sub/mul loops, `trim_len`, `dbl_decode`, `i64_limb_count`/`i64_fill`.
   Kernels that needed factoring out of allocating functions are marked in `exact.c`.
3. **Functional models** of the allocating arithmetic (`ZiModel`, `QrModel`, `DivModel`, `ShiftModel`,
   `PredModel`, `SegModel`, `ZiCmp`): they denote integer/rational arithmetic and the exact predicates; they are
   tied to the C only through layer 2 and differential tests (the MiniC subset has no allocator).
4. **Auditor pair decision** (`PairAudit*`, `NoncoplanarComplete`, `InPlane`, `CoplanarSharedEdge`,
   `SharedVertex`, ...): an executable specification of the C 3D auditor with soundness (accepted pairs meet only
   in the permitted shared simplex), completeness (rejections are genuine) for all configurations of 0/1/2 shared
   vertex IDs where stated.

Validation that complements the proofs (C/Lean/Fraction differential, mutation check, sanitizer runs) is
described in `lib/tess/docs/PREDICATE_VALIDATION.md`, `lib/tess/tools/mutation_check.py` and `lib/tess/STATUS.md`.
