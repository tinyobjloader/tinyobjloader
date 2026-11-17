# AGENTS.md

Guidance for AI coding agents (Claude Code, Copilot, Cursor, etc.) working in this repository.

## Project Overview

tinyobjloader is a Wavefront `.obj` / `.mtl` loader. It is deliberately not one
implementation: the repository ships several co-equal, independently usable ones,
and a change usually belongs in one of them, not all.

- `tiny_obj_loader.h` / `.cc` — the C++11 header-only loader (the historic API).
  Also contains `LoadObjOpt` / `LoadObjOptTyped`.
- `tiny_obj_c.{c,h}` + `tiny_obj_c_{pub,impl}.inc` — from-scratch **pure C11**
  loader. `_f` (float) and `_d` (double) families coexist. Freestanding-capable.
- `tobj_tess.{c,h}` — standalone robust polygon tessellator used by the C loader.
- `tobj_mtlx`, `tobj_subd`, `tobj_skel`, `tobj_write` — C11 sidecar support for
  MaterialX-in-MTL, subdivision tags, skeletons/skinning and canonical `.obj`
  writing.
- `web/` — WebAssembly build of the C11 loader + the `tinyobj` npm package.
- `python/` — CPython binding (`tinyobjloader` on PyPI).
- `formal/` — Lean 4 models that are the normative spec for the `C` sidecars.

No exceptions/exotic runtime requirements in the C layer; no libc in the core
when `TOBJ_NO_LIBC` is defined.

## Repository Layout

```
tiny_obj_loader.h/.cc        C++ header-only loader (+ LoadObjOpt)
tiny_obj_c.{c,h}             Pure C11 loader; _pub.inc/_impl.inc are the
                             per-precision bodies (included twice)
tobj_tess.{c,h} + .inc       Robust polygon tessellation
tobj_mtlx|subd|skel|write    C11 sidecar modules (MaterialX, subdivision,
                             skeletons, .obj writer)
tiny_obj_verified.c          Extracted/verified build of the loader
tests/                       C/C++ test harness (Acutest). Makefile drives
                             `make check`; fixtures under tests/ and models/
fuzzer/                      libFuzzer / AFL harnesses (+ fuzzer/afl.tar.gz)
models/                      Curated .obj/.mtl fixtures (85 tracked files)
examples/                    Standalone example apps (separate builds)
experimental/stream/         Streaming OBJ parser; USED by tests/ and fuzzers
formal/                      Lean 4 specs + proofs (Obj, Mtlx, Subd, Skel, Tess)
web/                         WASM build + npm package (package root)
python/                      CPython binding (setuptools + CMake)
blender/                     Blender add-on (skeletons, OpenSubdiv)
doc/                         Docs; doc/site/ is generated MkDocs output
lib/tess/                    Standalone C11 tessellation sub-project
mapbox/, deps/               Vendored third-party (earcut, cpplint)
sandbox/                     Scratch prototypes
```

## Build Commands

```bash
# C++ (header-only) example
make loader_example

# CMake (C++ lib + optional C library; C lib is ON by default)
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j

# C11 tests — this is the main gate for C changes
cd tests && make check            # default, features, nofastfloat, C suites
cd tests && make check_c          # C11 loader + tessellation only
cd tests && make check_mtlx       # / check_subd / check_skel for sidecars
```

`tests/Makefile` is the source of truth for how the C/C++ tests are compiled
(`-std=c11`, sanitizers on by default). C tests must be run from `tests/` because
they load fixtures via `../models/...`.

Key CMake options (see `CMakeLists.txt`):

- `TINYOBJLOADER_BUILD_C_LIBRARY` (default ON)
- `TINYOBJLOADER_C_ENABLE_FILE_IO` / `_MMAP` / `_SIMD` / `_MULTITHREADING`
- `TINYOBJLOADER_C_BUILD_TESTS` (default OFF; registers `tester_c`, `tess_tester`)

### WebAssembly / npm

```bash
cd web
./build.sh                 # needs emcc in PATH -> dist/tinyobj.{js,wasm}
npm run test:native        # native cc build of the ABI shim (no emscripten)
npm test                   # node, against the built wasm
npm run test:browser       # headless Chrome demo check (CHROME_PATH overrides)
npm pack --dry-run         # expect exactly 7 files
```

The wasm build intentionally defines no `TOBJ_ENABLE_*` macros: it is the
default scalar, single-threaded, libc-backed configuration.
`web/scripts/prepublish-check.sh` runs on `prepublishOnly` and refuses to publish
a prerelease under the default `latest` tag.

## Coding Conventions

- C11 for the C loader (`-std=c11`, no GNU extensions); C++11 for the C++ loader.
- Both precision families (`_f` / `_d`) must stay in sync — the
  `tiny_obj_c_{pub,impl}.inc` files are included twice, so edits apply to both.
- Public C API lives in the `.h`; do not leak `static` helpers across TUs.
- No new libc dependency in the C core without an `#ifndef TOBJ_NO_LIBC` guard.
- Keep `formal/` Lean specs and the C implementations consistent; when a
  sidecar's format changes, update its `.md` spec (`mtlx-mtl.md`,
  `subd-obj.md`, `skel-obj.md`) in the same change.
- Vendored code (`deps/`, `mapbox/`, `formal/.lake/`, `*.h` from third parties)
  is not reformatted and its copyright notice is never altered.
- Do not add comments to code unless the logic is genuinely non-obvious.

## Testing

See `tests/README.md`. The CI gate is `.github/workflows/unit.yml`
(`cd tests && make check`), plus `tess.yml` for the tessellation sub-project and
`wasm-package.yml` for `web/`.

### Pre-merge checklist

Run the suites that match what you touched; when in doubt, run all of them.

```bash
cd tests && make check          # C/C++ loader + tessellation
cd tests && make check_mtlx     # if tobj_mtlx.* changed
cd tests && make check_subd     # if tobj_subd.* changed
cd tests && make check_skel     # if tobj_skel.* changed

cd web && ./build.sh && npm test && npm run test:native   # if web/ changed
cd web && npm run test:browser                            # if demo/ changed
```

Also confirm:

- `tests/` fixtures still resolve (they are loaded relative to `tests/`).
- Any new test asset is **tracked** — CI checks out only tracked files, so a
  test that reads an untracked model passes locally and fails in CI.
- Workflow YAML still lints (`actionlint .github/workflows/*.yml` if available).

## Security

- The loader parses untrusted input. Preserve bounds checks, size limits
  (`max_vertices`, `max_input_bytes`, ...) and the "never crash / never loop
  forever" guarantees of `tobj_tess`.
- Fuzzers live in `fuzzer/` (`fuzzer/fuzz_tobj_c.c`, `obj-fuzz`, `llvm-fuzz`).
  Keep them building when you change parse entry points.
- Do not add new `malloc`/`fopen` calls outside the existing allocator and I/O
  hooks; the freestanding path must keep working.

## Commit Style

Concise imperative subjects (e.g. "Fix relative index underflow"). Body explains
*why* when it is not obvious. One logical change per commit — if a commit message
needs "and" to describe two unrelated things, split it.

Default branch for PRs: `release`.

## Release / Versioning

Two independent release trains. They have separate version sources and separate
tag namespaces; do not mix them.

| | C++ / PyPI | npm (`web/`) |
| --- | --- | --- |
| Version source | `CMakeLists.txt` (`TINYOBJLOADER_VERSION`) / setuptools_scm | `web/package.json` |
| Tag pattern | `v*` (e.g. `v3.1.0`) | `npm-v*` (e.g. `npm-v2.0.0-rc.13`) |
| Workflow | `unit.yml`, `python.yml` | `npm-publish.yml` |

The npm workflow listens on `npm-v*` only, on purpose: the repo already has many
`v*` tags whose versions do not track the npm package, so a `v*`-triggered npm
release would fire on every C++/PyPI release and fail its version check.

Full procedure for both trains is in the **Developer guide** section of
`README.md`, and the npm specifics (trusted publishing, staged approval,
dist-tags) in `web/PUBLISHING.md`. Read those before bumping a version or
pushing a release tag.

Tagging an npm release, in short:

```bash
# web/package.json is the source of truth; the tag must match it exactly.
version=$(node -p "require('./web/package.json').version")
git tag -a "npm-v$version" -m "tinyobj npm $version"
git push origin "npm-v$version"    # NOT --tags: that would fire the v* train
```

The workflow stages the package via npm Trusted Publishing (OIDC) and a
maintainer approves it with 2FA (`npm stage approve <id>`). Nothing is public
until that approval. Dist-tags are derived from the version: a prerelease goes
to `next`, a stable release to `latest`.

## Git Push Policy (mandatory pre-push checklist)

Pushing rewrites shared state. Before **any** `git push` (regular, force, or
`--force-with-lease`), an agent must complete every step below. Skipping a step
is a defect — pre-push hygiene is one of the few places in this repo where "ask
first" beats "act first" by default, because once a 100 MB binary or a leaked
credential lands on `origin` it is forever in the public Git history.

### 1. Audit the commits about to leave the machine

Always inspect the exact range you are pushing — `git log --oneline
@{upstream}..HEAD` for a regular push, or `git log --oneline <remote-tip>..HEAD`
for a force/lease push — and run the four checks below against **every** commit
in that range, not just `HEAD`. Any single offending commit blocks the push;
resolve via `git rebase -i` (drop / edit) or `git filter-repo` (path removal)
before continuing.

If the branch has no upstream yet (a brand-new branch), there is no range to
diff against — audit `git log --oneline origin/release..HEAD` instead, and say so
explicitly when reporting results.

#### Check 1 — Credentials & sensitive data

Never push a commit that contains, or has ever contained at any point in its
history within the push range:

- API keys, bearer tokens, OAuth client secrets, AWS / GCP / Azure access keys,
  SSH private keys, PGP private keys, `.netrc`, `.env`, `.npmrc` with
  `_authToken` (npm publishing here uses OIDC, so **no token should ever be
  needed or committed**).
- Email/password pairs, JWTs, Slack/Discord/GitHub webhook URLs.
- Internal hostnames, VPN configs, customer asset paths that aren't already
  public.
- Personal user paths (`/home/<someone>/…`, `C:\Users\<someone>\…`) baked into
  source comments — embarrassing rather than dangerous, but still gets stripped.

How to check (run from the repo root, against the exact push range):

```bash
RANGE="$(git rev-parse --abbrev-ref --symbolic-full-name @{upstream})..HEAD"
# Added lines only, and a value of >=12 token characters is required, so
# `id-token: write` / `const char *token = ...` idioms do not trip it.
git diff "$RANGE" -- ':!**/*.md' ':!**/*.txt' | grep '^+' \
  | grep -niE 'AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|AIza[0-9A-Za-z_-]{35}|(api[_-]?key|secret|token|password|passwd|bearer|private[_-]?key)[[:space:]]*[:=][[:space:]]*["'"'"']?[A-Za-z0-9_+/.-]{12,}' \
  || echo "No credential-shaped strings found in $RANGE"
```

Two portability notes for this repo, both learned by running it:

- `-i` (not an inline `(?i)`) does the case folding — GNU grep's `-E` rejects
  `(?i)` with `warning: ? at start of expression` and silently matches nothing.
- Scanning only `^+` (added) lines avoids flagging *removed* code, and the
  12-character value requirement keeps YAML like `id-token: write` and C
  identifiers such as `const char *token = linebuf;` out of the results.

This is a heuristic, not a guarantee. If a commit touches anything that *talks*
to an external service (CI, package upload, asset server) eyeball the diff
manually too.

##### Automated secret scanners (run when available — preferred over the grep heuristic)

When `gitleaks` and/or `trufflehog` are installed, run them over the **same push
range** as a stronger, entropy- and rule-aware complement to the grep above.
They do not replace the manual eyeball — they catch what the regex misses. **Any
finding blocks the push** (resolve with `git rebase -i` / `git filter-repo`,
treat the secret as compromised, and rotate before doing anything else). If a
tool is missing, note that it was skipped and fall back to the grep heuristic.

```bash
# Same range as Check 1 (BASE..HEAD).
RANGE="${RANGE:-$(git rev-parse --abbrev-ref --symbolic-full-name @{upstream})..HEAD}"
BASE="$(git rev-parse "${RANGE%%..*}")"
REPO="$(git rev-parse --show-toplevel)"
BRANCH="$(git branch --show-current)"
# trufflehog's go-git backend can't read a *worktree* `.git` file, so point it at
# the main worktree directory (its `.git` is a real directory) and pick the
# branch explicitly. For a normal checkout this resolves to the repo root.
MAIN_WT="$(git worktree list --porcelain | awk '/^worktree /{print $2; exit}')"

# gitleaks — handles worktrees natively; scans exactly the commits in the range
# via `git log` options. Exit 0 = clean, non-zero = leaks (or error). --redact
# keeps any secret out of logs/stdout.
if command -v gitleaks >/dev/null 2>&1; then
  gitleaks detect --source "$REPO" --redact --log-opts="$RANGE" \
    && echo "gitleaks: clean over $RANGE" \
    || { echo "ABORT: gitleaks flagged secrets in $RANGE"; exit 1; }
else
  echo "gitleaks not installed; skipping (https://github.com/gitleaks/gitleaks). Rely on the grep heuristic above."
fi

# trufflehog — default binary at ~/go/bin/trufflehog, else PATH. Scans BASE..tip
# of $BRANCH; --fail exits 183 when results are found (verified live secrets +
# verification-errored). Add --only-verified for the lowest-noise gate.
TRUFFLEHOG="${TRUFFLEHOG:-$HOME/go/bin/trufflehog}"
[ -x "$TRUFFLEHOG" ] || TRUFFLEHOG="$(command -v trufflehog || true)"
if [ -n "$TRUFFLEHOG" ] && [ -x "$TRUFFLEHOG" ]; then
  "$TRUFFLEHOG" git "file://$MAIN_WT" --since-commit="$BASE" --branch="$BRANCH" --fail \
    && echo "trufflehog: clean over $RANGE" \
    || { echo "ABORT: trufflehog flagged secrets in $RANGE"; exit 1; }
else
  echo "trufflehog not installed; skipping (default path: ~/go/bin/trufflehog). Rely on the grep heuristic above."
fi
```

##### Proprietary asset names & personal paths — scan commit *messages*, not just the diff

The credential grep and the scanners above look at the code diff. Private
**asset filenames** (model/scene names, customer assets) and **personal paths**
leak just as easily through **commit messages** and **source comments** — e.g. a
perf note that says "model `PrivateScene_X.obj` took 57 s", or a comment
`// e.g. CustomerScene: 5273 faces`. Public history should describe *what*
changed in generic terms ("a ~500k-face scene", "a reference folder scene"),
never the private asset that exercised it. Run both scans over the push range:

```bash
RANGE="$(git rev-parse --abbrev-ref --symbolic-full-name @{upstream})..HEAD"

# (a) Personal paths in BOTH messages and source — must be empty.
{ git log "$RANGE" --format='%B'; git diff "$RANGE" -- '*.c' '*.h' '*.inc' '*.cc' 'web/*' 'python/*'; } \
  | grep -inE '/home/[a-z]|/Users/[A-Za-z]|C:\\Users\\' \
  && { echo "ABORT: personal path in messages or source"; } \
  || echo "clean: no personal paths"

# (b) Asset-filename tokens in messages + added source lines — EYEBALL each and
#     strip any that names a private/proprietary/customer asset. Generic names
#     (models/cube.obj, tests fixtures, bare extensions) are fine.
{ git log "$RANGE" --format='%B'; git diff "$RANGE" -- '*.c' '*.h' '*.inc' '*.cc' 'web/*' 'python/*' | grep '^+'; } \
  | grep -oiE '[A-Za-z0-9_-]{3,}\.(obj|mtl|mtlx|png|jpg|jpeg|exr|hdr|blend|fbx|gltf|glb)' \
  | sort -u
```

Any private asset name → rewrite before pushing. Messages:
`git filter-branch --msg-filter '…'` (or `git filter-repo --replace-message`;
`git rebase -i` if your harness allows it — some sandboxes block `-i`). Source
comments: edit + `git commit --amend` / rebase. **Re-run every Check 1 scan
(incl. the scanners) after the rewrite — the commit hashes change.**

#### Check 2 — No build artifacts

Build outputs do not belong in Git. They explode the pack size, cause merge
conflicts on every rebuild, and routinely contain absolute paths from the
developer's machine. If you find any of these in the push range, drop the file
(and ignore the path going forward).

This repo is especially prone to it, because several build paths dump objects
and binaries *next to the sources* rather than into a single `build/` tree. The
common culprits:

- `*.o`, `*.a`, `*.so`, `*.dylib`, `*.dll`, `*.lib`, `*.exe`, `*.d` — compiled
  objects and dependency files (`tiny_obj_loader.o`, `tobj_*.o`,
  `obj/native/Release/*`, `bin/native/Release/*`).
- `build/`, `build-mtlx/`, `build-osd/`, `_codeql_build_dir/` — build trees.
- `*.ninja_deps`, `*.ninja_log`, `build.ninja`, `compile_commands.json` —
  ninja/CMake state (root `build.ninja` is tracked source; the *generated*
  `tests/build.ninja` is not).
- `*.make`, `*makefile` files emitted by premake (`objview.make`,
  `obj_sticher.make`, `tinyobjloader.make`) — generated, not source.
- `dist/`, `*.egg-info/`, `__pycache__/`, `*.pyc`, `node_modules/`.
- `web/dist/tinyobj.{js,wasm}` — generated by `web/build.sh`; gitignored, and
  `web/package.json`'s `prepack` rebuilds them for npm.
- `*.whl`, `*.tar.gz`, `*.tgz` produced by packaging runs.
- `a.out`, `tester*` / `tess_tester` / `obj_dump` build products in `tests/`,
  `loader_example`, `perf.data`, `log`.

Run from the repo root:

```bash
# NOTE: `obj` here means *build-output directories*, not `.obj` models. Anchor
# on `obj/` (a directory) so tracked fixtures such as `models/cube.obj` and
# `formal/Skel/tests/*.obj` do not trip the check.
git diff --name-only "$RANGE" \
  | grep -E '^(build|build-mtlx|build-osd|web/dist|dist)/|(^|/)obj/|(^|/)bin/|/CMakeFiles/|\.(a|o|so|dylib|dll|lib|pdb|pyc|whl|ninja_deps|ninja_log)$|/CMakeCache\.txt$|/CTestTestfile\.cmake$|/(tests/)?build\.ninja$|\.make$|/node_modules/' \
  && { echo "ABORT: build artifacts staged for push"; exit 1; } \
  || echo "No obvious build artifacts in $RANGE"
```

`.gitignore` covers most of the above; if a file shows up here it usually means
it was either `git add`-ed with `-f`, or a previous mistake was rebased forward.
Drop it; do not push it.

#### Check 3 — No unintended binary / asset data

Model files, test textures, captured payloads, large images and other binary art
belong in external storage, not in the main repo history. Specifically reject:

- `*.blend`, `*.fbx`, `*.glb`, `*.gltf`, `*.abc` larger than a few KB (small
  spec fixtures are OK).
- `*.obj` / `*.mtl` outside `models/`, `tests/`, `sandbox/`, `python/` — those
  hold curated, deliberately-small fixtures; any ad-hoc capture goes elsewhere.
  `models/living_room.obj` (~53 MB) and `models/dragon.obj` (~71 MB) are
  deliberately **not** tracked; never add them.
- `*.png`, `*.jpg`, `*.jpeg`, `*.exr`, `*.hdr`, `*.tif` over ~256 KB — texture
  captures are gitignored by default; small icons / spec test images are fine.
- `*.pdf` design docs and captured spec text that has no license to ship.
- `.claude/`, `.cursor/`, `.serena/`, `.commandcode/` and other AI tool scratch
  dirs (`.cache/`, `.clangd` are developer-local too).
- `fuzzer/afl/` corpus output (`id:*` crash files) — only the small seed corpus
  and `fuzzer/afl.tar.gz` are tracked.
- Anything you can't trivially regenerate from source.

Run from the repo root:

```bash
git diff --stat "$RANGE" \
  | awk '$3 ~ /^[0-9]+$/ && $3+0 > 256 { print }' \
  | head
# Inspect anything large; binaries show as "Bin <n> -> <m> bytes".

git diff --name-only "$RANGE" \
  | grep -iE '\.(blend|fbx|glb|gltf|abc|exr|hdr|tif|tiff|pdf)$|/captures?/|^fuzzer/afl/id:' \
  && { echo "ABORT: unexpected binary/asset paths in $RANGE"; exit 1; } \
  || echo "No flagged binary/asset paths in $RANGE"
```

If a binary really must ship with the repo, the answer is git-lfs or an external
asset bucket — never a plain `git add`. When in doubt, ask the user.

#### Check 4 — User permission (always, no exceptions)

After the three audits above pass, **stop and ask the user before pushing** —
even if the user previously said "push when done", "go ahead and push", or has
approved many pushes today. Authorization is single-shot and scoped to the
immediate request. The default mode is "audit, summarize, ask, then push", in
that exact order.

When asking, summarize what is about to be pushed:

- the branch name and remote (`origin/skel-ext`, etc.),
- whether it is a fast-forward or a force-push (force-pushes also need to spell
  out which previously-public commit hashes are being orphaned),
- the count of commits and a one-line per-commit summary,
- the audit results from checks 1–3 (e.g. "No credential-shaped strings, no
  build artifacts, no flagged binaries"),
- any pre-push test results worth surfacing (last `make check` / `npm test` run),
- a reminder that the branch has no upstream yet, if that is the case, since the
  push then creates a new remote branch.

Do **not** assume "auto mode" or any prior `--yes`-style flag covers a push.
Force-pushes especially need explicit, fresh confirmation; prefer
`--force-with-lease` over `--force` when the user agrees to a force push, because
lease refuses if the remote moved since the last fetch (avoiding the classic "I
just clobbered a teammate's commit" failure).

Release tags are a separate, bigger step: pushing a `v*` tag triggers the
PyPI/publish workflows and pushing an `npm-v*` tag stages an npm release. Those
need their own explicit approval, over and above this checklist — see
**Release / Versioning** above.

### 2. After the push

- If the push was a force-push, immediately note the previous remote tip in the
  conversation so a teammate can recover their work
  (`git reflog show origin/<branch>` on their side, or
  `git fetch origin <old-sha>:refs/heads/recovered-<branch>`).
- Open / update the PR if one exists; the project's default PR base is `release`.
- Do not delete branches the user did not explicitly ask to delete.
- If the push created a new remote branch, mention that the branch now exists on
  `origin` and whether an upstream tracking ref was set (`-u`).

### 3. If a check fails

- For a credential leak — **stop**, surface the leak to the user, and treat the
  credential as compromised even if the commit is still local. Rotate first,
  scrub history second; never push to "clean it up later."
- For a stray binary / artifact — drop it from history with
  `git filter-repo --invert-paths --path <p>` (or `git rebase -i` if it's a
  single recent commit), update `.gitignore`, then re-run the full checklist.
- For unintended assets — confirm with the user whether the asset belongs in Git
  LFS, an external bucket, or should simply be removed.

The Pre-push checklist is non-negotiable. A single 100 MB binary in `origin`
permanently bloats every future clone of this repo; a single leaked key in
`origin` is a security incident regardless of how fast it gets rotated.
