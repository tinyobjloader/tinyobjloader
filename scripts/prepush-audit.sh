#!/usr/bin/env bash
#
# Pre-push audit for tinyobjloader. Runs the four checks from AGENTS.md against
# the exact range a push would publish, and FAILS LOUDLY when a check cannot be
# performed -- "clean" must never mean "scanned nothing".
#
#   bash scripts/prepush-audit.sh                 # @{upstream}..HEAD
#   RANGE=origin/release..HEAD bash scripts/prepush-audit.sh
#   UPSTREAM_DEFAULT=origin/master bash scripts/prepush-audit.sh
#
set -uo pipefail

UPSTREAM_DEFAULT="${UPSTREAM_DEFAULT:-origin/release}"
fail=0
note() { printf '%s\n' "$*" >&2; }
abort() { printf 'ABORT: %s\n' "$*" >&2; exit 1; }

cd "$(git rev-parse --show-toplevel)" || exit 1

# --------------------------------------------------------------------------
# Resolve the range. A branch with no upstream (e.g. a brand new branch) must
# fall back to a named ref and say so; an unresolvable or empty range aborts.
# --------------------------------------------------------------------------
resolve_range() {
  local ref
  ref="$(git rev-parse --abbrev-ref --symbolic-full-name '@{upstream}' 2>/dev/null || true)"
  if [ -z "$ref" ]; then
    ref="$UPSTREAM_DEFAULT"
    note "note: branch has no upstream; auditing $ref..HEAD"
  fi
  case "$ref" in *..*) ;; *) ref="$ref..HEAD" ;; esac
  git rev-list -1 "$ref" >/dev/null 2>&1 || abort "cannot resolve range '$ref'"
  printf '%s' "$ref"
}

RANGE="${RANGE:-$(resolve_range)}" || exit 1
BASE="${RANGE%%..*}"
[ -n "$BASE" ] || abort "cannot derive a base commit from '$RANGE'"
count="$(git rev-list --count "$RANGE" 2>/dev/null || echo 0)"
[ "$count" -gt 0 ] || abort "range '$RANGE' contains no commits"
echo "==> auditing $RANGE ($count commits)"

# --------------------------------------------------------------------------
# Check 1a - credential-shaped strings in ADDED lines.
# --------------------------------------------------------------------------
hits="$(git diff "$RANGE" -- ':!**/*.md' ':!**/*.txt' | grep '^+' \
  | grep -niE 'AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|AIza[0-9A-Za-z_-]{35}|(api[_-]?key|secret|token|password|passwd|bearer|private[_-]?key)[[:space:]]*[:=][[:space:]]*["'"'"']?[A-Za-z0-9_+/.-]{12,}' || true)"
if [ -n "$hits" ]; then
  note "ABORT: credential-shaped strings:"
  note "$hits"
  fail=1
else
  echo "ok   Check 1a: no credential-shaped strings"
fi

# --------------------------------------------------------------------------
# Check 1b - automated secret scanners, over the SAME range.
# --------------------------------------------------------------------------
REPO="$(git rev-parse --show-toplevel)"
BRANCH="$(git branch --show-current)"
MAIN_WT="$(git worktree list --porcelain | awk '/^worktree /{print $2; exit}')"

if command -v gitleaks >/dev/null 2>&1; then
  # Trust the exit code: 0 means clean. Three output quirks, all measured here:
  #   - the summary literally says "no leaks found", so never grep for "leaks";
  #   - it colorizes its log lines and has no --no-color / NO_COLOR support,
  #     which defeats a plain sed match. Strip ESC then the CSI sequences;
  #   - it scans content *diffs*, so a range of only empty commits reports
  #     "0 commits scanned". That is not a failure -- but 0 commits for a range
  #     that does change content means the range was not understood.
  if out="$(gitleaks detect --source "$REPO" --redact --log-opts="$RANGE" --no-banner 2>&1)"; then
    clean="$(printf '%s' "$out" | tr -d '\033' | sed 's/\[[0-9;]*m//g')"
    scanned="$(printf '%s' "$clean" | grep -oE '[0-9]+ commits scanned' | grep -oE '^[0-9]+' | tail -1)"
    touched="$(git diff --name-only "$RANGE" | head -1)"
    if [ -n "$scanned" ] && [ "$scanned" -gt 0 ]; then
      echo "ok   Check 1b: gitleaks scanned $scanned commits, no leaks"
    elif [ -z "$touched" ]; then
      echo "skip Check 1b: gitleaks found no content to scan (empty commits only)"
    else
      printf '%s\n' "$clean" >&2
      note "ABORT: gitleaks scanned 0 commits for $RANGE despite changes (range not understood)"
      fail=1
    fi
  else
    printf '%s\n' "$out" >&2
    note "ABORT: gitleaks flagged secrets in $RANGE"
    fail=1
  fi
else
  echo "skip Check 1b: gitleaks not installed (regex heuristic only)"
fi

TRUFFLEHOG="${TRUFFLEHOG:-$HOME/go/bin/trufflehog}"
[ -x "$TRUFFLEHOG" ] || TRUFFLEHOG="$(command -v trufflehog || true)"
if [ -n "$TRUFFLEHOG" ] && [ -x "$TRUFFLEHOG" ]; then
  if out="$("$TRUFFLEHOG" git "file://$MAIN_WT" --since-commit="$BASE" \
        --branch="$BRANCH" --fail --no-update 2>&1)"; then
    if printf '%s' "$out" | grep -q 'finished scanning'; then
      echo "ok   Check 1b: trufflehog scanned $BASE..$BRANCH, no verified secrets"
    else
      printf '%s\n' "$out" >&2
      note "ABORT: trufflehog produced no scan summary for $BASE..$BRANCH"
      fail=1
    fi
  else
    printf '%s\n' "$out" >&2
    note "ABORT: trufflehog flagged secrets in $RANGE"
    fail=1
  fi
else
  echo "skip Check 1b: trufflehog not installed (regex heuristic only)"
fi

# --------------------------------------------------------------------------
# Check 1c - personal paths and proprietary asset names, in messages + source.
# --------------------------------------------------------------------------
hits="$({ git log "$RANGE" --format='%B';
  git diff "$RANGE" -- '*.c' '*.h' '*.inc' '*.cc' 'web/*' 'python/*'; } \
  | grep -inE '/home/[a-z]|/Users/[A-Za-z]|C:\\Users\\' || true)"
if [ -n "$hits" ]; then
  note "ABORT: personal path in messages or source:"; note "$hits"; fail=1
else
  echo "ok   Check 1c: no personal paths"
fi

note "     Check 1c: asset names (eyeball each; generic fixtures are fine):"
{ git log "$RANGE" --format='%B'
  git diff "$RANGE" -- '*.c' '*.h' '*.inc' '*.cc' 'web/*' 'python/*' | grep '^+'; } \
  | grep -oiE '[A-Za-z0-9_-]{3,}\.(obj|mtl|mtlx|png|jpg|jpeg|exr|hdr|blend|fbx|gltf|glb)' \
  | sort -u | sed 's/^/       /' >&2

# --------------------------------------------------------------------------
# Check 2 - build artifacts. `obj/` and `bin/` are build-output DIRECTORIES
# here; tracked .obj models live in models/ tests/ sandbox/ python/ formal/.
# --------------------------------------------------------------------------
hits="$(git diff --name-only "$RANGE" | grep -E \
  '^(build|build-mtlx|build-osd|web/dist|dist)/|(^|/)obj/|(^|/)bin/|/CMakeFiles/|\.(a|o|so|dylib|dll|lib|pdb|pyc|whl|ninja_deps|ninja_log)$|/CMakeCache\.txt$|/CTestTestfile\.cmake$|/(tests/)?build\.ninja$|\.make$|/node_modules/' || true)"
if [ -n "$hits" ]; then
  note "ABORT: build artifacts staged for push:"; note "$hits"; fail=1
else
  echo "ok   Check 2:  no build artifacts"
fi

# --------------------------------------------------------------------------
# Check 3 - unintended binary / asset data.
# --------------------------------------------------------------------------
hits="$(git diff --name-only "$RANGE" | grep -iE \
  '\.(blend|fbx|glb|gltf|abc|exr|hdr|tif|tiff|pdf)$|/captures?/|^fuzzer/afl/id:' || true)"
if [ -n "$hits" ]; then
  note "ABORT: unexpected binary/asset paths:"; note "$hits"; fail=1
else
  echo "ok   Check 3:  no flagged binary/asset paths"
fi

# Oversized additions are reported for inspection (binaries show as Bin n -> m).
note "     Check 3:  largest changes (inspect any 'Bin' line):"
git diff --stat "$RANGE" | awk '$3 ~ /^[0-9]+$/ && $3+0 > 256 { print "       " $0 }' \
  | head -10 >&2

# --------------------------------------------------------------------------
[ "$fail" -eq 0 ] || abort "one or more checks failed; do not push"
echo "==> all automated checks passed"
echo "    Check 4 (user permission) is NOT automated: ask before pushing."
