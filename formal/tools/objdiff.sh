#!/bin/sh
# Differential check: Lean parse model (formal/ObjDiff.lean) vs C loader
# (tests/obj_dump.c) on the given .obj files (default: models/*.obj).
# Usage: formal/tools/objdiff.sh [file.obj ...]
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=${TMPDIR:-/tmp}/objdiff.$$
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT
(cd "$here" && lake build objdiff >/dev/null)
cc -std=c11 -O1 -I"$root" -DTOBJ_ENABLE_FILE_IO "$root/tests/obj_dump.c" \
   "$root/tiny_obj_c.c" "$root/tobj_tess.c" -lm -o "$tmp/obj_dump"
[ $# -gt 0 ] || set -- "$root"/models/*.obj
pass=0; fail=0; skip=0
for f in "$@"; do
  if ! "$tmp/obj_dump" "$f" >"$tmp/c.txt" 2>/dev/null; then skip=$((skip+1)); continue; fi
  "$here/.lake/build/bin/objdiff" "$f" >"$tmp/lean.txt"
  if cmp -s "$tmp/c.txt" "$tmp/lean.txt"; then pass=$((pass+1))
  else fail=$((fail+1)); echo "DIFF: $f"; diff "$tmp/c.txt" "$tmp/lean.txt" | head -6; fi
done
echo "objdiff: $pass match, $fail differ, $skip skipped (C load failed)"
[ "$fail" -eq 0 ]
