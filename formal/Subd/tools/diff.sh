#!/bin/sh
# Lean reference (subdobj) vs C (tests/subd_dump): fixtures + N random cases.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd); root=$(cd "$here/../.." && pwd)
n=${1:-500}; tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
lean="$here/.lake/build/bin/subdobj"
cbin="$tmp/subd_dump"
${CC:-cc} -std=c11 -O1 -g -Wall -Wextra -Werror ${SAN:--fsanitize=address,undefined} \
  -o "$cbin" "$root/tests/subd_dump.c" "$root/tobj_subd.c"
fail=0; ok=0; acc=0
check() {
  "$lean" "$1" > "$tmp/l"; "$cbin" "$1" > "$tmp/c"
  if cmp -s "$tmp/l" "$tmp/c"; then ok=$((ok+1)); else
    echo "MISMATCH $1"; diff "$tmp/l" "$tmp/c" | head -10; fail=$((fail+1))
    cp "$1" "${TMPDIR:-/tmp}/subd-mismatch-$ok.obj" 2>/dev/null || true; fi
  acc=$((acc + $(grep -c 'ok=1' "$tmp/l" || true)))
}
for f in "$here"/tests/*.obj; do check "$f"; done
i=0; while [ $i -lt "$n" ]; do python3 "$here/tools/gen.py" $i > "$tmp/r.obj"; check "$tmp/r.obj"; i=$((i+1)); done
echo "subd differential: $ok identical, $fail mismatched, $acc accepted meshes"
[ $fail -eq 0 ]
