#!/bin/sh
# Lean reference (mtlxmtl) vs C (tests/mtlx_dump): fixtures + N random cases.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd); root=$(cd "$here/../.." && pwd)
n=${1:-500}; tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
lean="$here/.lake/build/bin/mtlxmtl"
cbin="$tmp/mtlx_dump"
${CC:-cc} -std=c11 -O1 -g -Wall -Wextra -Werror ${SAN:--fsanitize=address,undefined} \
  -o "$cbin" "$root/tests/mtlx_dump.c" "$root/tobj_mtlx.c"
fail=0; ok=0; acc=0
check() {
  "$lean" "$1" > "$tmp/l" ; "$cbin" "$1" > "$tmp/c"
  if cmp -s "$tmp/l" "$tmp/c"; then ok=$((ok+1)); else
    echo "MISMATCH $1"; diff "$tmp/l" "$tmp/c" | head -10; fail=$((fail+1)); cp "$1" "$tmp/../mtlx-mismatch-$ok.mtl" 2>/dev/null || true; fi
  acc=$((acc + $(grep -c 'ok=1' "$tmp/l" || true)))
}
for f in "$here"/tests/*.mtl; do check "$f"; done
i=0; while [ $i -lt "$n" ]; do python3 "$here/tools/gen.py" $i > "$tmp/r.mtl"; check "$tmp/r.mtl"; i=$((i+1)); done
echo "mtlx differential: $ok identical, $fail mismatched, $acc accepted materials"
[ $fail -eq 0 ]
