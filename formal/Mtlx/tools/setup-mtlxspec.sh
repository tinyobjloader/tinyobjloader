#!/bin/sh
# Point formal/Mtlx at the MaterialX Lean model (materialx-conformance/verif/lean).
# usage: tools/setup-mtlxspec.sh /path/to/materialx-conformance/verif/lean
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
src=${1:?path to materialx-conformance/verif/lean}
[ -f "$src/MtlxSpec.lean" ] || { echo "no MtlxSpec.lean in $src" >&2; exit 1; }
ln -sfn "$(cd "$src" && pwd)" "$here/mtlxspec-src"
echo "mtlxspec-src -> $src"
