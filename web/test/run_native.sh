#!/usr/bin/env bash
# Builds and runs the native (non-emscripten) oracle for the wasm shim.
# Run from the repository root: bash web/test/run_native.sh
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"

out="${TMPDIR:-/tmp}/tobj_wasm_native"

# Upstream loader: -Wall -Wextra without -Werror (its .inc files are not clean).
cc -std=c11 -Wall -Wextra -O1 -g -I . -c tiny_obj_c.c -o "$out.obj.o"
cc -std=c11 -Wall -Wextra -O1 -g -I . -c tobj_tess.c -o "$out.tess.o"

# Our shim and the test must be warning-clean.
cc -std=c11 -Wall -Wextra -Werror -O1 -g -I web/src -I . \
  -c web/src/tobj_wasm.c -o "$out.shim.o"
cc -std=c11 -Wall -Wextra -Werror -O1 -g -I web/src -I . \
  -c web/test/shim_native.c -o "$out.test.o"

cc "$out.obj.o" "$out.tess.o" "$out.shim.o" "$out.test.o" -lm -o "$out"
rm -f "$out".*.o
"$out"
