#!/usr/bin/env bash
#
# Builds the WebAssembly module shipped by the npm package.
#
#   ./build.sh            release (-O3)
#   ./build.sh --debug    unoptimized with assertions
#
# Requires emcc (Emscripten) in PATH. Pure C11 only: tiny_obj_c.c + tobj_tess.c
# plus the hand-written binding shim. No embind, no C++.
# Threads are off: static hosts (e.g. GitHub Pages) cannot set the COOP/COEP
# headers that SharedArrayBuffer-based pthreads require.
#
set -euo pipefail
cd "$(dirname "$0")"

OPT="-O3"
MODE="release"
if [ "${1:-}" = "--debug" ]; then
  OPT="-O0 -g3 -sASSERTIONS=2"
  MODE="debug"
elif [ -n "${1:-}" ]; then
  echo "usage: $0 [--debug]" >&2
  exit 2
fi

if ! command -v emcc >/dev/null 2>&1; then
  echo "error: emcc not found in PATH (install Emscripten)" >&2
  exit 1
fi

root=$(cd .. && pwd)

exports='["_malloc","_free"'
for sym in tobjw_load_memory tobjw_destroy tobjw_last_message tobjw_version \
           tobjw_num_shapes tobjw_num_materials tobjw_shape_desc \
           tobjw_material tobjw_material_name tobjw_material_texname; do
  exports="$exports,\"_$sym\""
done
exports="$exports]"

mkdir -p dist
# shellcheck disable=SC2086 # $OPT is a flag list
emcc -std=c11 $OPT \
  -I "$root" -I src \
  "$root/tiny_obj_c.c" "$root/tobj_tess.c" src/tobj_wasm.c \
  -o dist/tinyobj.js \
  --no-entry \
  -sMODULARIZE=1 \
  -sEXPORT_ES6=1 \
  -sEXPORT_NAME=createTinyObj \
  -sENVIRONMENT=web,worker,node \
  -sALLOW_MEMORY_GROWTH=1 \
  -sINITIAL_MEMORY=536870912 \
  -sMAXIMUM_MEMORY=2147483648 \
  -sSTACK_SIZE=1048576 \
  -sFILESYSTEM=0 \
  -sUSE_PTHREADS=0 \
  -sEXPORTED_FUNCTIONS="$exports" \
  -sEXPORTED_RUNTIME_METHODS='["UTF8ToString","HEAPU8","HEAPU32","HEAPF32"]' \
  -sINCOMING_MODULE_JS_API='["locateFile","print","printErr","wasmBinary"]'

# Status goes to stderr: `prepack` runs this script, and stdout must stay clean
# so that `npm pack --json` output is parsable.
echo "built web/dist/tinyobj.js + web/dist/tinyobj.wasm ($MODE)" >&2
ls -l dist/tinyobj.js dist/tinyobj.wasm >&2
