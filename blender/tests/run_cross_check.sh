#!/bin/sh
# Run the Blender add-on tests, including the OpenSubdiv cross-check.
#
#   sh blender/tests/run_cross_check.sh BLENDER [OSD_ROOT] [WORKDIR]
#
# BLENDER:  path to the blender executable (tested with 5.3).
# OSD_ROOT: OpenSubdiv install prefix (default: ./build-osd/install, as made by
#           build_osd.sh). Without it the cross-check is skipped.
# WORKDIR:  scratch directory (default: a new temporary directory).
set -eu
BLENDER=${1:?usage: run_cross_check.sh BLENDER [OSD_ROOT] [WORKDIR]}
OSD_ROOT=${2:-build-osd/install}
WORK=${3:-$(mktemp -d)}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ -f "$OSD_ROOT/include/opensubdiv/far/topologyRefiner.h" ]; then
  export OSD_ROOT=$(cd "$OSD_ROOT" && pwd)
else
  echo "no OpenSubdiv at $OSD_ROOT (run build_osd.sh); the cross-check will be skipped"
  unset OSD_ROOT
fi
"$BLENDER" -b --factory-startup --python-exit-code 1 --python "$HERE/run.py" -- "$WORK"
