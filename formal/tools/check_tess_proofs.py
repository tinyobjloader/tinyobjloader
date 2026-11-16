#!/usr/bin/env python3
"""Kernel build, generation freshness and complete Tess dependency axiom audit."""
import pathlib
import re
import subprocess
import sys
root=pathlib.Path(__file__).resolve().parents[2]
for path in [*(root/'formal').glob('Tess*.lean'),*(root/'formal'/'Tess').rglob('*.lean')]:
    text=path.read_text()
    if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s',text,re.M):
        raise SystemExit('unfinished proof or unapproved axiom declaration: '+str(path))
commands=[
    ([sys.executable,'formal/tools/c2lean.py','--check'],root),
    ([sys.executable,'formal/tools/c2lean.py','--source','lib/tess/src/exact_core.c','--output','formal/Tess/C/Gen.lean',
      '--namespace','Tess.C.Gen','--function','tess_mag','--function','tess_limb_madd','--check'],root),
    ([sys.executable,'formal/tools/c2lean.py','--source','lib/tess/src/exact.c','--output','formal/Tess/C/LimbGen.lean',
      '--namespace','Tess.C.LimbGen','--function','tess_limb_madd','--function','acmp','--function','zi_add_equisign',
      '--function','zi_add_mixed','--function','zi_mul_accumulate','--function','zi_cmp','--function','trim_len','--function','dbl_decode','--include','lib/tess/include','--check'],root),
    (['lake','build','Tess','tesscheck','tesspredicates'],root/'formal'),
    (['lake','env','lean','TessAudit.lean'],root/'formal')]
for command,directory in commands:
    subprocess.run(command,cwd=directory,check=True)
