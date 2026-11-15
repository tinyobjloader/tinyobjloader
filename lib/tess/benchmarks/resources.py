#!/usr/bin/env python3
"""Record default-budget seed-construction scaling without changing the caps."""
import argparse
import datetime
import hashlib
import json
import pathlib
import platform
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--executable', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
completed = subprocess.run([args.executable], capture_output=True, text=True,
                           check=True, timeout=300)
rows = [json.loads(line) for line in completed.stdout.splitlines()]
assert rows and any(row['status'] == 0 for row in rows)
assert any(row['status'] == 3 for row in rows)
for row in rows:
    assert row['status'] in (0, 3)
    assert row['operations'] <= row['operation_cap']
    if row['status'] == 3:
        assert row['triangles'] == 0
source = pathlib.Path(__file__).resolve().parents[1]/'tools'/'resource_sweep.c'
report = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              platform=platform.platform(), fixture='(i,i*i,0) in index order, closed by last-to-first edge',
              chart_axis=2, build='GCC Release, strict C11',
              source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(), samples=rows)
pathlib.Path(args.output).write_text(json.dumps(report, indent=2)+'\n')
