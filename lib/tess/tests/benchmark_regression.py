"""The release benchmark must fail closed when required artifacts disappear."""
import json
import pathlib
import subprocess
import sys
import tempfile

root = pathlib.Path(__file__).resolve().parents[1]
fixtures = json.loads((root/'benchmarks'/'results.json').read_text())['fixtures']
with tempfile.TemporaryDirectory() as directory:
    directory = pathlib.Path(directory)
    rows = directory/'rows.json'
    rows.write_text(json.dumps(fixtures))
    producer = directory/'producer'
    checker = directory/'checker'
    calls = directory/'calls'
    checker.write_text('#!/usr/bin/env python3\nimport pathlib,sys\n'
                       f'with pathlib.Path({str(calls)!r}).open("a") as log: log.write(sys.argv[2]+"\\n")\n')
    checker.chmod(0o700)
    for scenario in ('missing-both', 'missing-rounded', 'export-failed', 'complete'):
        producer.write_text('#!/usr/bin/env python3\nimport json,pathlib,sys\n'
            f'rows=json.loads(pathlib.Path({str(rows)!r}).read_text())\n'
            'for row in rows:\n'
            ' p=pathlib.Path(sys.argv[1])/row["fixture"]\n'
            ' pathlib.Path(str(p)+".request.tess").write_text("TESS2\\npolicy\\n")\n'
            + (' row["binary64_export_status"]=9\n' if scenario == 'export-failed' else '')
            + ('' if scenario == 'missing-both' else
               ' pathlib.Path(str(p)+".exact.tess").write_text("exact")\n')
            + (' pathlib.Path(str(p)+".rounded.tess").write_text("rounded")\n'
               if scenario in ('complete', 'export-failed') else '')
            + ' print(json.dumps(row))\n')
        producer.chmod(0o700)
        for optimize in ([], ['-O']):
            output = directory/'result.json'
            output.unlink(missing_ok=True)
            calls.unlink(missing_ok=True)
            checked = subprocess.run([sys.executable, *optimize,
                str(root/'benchmarks'/'run.py'), '--executable', str(producer),
                '--checker', str(checker), '--output', str(output)],
                capture_output=True, text=True, timeout=30)
            if scenario == 'complete':
                assert checked.returncode == 0, checked.stderr
                assert len(calls.read_text().splitlines()) == 16
                report = json.loads(output.read_text())
                assert all(len(row['certificate_checks']) == 2 for row in report['fixtures'])
            else:
                assert checked.returncode != 0, (scenario, checked.stdout)
                assert not output.exists(), scenario
                message = 'required binary64 export failed' if scenario == 'export-failed' else 'missing required'
                assert message in checked.stderr, checked.stderr
print('benchmark gate: missing certificates and export failures reject; all 16 required checks run')
