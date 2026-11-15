#!/usr/bin/env python3
"""Run frozen C benchmarks and check every emitted exact/rounded artifact."""
import argparse
import datetime
import hashlib
import json
import pathlib
import platform
import subprocess
import tempfile
import time

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--executable',required=True)
    parser.add_argument('--checker',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--compiler',default='gcc')
    args=parser.parse_args()
    root=pathlib.Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory() as temporary:
        temporary=pathlib.Path(temporary);command=[str(pathlib.Path(args.executable).resolve()),str(temporary)]
        rss_file=temporary/'rss.txt'
        if pathlib.Path('/usr/bin/time').exists():
            command=['/usr/bin/time','-f','%M','-o',str(rss_file),*command]
        start=time.perf_counter()
        completed=subprocess.run(command,capture_output=True,text=True,timeout=600)
        elapsed=time.perf_counter()-start
        if completed.returncode:
            raise RuntimeError(completed.stderr)
        rows=[json.loads(line,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
            for line in completed.stdout.splitlines() if line]
        assert len(rows)==8
        for row in rows:
            name=row['fixture'];after=row['after']
            assert row['outcome'] in (6,7)
            if name in ('square','concave-L'):
                assert row['target_count']==128 and row['outcome']==7
                assert after['area_cv']<=.30 and after['fraction_target_band']>=.90 and after['min_angle_p05']>=20
            if name=='interior-fixed-features':
                assert row['face_splits']>0
                assert after['mean_squared_log_area_error']<=.75*row['before']['mean_squared_log_area_error']
            if name=='acute-stagnant':
                assert row['outcome']==6 and row['edits']==0 and row['termination'] in (2,3)
            assert after['max_reference_deviation']<=row['height_tolerance']
            request=temporary/(name+'.request.tess')
            row['certificate_checks']=[]
            if row['binary64_export_status'] != 0:
                raise RuntimeError(f'{name}: required binary64 export failed')
            for suffix in ('exact','rounded'):
                artifact=temporary/(name+'.'+suffix+'.tess')
                if not artifact.is_file():
                    raise RuntimeError(f'{name}: missing required {suffix} certificate')
                start=time.perf_counter()
                checked=subprocess.run([args.checker,str(request),str(artifact)],capture_output=True,text=True,timeout=180)
                if checked.returncode != 0:
                    raise RuntimeError(f'{name}: {suffix} checker exit {checked.returncode}: {checked.stderr.strip()}')
                row['certificate_checks'].append(dict(artifact=suffix,lean_accepted=True,seconds=time.perf_counter()-start,
                    sha256=hashlib.sha256(artifact.read_bytes()).hexdigest()))
            row['seed_policy']=request.read_text().splitlines()[1]
        report=dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            platform=platform.platform(),machine=platform.machine(),
            compiler=subprocess.run([args.compiler,'--version'],capture_output=True,text=True,check=True).stdout.splitlines()[0],
            build='CMake Release; strict C11; no fast-math',
            benchmark_source_sha256=hashlib.sha256((root/'tools'/'benchmark.c').read_bytes()).hexdigest(),
            percentile='Type 7 linear interpolation',precision='long double intermediates, checked binary64 reports',
            wall_seconds_C_process=elapsed,max_rss_kib_C_process=int(rss_file.read_text()) if rss_file.exists() else None,
            max_rss_scope='entire C benchmark process; per-result peak_core_bytes excludes loader, parser and external Lean process',
            cgal_comparison='not run: CGAL headers are not installed in this environment',fixtures=rows)
        pathlib.Path(args.output).write_text(json.dumps(report,indent=2)+'\n')
        for row in rows:
            q=row['after']
            print(f"{row['fixture']}: n={q['triangles']} CV={q['area_cv']:.6g} band={q['fraction_target_band']:.6g} "
                f"angle05={q['min_angle_p05']:.6g} MSE={q['mean_squared_log_area_error']:.6g} "
                f"deviation={q['max_reference_deviation']:.6g}; {len(row['certificate_checks'])} Lean artifacts")
if __name__=='__main__':
    main()
