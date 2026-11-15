"""Exercise certified OBJ output and byte/geometry/request association failures."""
import json
import pathlib
import subprocess
import sys
import tempfile
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/'tools'))
from verify_asset import records
exe,checker,auditor=sys.argv[1:]
fixtures=pathlib.Path(__file__).parent/'fixtures'
verifier=pathlib.Path(__file__).resolve().parents[1]/'tools'/'verify_asset.py'
def run(args,code):
    p=subprocess.run(args,capture_output=True,text=True,timeout=180)
    assert p.returncode==code,(args,p.returncode,p.stdout,p.stderr)
def encode(items):
    return b'TESS-ASSET1\n'+b''.join(k.encode()+b'\n'+str(len(v)).encode()+b'\n'+v for k,v in items)+b'END\n'
with tempfile.TemporaryDirectory() as d:
    d=pathlib.Path(d);out=d/'out.obj'
    for name,flags in [('planar-square',['--target-count','128','--subdivide-boundary']),
        ('concave-L',['--target-count','128','--subdivide-boundary']),('annulus',[]),('warped',[])]:
        source=fixtures/(name+'.obj')
        run([exe,*flags,'--lean-checker',checker,str(source),str(out)],0)
        verify=[sys.executable,str(verifier),'--source',str(source),'--request',str(out)+'.tess-request',
            '--bundle',str(out)+'.tess','--obj',str(out),'--lean-checker',checker,'--audit-exe',auditor]
        run(verify,0)
        if name == 'annulus':
            # A resource-limited dependency must stay distinct from rejection.
            fake=d/'checker'
            fake.write_text('#!/usr/bin/env python3\nimport sys\nsys.exit(3)\n')
            fake.chmod(0o700)
            for flag in ('--lean-checker','--audit-exe'):
                limited=verify.copy();limited[limited.index(flag)+1]=str(fake)
                run(limited,3)
            fake.write_text('#!/usr/bin/env python3\nimport sys\nsys.exit(1)\n')
            for flag in ('--lean-checker','--audit-exe'):
                rejected=verify.copy();rejected[rejected.index(flag)+1]=str(fake)
                run(rejected,1)
        original=out.read_bytes();items=records(str(out)+'.tess',b'TESS-ASSET1')
        out.write_bytes(original+b'# changed actual asset\n');run(verify,1)
        out.write_bytes(original)
        changed=original.replace(b'v 0 0 0',b'v 0.125 0 0',1)
        assert changed!=original
        out.write_bytes(changed)
        pathlib.Path(str(out)+'.tess').write_bytes(encode([(k,changed if k=='OBJ' else v) for k,v in items]))
        run(verify,1)
        out.write_bytes(original)
        modified=[]
        for k,v in items:
            if k=='PATCH_MAP':
                data=json.loads(v);data['output_global_face_start']+=1;v=json.dumps(data).encode()
            modified.append((k,v))
        pathlib.Path(str(out)+'.tess').write_bytes(encode(modified));run(verify,1)
        pathlib.Path(str(out)+'.tess').write_bytes(encode(items)[:-1]);run(verify,1)
        for length in (b'-1', b'+1', b'01', b'9'*100):
            pathlib.Path(str(out)+'.tess').write_bytes(b'TESS-ASSET1\nSOURCE\n'+length+b'\nxEND\n')
            run(verify,1)
        # Original global IDs are bound even when another unused source vertex
        # has identical coordinates. Do not permit provenance to move to it.
        if name == 'planar-square':
            duplicate=d/'duplicate.obj'
            duplicate.write_bytes(source.read_bytes()+b'\nv 0 0 0\n')
            run([exe,str(duplicate),str(out)],0)
            verify[verify.index('--source')+1]=str(duplicate)
            run(verify,0)
            dup_items=records(str(out)+'.tess',b'TESS-ASSET1')
            mapping=json.loads(next(v for k,v in dup_items if k=='PATCH_MAP'))
            old=mapping['output_global_vertices'][0]
            new=len([line for line in out.read_text().splitlines() if line.startswith('v ')])-1
            assert old != new
            mapping['output_global_vertices'][0]=new
            lines=out.read_text().splitlines()
            for j,line in enumerate(lines):
                if line.startswith('f '):
                    lines[j]='f '+' '.join(str(new+1) if int(x)==old+1 else x for x in line.split()[1:])
            replacement=('\n'.join(lines)+'\n').encode()
            out.write_bytes(replacement)
            patched=[(k,json.dumps(mapping).encode() if k=='PATCH_MAP' else replacement if k=='OBJ' else v) for k,v in dup_items]
            pathlib.Path(str(out)+'.tess').write_bytes(encode(patched));run(verify,1)
print('actual OBJ, sidecar/request binding, rounded geometry and patch face association checks passed')
