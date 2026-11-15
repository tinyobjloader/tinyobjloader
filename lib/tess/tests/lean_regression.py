"""Check actual C artifacts with Lean; mutate semantics, provenance and bounds."""
import pathlib
import subprocess
import sys
import tempfile
emitter, checker = sys.argv[1:]
def run(arguments, expected, **options):
    p = subprocess.run(arguments, capture_output=True, timeout=120, **options)
    assert p.returncode == expected, (arguments, p.returncode, p.stdout, p.stderr)
def sections(lines):
    nr=int(lines[4]); section=6+nr
    version=int(lines[0][-1]); run_start=None
    if version==2:
        run_start=section
        section+=19+int(lines[section+7])
    meshes=[]
    for _ in range(2):
        nv,nf,ne=map(int,lines[section:section+3])
        vertices=section+8
        faces=vertices+(6 if version==2 else 5)*nv
        constraints=faces+(4 if version==2 else 3)*nf
        meshes.append(dict(header=section,vertices=vertices,faces=faces,constraints=constraints,nv=nv,nf=nf,ne=ne))
        section=constraints+(8 if version==2 else 4)*ne
    assert lines[section:]==['END']
    return version,run_start,meshes
with tempfile.TemporaryDirectory() as directory:
    directory=pathlib.Path(directory)
    originals=[]
    for name,flags in [('square',[]),('warped',['warped']),('reversed',['warped','reversed']),('hole',['hole']),('concave',['concave'])]:
        request=directory/(name+'.request.tess'); candidate=directory/(name+'.tess')
        run([emitter,str(request),*flags],0)
        candidate.write_bytes(request.read_bytes())
        run([checker,str(request),str(candidate)],0)
        originals.append(request)
        lines=request.read_text().splitlines(); _,_,meshes=sections(lines); output=meshes[1]
        for location,value in [(output['vertices']+2,'00000001/00000001'),(output['header']+6,str(1-int(lines[output['header']+6])))]:
            corrupted=lines.copy();corrupted[location]=value
            candidate.write_text('\n'.join(corrupted)+'\n')
            run([checker,str(request),str(candidate)],1)
        if name=='square':
            alternate=lines.copy()
            for mesh in meshes:
                alternate[mesh['faces']:mesh['faces']+6]=['0','1','3','1','2','3']
            candidate.write_text('\n'.join(alternate)+'\n')
            run([checker,str(request),str(candidate)],1)
        candidate.write_bytes(request.read_bytes()[:-1]);run([checker,str(request),str(candidate)],1)
    run([checker,str(originals[0]),str(originals[1])],1)
    for mode in ('remesh','remesh-features','approx'):
        request=directory/(mode+'.request.tess'); candidate=directory/(mode+'.tess')
        run([emitter,str(request),mode,str(candidate)],0)
        run([checker,str(request),str(candidate)],0)
        req=request.read_bytes(); original=candidate.read_bytes()
        run([checker,'--stdin'],0,input=req+b'\0'+original)
        lines=original.decode().splitlines(); _,run_start,meshes=sections(lines); seed,output=meshes
        mutations=[(output['vertices']+3,'00000001/00000001'),
            (output['header']+6,str(1-int(lines[output['header']+6]))),
            (output['faces'],lines[output['faces']+1]),
            (output['constraints']+5,'00000001/00000002'),
            (seed['faces']+3,'999'),
            (run_start+2,'00000001/00000001')]
        for location,value in mutations:
            corrupted=lines.copy();corrupted[location]=value
            candidate.write_text('\n'.join(corrupted)+'\n')
            run([checker,str(request),str(candidate)],1)
        oversized=lines.copy();oversized[seed['header']]='10001'
        candidate.write_text('\n'.join(oversized)+'\n');run([checker,str(request),str(candidate)],3)
        candidate.write_bytes(original[:-1]);run([checker,str(request),str(candidate)],1)
        candidate.write_bytes(b'\xff');run([checker,str(request),str(candidate)],1)
        if mode=='approx':
            # Same vertex heights, different diagonal: maximum error is at the
            # rational overlay crossing. 1/2 accepted; 1/3 and zero rejected.
            request_lines=req.decode().splitlines()
            for tolerance in ('00000001/00000003','0/00000001'):
                changed_request=request_lines.copy(); changed_request[run_start+3]=tolerance
                changed_output=lines.copy(); changed_output[run_start+3]=tolerance
                request.write_text('\n'.join(changed_request)+'\n')
                candidate.write_text('\n'.join(changed_output)+'\n')
                run([checker,str(request),str(candidate)],1)
print('C-to-Lean V1/V2: coverage, holes, remeshing, tags, positive overlay bound, request binding and corruption passed')
