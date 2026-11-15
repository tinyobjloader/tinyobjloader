"""Reproducible bounded input/certificate parser mutation campaign."""
import argparse
import pathlib
import random
import subprocess
import tempfile
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('driver');parser.add_argument('auditor');parser.add_argument('emitter');parser.add_argument('--checker')
args=parser.parse_args();rng=random.Random(0xC11FACE)
base=b'v 0 0 0\nv 1 0 0\nv 1 1 0\nv 0 1 0\nf 1 2 3 4\n'
def execute(command,timeout=30):
    result=subprocess.run(command,capture_output=True,timeout=timeout)
    assert result.returncode>=0,(command,result.returncode,result.stderr)
    return result
with tempfile.TemporaryDirectory() as d:
    d=pathlib.Path(d);source=d/'source.obj';output=d/'output.obj'
    for index in range(96):
        mutated=bytearray(base)
        for _ in range(1+index%4):
            position=rng.randrange(len(mutated))
            operation=rng.randrange(3)
            if operation==0:mutated[position]=rng.randrange(256)
            elif operation==1:del mutated[position]
            else:mutated[position:position]=bytes([rng.randrange(256)])
        source.write_bytes(mutated)
        result=execute([args.driver,'--max-operations','1000000','--max-bytes','1048576',str(source),str(output)])
        assert result.returncode in (0,1,2,3,4),result.stderr
        if result.returncode in (0,4):
            audited=execute([args.auditor,'--max-operations','100000000',str(output)])
            assert audited.returncode==0,audited.stderr
    if args.checker:
        request=d/'request.tess';candidate=d/'candidate.tess'
        for flags in ([],['remesh']):
            command=[args.emitter,str(request),*flags]
            if flags:command.append(str(candidate))
            result=execute(command,120);assert result.returncode==0,result.stderr
            if not flags:candidate.write_bytes(request.read_bytes())
            original=candidate.read_bytes()
            for index in range(48):
                mutated=bytearray(original)
                for _ in range(1+index%3):
                    position=rng.randrange(len(mutated));mutated[position]=rng.randrange(256)
                candidate.write_bytes(mutated)
                result=execute([args.checker,str(request),str(candidate)],60)
                assert result.returncode in (0,1,3),(index,result.stdout,result.stderr)
print('parser fuzz seed=0xC11FACE: 96 OBJ mutations and optional 96 Lean certificate mutations passed')
