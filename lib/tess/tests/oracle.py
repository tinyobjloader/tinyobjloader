#!/usr/bin/env python3
"""Independent arbitrary-integer/Fraction oracle. Deterministic seed."""
import fractions as F
import random
import subprocess
import sys
import math
rng = random.Random(8128)
def enc(q):
    return f'{q.numerator:x}/{q.denominator:x}\n'
commands=[]
expected=[]
for _ in range(400):
    a=F.Fraction(rng.getrandbits(rng.randrange(1,512))*(-1 if rng.randrange(2) else 1), rng.getrandbits(150)+1)
    b=F.Fraction(rng.getrandbits(rng.randrange(1,512))*(-1 if rng.randrange(2) else 1), rng.getrandbits(150)+1)
    for op, fn in [('add',lambda:a+b),('sub',lambda:a-b),('mul',lambda:a*b),('div',lambda:a/b)]:
        if op=='div' and not b: continue
        commands.append(op+'\n'+enc(a)+enc(b)); expected.append(fn())
for d in [0.,-0.,math.ulp(0.),sys.float_info.max,sys.float_info.min]+[math.ldexp(rng.random()-.5,rng.randrange(-1073,1024)) for _ in range(300)]:
    commands.append('double\n'+d.hex()+'\n');expected.append(F.Fraction(d))
p=subprocess.run([sys.argv[1]],input=''.join(commands),text=True,capture_output=True)
assert p.returncode==0,p.stderr
lines=p.stdout.splitlines()
assert len(lines)==len(expected),(len(lines),len(expected))
for i,(s,want) in enumerate(zip(lines,expected)):
    a,b=s.split('/');got=F.Fraction(int(a,16),int(b,16))
    assert got==want,(i,got,want)
print(f'{len(expected)} independent rational/binary64 checks passed')
