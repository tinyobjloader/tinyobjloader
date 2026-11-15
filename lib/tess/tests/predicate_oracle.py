"""Independent Fraction determinant oracle, exhaustive grids and exponent stress."""
from fractions import Fraction as Q
from itertools import product
import math
import random
import subprocess
import sys

def det3(rows):
    a,b,c=rows
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def orient(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def determinant(op, points):
    a,b,c,d=[tuple(map(Q,p)) for p in points]
    rows=[tuple(x-y for x,y in zip(p,d)) for p in (a,b,c)]
    if op=='incircle':
        rows=[(x,y,x*x+y*y) for x,y,_ in rows]
        value=det3(rows)*orient(a,b,c)
    else:
        value=det3(rows)
    return (value>0)-(value<0)
commands=[]
expected=[]
def add(op,points):
    expected.append(determinant(op,points))
    commands.append(op+' '+' '.join(float(x).hex() for p in points for x in p)+'\n')
grid2=[(x,y,0) for x,y in product(range(-1,2),repeat=2)]
grid3=list(product(range(2),repeat=3))
for points in product(grid2,repeat=4): add('incircle',points)
for points in product(grid3,repeat=4): add('orient3',points)
rng=random.Random(0xC11)
for _ in range(300):
    points=[tuple(math.ldexp(rng.uniform(-1,1),rng.randrange(-30,31)) for _ in range(3)) for _ in range(4)]
    for op in ('incircle','orient3'): add(op,points)
for exponent in (-1000,-500,-10,0,500,1000):
    scale=math.ldexp(1.,exponent)
    for perturbation in (0., math.ulp(scale),-math.ulp(scale)):
        points=[(0.,0.,0.),(scale,0.,0.),(scale,scale,0.),(0.,scale+perturbation,0.)]
        add('incircle',points)
        points[-1]=(0.,scale,perturbation)
        add('orient3',points)
p=subprocess.run([sys.argv[1]],input=''.join(commands),text=True,capture_output=True,timeout=120)
assert p.returncode==0,(p.stderr,len(p.stdout.splitlines()),commands[len(p.stdout.splitlines())])
actual=list(map(int,p.stdout.split()))
assert len(actual)==len(expected)
for i,(got,want) in enumerate(zip(actual,expected)):
    assert got==want,(i,commands[i],got,want)
print(f'{len(expected)} exact incircle/orient3 oracle checks passed (exhaustive grids + exponent/cancellation stress)')
