"""Closed contact oracle using exact line parameters, independent of sign tests."""
from fractions import Fraction as Q
from itertools import product
import math
import random
import subprocess
import sys


def cross(a, b):
    return a[0]*b[1]-a[1]*b[0]


def sub(a, b):
    return a[0]-b[0], a[1]-b[1]


def point_on(p, a, b):
    v = sub(b, a)
    if v == (0, 0):
        return p == a
    axis = 0 if v[0] else 1
    t = (p[axis]-a[axis])/v[axis]
    return 0 <= t <= 1 and all(p[k] == a[k]+t*v[k] for k in (0, 1))


def intersects(points):
    a, b, c, d = [tuple(Q(x) for x in p[:2]) for p in points]
    r, s = sub(b, a), sub(d, c)
    if r == (0, 0):
        return point_on(a, c, d)
    if s == (0, 0):
        return point_on(c, a, b)
    delta = sub(c, a)
    denominator = cross(r, s)
    if denominator:
        t = cross(delta, s)/denominator
        u = cross(delta, r)/denominator
        return 0 <= t <= 1 and 0 <= u <= 1
    if cross(delta, r):
        return False
    axis = 0 if r[0] else 1
    return max(min(a[axis], b[axis]), min(c[axis], d[axis])) <= min(
        max(a[axis], b[axis]), max(c[axis], d[axis]))


rng = random.Random(0x5E6C11)
grid = [(x, y, 0.) for x, y in product(range(-1, 2), repeat=2)]
cases = list(product(grid, repeat=4))
for _ in range(1024):
    cases.append([tuple(math.ldexp(rng.randrange(-8, 9), rng.randrange(-500, 501))
                        for _ in range(2))+(0.,) for _ in range(4)])
for exponent in (-1000, -500, 0, 500, 1000):
    v = math.ldexp(1., exponent)
    u = math.ulp(v)
    cases.extend([
        [(0., 0., 0.), (v, v, 0.), (0., v, 0.), (v, 0., 0.)],
        [(0., 0., 0.), (v, 0., 0.), (v, 0., 0.), (v+u, 0., 0.)],
        [(0., 0., 0.), (v, 0., 0.), (v+u, 0., 0.), (2*v, 0., 0.)],
        [(0., 0., 0.), (v, 0., 0.), (v/2, 0., 0.), (2*v, 0., 0.)],
        [(0., 0., 0.), (0., 0., 0.), (0., -v, 0.), (0., v, 0.)],
        [(0., 0., 0.), (0., 0., 0.), (u, 0., 0.), (u, 0., 0.)]])
commands = ['segments '+' '.join(float(x).hex() for p in case for x in p)+'\n'
            for case in cases]
checked = subprocess.run([sys.argv[1]], input=''.join(commands), capture_output=True,
                         text=True, timeout=120)
assert checked.returncode == 0, checked.stderr
actual = list(map(int, checked.stdout.split()))
assert len(actual) == len(cases)
for i, (case, result) in enumerate(zip(cases, actual)):
    assert result == int(intersects(case)), (i, case, result)
print(f'{len(cases)} closed segment contact cases passed, including zero-length segments; seed=0x5E6C11')
