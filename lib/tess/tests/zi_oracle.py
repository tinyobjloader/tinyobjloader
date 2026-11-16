"""Limb-boundary differential of the real zi_add/zi_sub/zi_mul/zi_cmp vs Python ints."""
import itertools, random, subprocess, sys
rng = random.Random(0x21B16)
def interesting():
    vs = {0, 1, 2}
    for limbs in range(1, 7):
        for k in (2**(32*limbs), ):
            for d in (-2, -1, 0, 1, 2):
                vs.add(k + d)
        vs.add(2**(32*limbs - 1)); vs.add(2**(32*limbs - 1) - 1)
        vs.add(int('ab'*(4*limbs), 16))
        # one limb nonzero amid zeros (borrow ripple / normalization)
        for pos in range(limbs):
            vs.add(2**(32*pos)); vs.add(2**(32*limbs) - 2**(32*pos))
    vs = sorted(vs)
    return [s*v for v in vs for s in (1, -1)]
vals = sorted(set(interesting()))
pairs = list(itertools.product(vals, repeat=2))
pairs += [(rng.getrandbits(rng.randrange(1, 300))*rng.choice((1,-1)),
           rng.getrandbits(rng.randrange(1, 300))*rng.choice((1,-1))) for _ in range(3000)]
h = lambda v: ('-' if v < 0 else '') + format(abs(v), 'x')
ops = {'add': lambda a, b: a+b, 'sub': lambda a, b: a-b, 'mul': lambda a, b: a*b,
       'cmp': lambda a, b: (a > b) - (a < b)}
cmds, want = [], []
for op, f in ops.items():
    for a, b in pairs:
        cmds.append(f'{op} {h(a)} {h(b)}\n')
        want.append(str(f(a, b)) if op == 'cmp' else h(f(a, b)))
p = subprocess.run([sys.argv[1]], input=''.join(cmds), text=True, capture_output=True)
if p.returncode:
    sys.exit(f'probe exit {p.returncode}')
got = p.stdout.split()
if got != want:
    i = next(i for i, (g, w) in enumerate(zip(got, want)) if g != w)
    sys.exit(f'mismatch {cmds[i]!r}: got {got[i]} want {want[i]}')
print(len(want), 'cases ok')
