"""Direct arbitrary-integer oracle for both actual translated C helpers."""
import itertools
import random
import subprocess
import sys

rng = random.Random(0xC11A641)
magnitudes = set(range(-128, 129))
for bit in range(64):
    for offset in (-1, 0, 1):
        for sign in (-1, 1):
            a = sign * (2**bit + offset)
            if -(2**63) <= a < 2**63:
                magnitudes.add(a)
magnitudes.update(rng.randrange(-(2**63), 2**63) for _ in range(4096))
limbs = (0, 1, 2, 2**16-1, 2**16, 2**31-1, 2**31, 2**32-2, 2**32-1)
madds = list(itertools.product(limbs, repeat=4))
madds.extend(tuple(rng.getrandbits(32) for _ in range(4)) for _ in range(4096))
commands = [f'mag {a}\n' for a in sorted(magnitudes)]
commands.extend('madd '+' '.join(map(str, row))+'\n' for row in madds)
checked = subprocess.run([sys.argv[1]], input=''.join(commands), text=True,
                         capture_output=True, timeout=60)
assert checked.returncode == 0, checked.stderr
lines = checked.stdout.splitlines()
assert len(lines) == len(commands), (len(lines), len(commands))
for a, line in zip(sorted(magnitudes), lines):
    assert int(line) == abs(a), (a, line)
for row, line in zip(madds, lines[len(magnitudes):]):
    result, low, high = map(int, line.split())
    a, b, add, carry = row
    expected = a*b+add+carry
    assert result == expected < 2**64, (row, line)
    assert low == expected % 2**32 and high == expected // 2**32
    assert 0 <= low < 2**32 and 0 <= high < 2**32
print(f'{len(magnitudes)} signed magnitudes and {len(madds)} limb multiply-add/carry cases passed; seed=0xC11A641')
