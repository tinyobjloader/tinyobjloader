#!/usr/bin/env python3
"""Targeted mutation check: apply small source mutations to a scratch copy of lib/tess and
confirm the arithmetic/predicate oracles (and, with --lean, the C/Lean/Fraction differential)
reject each one. Equivalent mutants are listed explicitly. Not part of the default ctest run.

usage: mutation_check.py [--lean PATH_TO_tesspredicates]
"""
import pathlib, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
# (file, original text, mutated text, oracle set, expected-equivalent)
MUTANTS = [
    ('exact.c', 'carry = v >> 32;', 'carry = v >> 31;', 'core', False),
    ('exact.c', 'if (a->sign != b->sign) return a->sign > b->sign ? 1 : -1;',
     'if (a->sign != b->sign) return a->sign < b->sign ? 1 : -1;', 'core', False),
    ('exact.c', 'nb.sign = -nb.sign;', 'nb.sign = nb.sign;', 'core', False),
    ('exact.c', 'if (cmp >= 0) {', 'if (cmp > 0) {', 'core', False),
    ('exact.c', 't.sign = a->sign * b->sign;', 't.sign = a->sign;', 'core', False),
    ('exact.c', 't->sign = x < 0 ? -1 : 1;', 't->sign = 1;', 'core', False),
    ('exact.c', 'carry = xv < yv;', 'carry = xv > yv;', 'core', False),
    ('exact.c', 'uint64_t value = (remainder << 32) | a->v[i - 1];',
     'uint64_t value = (remainder << 31) | a->v[i - 1];', 'core', False),
    ('exact.c', 'remainder = value % d;', 'remainder = (value % d) & 0x7fffffffu;', 'core', False),
    ('exact.c', 't->v[a->n + bits / 32] = (uint32_t)carry;', 't->v[a->n + bits / 32] = 0;', 'core', False),
    ('exact.c', 'cmp = rt.v[b->n] ? 1 : 0;', 'cmp = 0;', 'core', False),
    ('exact.c', 'qt.v[bit / 32] |= UINT32_C(1) << (bit % 32);', 'qt.v[bit / 32] |= UINT32_C(1) << (bit % 31);',
     'core', False),
    ('predicates.c', 's = v.n.sign * tg_orient(m, a, b, c);', 's = v.n.sign;', 'core', False),
    ('audit.c', 'if (cross.n.sign) ok = 0;', 'if (0) ok = 0;', 'lean', False),
    ('audit.c', 'positive |= s > 0;', 'positive |= s >= 0;', 'lean', False),
    ('audit.c', 'if (shared == 3) ok = 0;', 'if (shared == 4) ok = 0;', 'lean', False),
    ('geometry.c', 'if (x * y < 0 && z * w < 0) return 1;', 'if (x * y < 0 && z * w <= 0) return 1;',
     'lean', True),
]

def run(cmd, cwd, timeout=300):
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, timeout=timeout).returncode == 0
    except subprocess.TimeoutExpired:
        return False  # a hang is a kill

def main():
    lean = None
    if '--lean' in sys.argv:
        lean = pathlib.Path(sys.argv[sys.argv.index('--lean') + 1]).resolve()
    bad = 0
    for filename, old, new, oracles, equivalent in MUTANTS:
        if oracles == 'lean' and lean is None:
            print(f'skipped (needs --lean): {filename}: {old}')
            continue
        with tempfile.TemporaryDirectory() as tmp:
            work = pathlib.Path(tmp)
            for part in ('src', 'tests', 'include'):
                shutil.copytree(ROOT / part, work / part)
            source = (work / 'src' / filename).read_text()
            assert old in source, (filename, old)
            (work / 'src' / filename).write_text(source.replace(old, new, 1))
            cc = ['gcc', '-std=c11', '-O1', '-Isrc', '-Iinclude']
            if oracles == 'core':
                ok = True
                for probe, srcs, oracle in (
                        ('zp', ['tests/zi_probe.c', 'src/exact.c', 'src/tess.c'], 'tests/zi_oracle.py'),
                        ('ep', ['tests/exact_probe.c', 'src/exact.c', 'src/tess.c'], 'tests/oracle.py'),
                        ('pp', ['tests/predicate_probe.c', *map(str, (work / 'src').glob('*.c'))],
                         'tests/predicate_oracle.py')):
                    built = run(cc + srcs + ['-o', probe, '-lm'], work)
                    ok = ok and built and run([sys.executable, oracle, './' + probe], work, 120)
            else:
                built = run(cc + ['tests/predicate_probe.c', *map(str, (work / 'src').glob('*.c')),
                                  '-o', 'pp', '-lm'], work)
                ok = built and run([sys.executable, 'tests/predicate_differential.py', './pp', str(lean)],
                                   work, 600)
        survived = ok
        if survived and not equivalent:
            bad += 1
        print(('SURVIVED (equivalent, expected)' if survived and equivalent else
               'SURVIVED' if survived else 'killed'), f'{filename}: {old!r} -> {new!r}')
    return 1 if bad else 0

sys.exit(main())
