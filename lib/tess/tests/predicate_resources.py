"""Frozen default-fuel exhaustion without an invented predicate sign or leak."""
import subprocess
import sys

# Seed 0xC1EA4, first mixed-exponent incircle sample. All values are finite
# dyadics. C's default 100-million-unit cap is insufficient for this determinant.
RESOURCE_POINTS = [tuple(float.fromhex(x) for x in row)+(0.,) for row in (
    ('-0x1.8p-400', '0x1.8p+97'), ('0x1p-463', '0x1p+79'),
    ('-0x1.cp-275', '0x1p-334'), ('-0x1.8p+69', '-0x1p+335'))]


def check_resource(probe):
    data = 'incircle '+' '.join(x.hex() for p in RESOURCE_POINTS for x in p)+'\n'
    limited = subprocess.run([probe], input=data, text=True, capture_output=True, timeout=60)
    assert limited.returncode == 5 and not limited.stdout, limited
    assert limited.stderr == 'predicate resource/error 3\n', limited.stderr


if __name__ == '__main__':
    check_resource(sys.argv[1])
    print('mixed-exponent incircle: default resource failure, no sign, complete teardown')
