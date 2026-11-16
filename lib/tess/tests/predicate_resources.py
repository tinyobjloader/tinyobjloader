"""Frozen default-fuel exhaustion without an invented predicate sign or leak."""
import subprocess
import sys

# Seed 0xC1EA4, first mixed-exponent incircle sample. All values are finite
# dyadics. C's default 100-million-unit cap is insufficient for this determinant.
RESOURCE_POINTS = [tuple(float.fromhex(x) for x in row)+(0.,) for row in (
    ('-0x1.8p-400', '0x1.8p+97'), ('0x1p-463', '0x1p+79'),
    ('-0x1.cp-275', '0x1p-334'), ('-0x1.8p+69', '-0x1p+335'))]

# Seed 0xE57A, trial 4. Mixed-exponent exact dyadic 3D orientation fixture:
# C's default work budget is exhausted, while the Lean exact fixture agrees
# on the sign (-1 here). No sign is emitted by the C probe.
ORIENT3_RESOURCE_POINTS = [tuple(float.fromhex(x) for x in row) for row in (
    ('-0x1p+495', '0x1p-54', '0x1.8p-396'),
    ('0x1.c000000000000p+47', '-0x1p+78', '0x1p-432'),
    ('0x1p-389', '-0x1p-654', '-0x1.8p+44'),
    ('-0x1.cp-521', '0x1p-73', '0x1.cp-56'))]

# Seed 0x7CA7, trial 0. Mixed-exponent 6-point noncoplanar fixture: C's
# default work budget is exhausted; the Lean exact fixture returns 1
# (no contact). No sign is emitted by the C probe.
TRICONTACT_RESOURCE_POINTS = [tuple(float.fromhex(x) for x in row) for row in (
    ('0x1p+175', '0x1.cp-387', '-0x1p+73'),
    ('0x1.8p+428', '-0x1p+97', '-0x1.cp-454'),
    ('-0x1.8p+620', '-0x1p+281', '0x1.8p+309'),
    ('0x1.cp-421', '0x1p-645', '-0x1p+604'),
    ('0x1p-573', '-0x1.cp-146', '-0x1p+451'),
    ('-0x1p+634', '-0x1.8p+356', '-0x1.8p-36'))]


def _check_limited(probe, data):
    limited = subprocess.run([probe], input=data, text=True, capture_output=True, timeout=60)
    assert limited.returncode == 5 and not limited.stdout, limited
    assert limited.stderr == 'predicate resource/error 3\n', limited.stderr


def check_resource(probe):
    data = 'incircle '+' '.join(x.hex() for p in RESOURCE_POINTS for x in p)+'\n'
    _check_limited(probe, data)
    orient3_data = 'orient3 '+' '.join(x.hex() for p in ORIENT3_RESOURCE_POINTS for x in p)+'\n'
    _check_limited(probe, orient3_data)
    tricontact_data = 'tricontact '+' '.join(x.hex() for p in TRICONTACT_RESOURCE_POINTS for x in p)+'\n'
    _check_limited(probe, tricontact_data)


if __name__ == '__main__':
    check_resource(sys.argv[1])
    print('mixed-exponent incircle/orient3/tricontact: default resource failure, no sign, complete teardown')
