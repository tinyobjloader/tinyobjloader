"""C and executable Lean predicates versus independent Fraction constructions."""
from fractions import Fraction as Q
from itertools import product
import math
import random
import subprocess
import sys

from segment_oracle import fixtures, intersects, point_on, sub, cross
from predicate_resources import RESOURCE_POINTS, ORIENT3_RESOURCE_POINTS, TRICONTACT_RESOURCE_POINTS, check_resource

c_probe, lean_probe = sys.argv[1:]


def determinant(matrix):
    matrix = [list(map(Q, row)) for row in matrix]
    value = Q(1)
    for i in range(len(matrix)):
        pivot = next((j for j in range(i, len(matrix)) if matrix[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
            value = -value
        diagonal = matrix[i][i]
        value *= diagonal
        for j in range(i+1, len(matrix)):
            factor = matrix[j][i]/diagonal
            matrix[j] = [x-factor*y for x, y in zip(matrix[j], matrix[i])]
    return value


def triangular_plane_value(a, b, c, p):
    q = [tuple(Q(x) for x in point) for point in (a, b, c, p)]
    a, b, c, p = q
    return determinant([[a[0]-p[0], a[1]-p[1], a[2]-p[2]],
                        [b[0]-p[0], b[1]-p[1], b[2]-p[2]],
                        [c[0]-p[0], c[1]-p[1], c[2]-p[2]]])


def point_in_triangle(p, triangle):
    p = tuple(Q(x) for x in p)
    tri = [tuple(Q(x) for x in point) for point in triangle]
    for axis in range(3):
        other = [i for i in range(3) if i != axis]
        area = determinant([[tri[0][other[0]], tri[0][other[1]], 1],
                            [tri[1][other[0]], tri[1][other[1]], 1],
                            [tri[2][other[0]], tri[2][other[1]], 1]])
        if area == 0:
            continue
        signs = []
        for i in range(3):
            a = tri[i]
            b = tri[(i + 1) % 3]
            value = determinant([[a[other[0]], a[other[1]], 1],
                                 [b[other[0]], b[other[1]], 1],
                                 [p[other[0]], p[other[1]], 1]])
            signs.append(value)
        return (all(sign >= 0 for sign in signs) or all(sign <= 0 for sign in signs))
    return False


def triangle_contact(points):
    tri_a, tri_b = points[:3], points[3:]
    for source, target in ((tri_a, tri_b), (tri_b, tri_a)):
        for i in range(3):
            x = source[i]
            y = source[(i + 1) % 3]
            dx = triangular_plane_value(target[0], target[1], target[2], x)
            dy = triangular_plane_value(target[0], target[1], target[2], y)
            if dx == 0:
                if point_in_triangle(x, target):
                    return True
            elif dy == 0:
                if point_in_triangle(y, target):
                    return True
            elif dx * dy < 0:
                t = dx/(dx - dy)
                p = tuple(Q(a) + t*(Q(b) - Q(a)) for a, b in zip(x, y))
                if point_in_triangle(p, target):
                    return True
    return False


def expected(operation, points, ids=None):
    if operation == 'segments':
        a, b, c, d = [tuple(Q(x) for x in p[:2]) for p in points]
        return int(intersects(points))
    if operation == 'indexedsegments':
        return indexed_conflict(points, ids)
    if operation == 'tricontact':
        return 0 if triangle_contact(points) else 1
    a, b, c, d = [tuple(Q(x) for x in p[:2]) for p in points]
    if operation == 'orient3':
        points3 = [tuple(Q(x) for x in point) for point in points]
        a, b, c, d = points3
        return (determinant([[a[0]-d[0], a[1]-d[1], a[2]-d[2]],
                             [b[0]-d[0], b[1]-d[1], b[2]-d[2]],
                             [c[0]-d[0], c[1]-d[1], c[2]-d[2]]]) > 0) - \
               (determinant([[a[0]-d[0], a[1]-d[1], a[2]-d[2]],
                             [b[0]-d[0], b[1]-d[1], b[2]-d[2]],
                             [c[0]-d[0], c[1]-d[1], c[2]-d[2]]]) < 0)
    if operation == 'onsegment':
        return int(point_on(c, a, b))
    value = determinant([[x, y, 1] for x, y in (a, b, c)])
    if operation == 'incircle':
        value *= determinant([[x, y, x*x+y*y, 1] for x, y in (a, b, c, d)])
    return (value > 0)-(value < 0)


def proper_crossing(a, b, c, d):
    r = sub(b, a)
    s = sub(d, c)
    denominator = cross(r, s)
    if not denominator:
        return False
    delta = sub(c, a)
    t = cross(delta, s)/denominator
    u = cross(delta, r)/denominator
    return Q(0) < t < 1 and Q(0) < u < 1


def indexed_conflict(points, ids):
    a, b, c, d = [tuple(Q(x) for x in p[:2]) for p in points]
    if (ids[0], ids[1]) == (ids[2], ids[3]) or (ids[0], ids[1]) == (ids[3], ids[2]):
        return 0
    if proper_crossing(a, b, c, d):
        return 1
    if ids[2] not in (ids[0], ids[1]) and point_on(c, a, b):
        return 1
    if ids[3] not in (ids[0], ids[1]) and point_on(d, a, b):
        return 1
    if ids[0] not in (ids[2], ids[3]) and point_on(a, c, d):
        return 1
    if ids[1] not in (ids[2], ids[3]) and point_on(b, c, d):
        return 1
    return 0


def orient2v(a, b, p):
    return (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])


def expected_contains2(points):
    a, b, c, p = [tuple(Q(v) for v in point[:2]) for point in points]
    signs = (orient2v(a, b, p), orient2v(b, c, p), orient2v(c, a, p))
    nonnegative = all(sign >= 0 for sign in signs)
    nonpositive = all(sign <= 0 for sign in signs)
    return int(nonnegative or nonpositive)


def expected_planecut(points):
    a, b, c, x, y = [tuple(Q(v) for v in point) for point in points]
    dx = triangular_plane_value(a, b, c, x)
    dy = triangular_plane_value(a, b, c, y)
    if not dx * dy < 0:
        return None
    t = dx / (dx - dy)
    return tuple(xi + t * (yi - xi) for xi, yi in zip(x, y))


def projected_axis(face, axis):
    u, w = (axis + 1) % 3, (axis + 2) % 3
    return [(point[u], point[w]) for point in face]


def first_nondegenerate_axis(face):
    for axis in range(3):
        a, b, c = projected_axis(face, axis)
        if orient2v(a, b, c) != 0:
            return axis
    return None


def contains_axis(face, p, axis):
    a, b, c, pp = projected_axis((*face, p), axis)
    signs = (orient2v(a, b, pp), orient2v(b, c, pp), orient2v(c, a, pp))
    positive, negative = any(s > 0 for s in signs), any(s < 0 for s in signs)
    return not (positive and negative)


def allowed_indexed(src_ids, dst_ids, points, p):
    common = sorted(set(src_ids) & set(dst_ids))
    for index in common:
        if tuple(points[index]) == tuple(p):
            return True
    if len(common) == 2:
        u, v = points[common[0]], points[common[1]]
        if all(min(u[k], v[k]) <= p[k] <= max(u[k], v[k]) for k in range(3)):
            da = tuple(p[k] - u[k] for k in range(3))
            db = tuple(v[k] - u[k] for k in range(3))
            cross = (da[1] * db[2] - da[2] * db[1],
                     da[2] * db[0] - da[0] * db[2],
                     da[0] * db[1] - da[1] * db[0])
            if all(component == 0 for component in cross):
                return True
    return False


def edges_against(src, src_ids, dst, dst_ids, dst_axis, points):
    for k in range(3):
        x, y = src[k], src[(k + 1) % 3]
        dx = triangular_plane_value(dst[0], dst[1], dst[2], x)
        dy = triangular_plane_value(dst[0], dst[1], dst[2], y)
        if dx == 0 and contains_axis(dst, x, dst_axis) and \
                not allowed_indexed(src_ids, dst_ids, points, x):
            return False
        if dy == 0 and contains_axis(dst, y, dst_axis) and \
                not allowed_indexed(src_ids, dst_ids, points, y):
            return False
        if dx * dy < 0:
            t = dx / (dx - dy)
            p = tuple(q + t * (r - q) for q, r in zip(x, y))
            if contains_axis(dst, p, dst_axis) and \
                    not allowed_indexed(src_ids, dst_ids, points, p):
                return False
    return True


def audit3(points, fa, fb):
    """Exact replication of the C 3D auditor's accept/reject decision for the
    two-face case, including coplanarity, indexed shared simplices and
    identical triangles. Returns True when the audit accepts."""
    fa, fb = tuple(fa), tuple(fb)
    points = [tuple(Q(v) for v in point) for point in points]
    face_a = [points[i] for i in fa]
    face_b = [points[i] for i in fb]
    axis_a = first_nondegenerate_axis(face_a)
    axis_b = first_nondegenerate_axis(face_b)
    if axis_a is None or axis_b is None:
        return False

    def segment_conflict_xy(x, y, u, v, id_x, id_y, id_u, id_v):
        return indexed_conflict([x, y, u, v], (id_x, id_y, id_u, id_v))

    coplanar = all(triangular_plane_value(face_a[0], face_a[1], face_a[2], q) == 0
                   for q in face_b)
    if coplanar:
        if len(set(fa) & set(fb)) == 3:
            return False
        axis_u, axis_w = (axis_a + 1) % 3, (axis_a + 2) % 3

        def project(p):
            return (p[axis_u], p[axis_w])

        for k in range(3):
            x, y = face_a[k], face_b[k]
            if contains_axis(face_b, x, axis_a) and \
                    not allowed_indexed(fa, fb, points, x):
                return False
            if contains_axis(face_a, y, axis_a) and \
                    not allowed_indexed(fa, fb, points, y):
                return False
            for l in range(3):
                u, v = face_b[l], face_b[(l + 1) % 3]
                x_next = face_a[(k + 1) % 3]
                if segment_conflict_xy(project(x), project(x_next),
                                       project(u), project(v),
                                       fa[k], fa[(k + 1) % 3], fb[l], fb[(l + 1) % 3]):
                    return False
        return True
    return (edges_against(face_a, fa, face_b, fb, axis_b, points)
            and edges_against(face_b, fb, face_a, fa, axis_a, points))


cases = [('segments' if index < 100 else 'indexedsegments', points,
          None if index < 100 else (0, 1, 2, 3))
         for index, points in enumerate(fixtures())]
grid = [(float(x), float(y), 0.) for x, y in product(range(-1, 2), repeat=2)]
for points in product(grid, repeat=3):
    cases.append(('onsegment', (*points, points[-1]), None))
    cases.append(('orient2', (*points, points[-1]), None))
cases.extend(('incircle', points, None) for points in product(grid, repeat=4))

# Shared indexed IDs are intentionally exercised separately from ordinary
# disjoint-edge intersection. Repeated IDs denote the same vertex, so their
# recorded coordinates must agree. The variants cover every shared endpoint
# position, identical and reversed edges, collinear overlap beyond a common
# vertex and larger IDs.
for index, (p, q, r) in enumerate(product(grid, repeat=3)):
    if index % 2:
        shared = [(7, 100, 7, 11), (7, 100, 11, 7), (7, 100, 100, 11), (7, 100, 11, 100)]
    else:
        shared = [(0, 1, 0, 2), (0, 1, 2, 0), (0, 1, 1, 2), (0, 1, 2, 1)]
    fixtures_shared = [(p, q, p, r), (p, q, r, p), (p, q, q, r), (p, q, r, q)]
    cases.extend(('indexedsegments', points, ids)
                 for points, ids in zip(fixtures_shared, shared))
for index, (p, q) in enumerate(product(grid, repeat=2)):
    if index % 2:
        identical, reversed_ = (7, 100, 7, 100), (7, 100, 100, 7)
    else:
        identical, reversed_ = (0, 1, 0, 1), (0, 1, 1, 0)
    cases.append(('indexedsegments', (p, q, p, q), identical))
    cases.append(('indexedsegments', (p, q, q, p), reversed_))


# Noncoplanar exact triangle contacts. Fixtures stay nondegenerate and exclude
# the indexed shared-simplex exception; all six vertices have distinct indices.
small3 = [(float(x), float(y), float(z)) for x, y, z in product(range(-1, 2), repeat=3)]
target_tricontact = []
rng_tricontact = random.Random(0xC0A5)

# Nested plane cases: one source edge lies in the other face's plane while
# only its middle overlaps the target triangle. This exercises the collapsed
# plane-value branch and the complementary edge from the other face.
nested = []
nested_thirds = [(1, 1, 1), (-1, 1, 1), (1, -1, 1), (-1, -1, 1)]
for third in nested_thirds:
    for a in (-4, -3, -2, -1):
        for b in (-2, -1, 0, 1, 2, 3):
            triangle_b = [(0., float(a), float(b)),
                          (0., float(a) + 4., float(b) + 4.),
                          (0., float(a), float(b) + 4.)]
            points = [(0., -10., 0.), (0., 10., 0.), tuple(float(q) for q in third), *triangle_b]
            if triangle_contact(points):
                nested.append(('tricontact', points, None))
cases.extend(nested[:36])
def face_nondegenerate(tri):
    for axis in range(3):
        other = [i for i in range(3) if i != axis]
        area = determinant([[tri[0][other[0]], tri[0][other[1]], 1],
                           [tri[1][other[0]], tri[1][other[1]], 1],
                           [tri[2][other[0]], tri[2][other[1]], 1]])
        if area != 0:
            return True
    return False
rng_tricontact = random.Random(0xC0A5)
while len(target_tricontact) < 64:
    points = rng_tricontact.sample(small3, 6)
    if not face_nondegenerate(points[:3]):
        continue
    if not face_nondegenerate(points[3:]):
        continue
    offsets = [triangular_plane_value(points[0], points[1], points[2], point)
               for point in points[3:]]
    if not any(offsets):
        continue
    if all(offsets):
        # Faces in distinct parallel planes do not contact; accept as
        # disjoint fixtures only if all offsets have the same sign.
        if any(offset > 0 for offset in offsets) and any(offset < 0 for offset in offsets):
            continue
    target_tricontact.append(('tricontact', points, None))
cases.extend(target_tricontact)

# Exact strict plane cuts: z=0 face grids with edges on both sides, coplanar
# endpoints and touching endpoints, plus bounded random 3D dyadics. Mixed
# extreme exponents can exhaust the C work budget, so fixtures stay bounded.
planecut_cases = []
face_grid = [(float(x), float(y), 0.) for x, y in product(range(-1, 2), repeat=2)]
planecut_faces = list(product(face_grid, repeat=3))
for index, face in enumerate(planecut_faces):
    if index >= 96:
        break
    face = [tuple(float(component) for component in point) for point in face]
    config = index % 4
    if config == 0:
        edge = ((2., 3., -1.), (2., 3., 1.))
    elif config == 1:
        edge = ((-3., 1., -2.), (5., -2., -4.))
    elif config == 2:
        edge = ((1.5, -2.5, 0.), (1.5, -2.5, 2.))
    else:
        edge = ((0., 0., 0.), (3., 4., 0.))
    planecut_cases.append(('planecut', (*face, *edge), None))
for index, face in enumerate(planecut_faces):
    if index >= 64:
        break
    face = [tuple(float(component) for component in point) for point in face]
    edge = ((-1., 2., -1.), (1., 2., 1.))
    planecut_cases.append(('planecut', (*face, *edge), None))
rng_pc = random.Random(0x51EC)
for _ in range(128):
    points = [tuple(math.ldexp(rng_pc.randrange(-6, 7), rng_pc.randrange(-15, 16))
                    for _ in range(3)) for _ in range(5)]
    planecut_cases.append(('planecut', points, None))
cases.extend(planecut_cases)
# Exact 2D containment, both face orientations (grid enumeration covers them).
grid2 = [(float(x), float(y)) for x, y in product(range(-1, 2), repeat=2)]
for a, b, c in product(grid2, repeat=3):
    cases.append(('contains2', (a, b, c, (0., 0.)), None))
    cases.append(('contains2', (a, b, c, (2., 2.)), None))
# Coplanar/shared-index triangle audits. Hand-verified expectations first,
# then random nondegenerate pairs decided by the exact Fraction oracle.
ta_unit_outer = [(0., 0., 0.), (8., 0., 0.), (0., 8., 0.)]
for points, fa, fb, wanted in (
        (ta_unit_outer + [(2., 2., 0.), (4., 2., 0.), (2., 4., 0.)], (0, 1, 2), (3, 4, 5), False),
        (ta_unit_outer + [(10., 10., 0.), (12., 10., 0.), (10., 12., 0.)], (0, 1, 2), (3, 4, 5), True),
        (ta_unit_outer + [(0., -4., 0.), (8., -4., 0.), (4., 0., 0.)], (0, 1, 2), (3, 4, 5), False),
        (ta_unit_outer + [(0., -4., 0.)], (0, 1, 2), (0, 1, 3), True),
        ([(1., 1., -1.), (3., 1., -1.), (2., -1., 1.)] + ta_unit_outer, (3, 4, 5), (0, 1, 2), False),
        (ta_unit_outer + [(1., 1., 1.), (3., 1., 1.), (2., 3., 1.)], (0, 1, 2), (3, 4, 5), True)):
    assert audit3(points, fa, fb) is wanted
triaudit_cases = []
rng_ta = random.Random(0x7E5A)
while len(triaudit_cases) < 192:
    pts = rng_ta.sample(small3, 6)
    if not face_nondegenerate(pts[:3]) or not face_nondegenerate(pts[3:]):
        continue
    fa = (0, 1, 2)
    mode = rng_ta.randrange(10)
    if mode < 3:
        fb = (fa[2], 3, 4)
    elif mode < 5:
        fb = (fa[0], fa[1], 3)
    elif mode < 7:
        fb = (fa[1], fa[2], fa[0])
    else:
        fb = (fa[2], fa[1], fa[0]) if mode == 7 else tuple(reversed(fa))
    triaudit_cases.append(('triaudit', tuple(pts), fa + fb))
for A, B in (
        ([(0., 0., 0.), (8., 0., 0.), (0., 8., 0.)], [(2., 2., 0.), (4., 2., 0.), (2., 4., 0.)]),
        ([(0., 0., 0.), (8., 0., 0.), (0., 8., 0.)], [(10., 10., 0.), (12., 10., 0.), (10., 12., 0.)]),
        ([(0., 0., 0.), (8., 0., 0.), (0., 8., 0.)], [(1., 1., -1.), (3., 1., -1.), (2., -1., 1.)])):
    triaudit_cases.append(('triaudit', tuple(A) + tuple(B), (0, 1, 2, 3, 4, 5)))
cases.extend(triaudit_cases)
rng = random.Random(0xC1EA4)
for _ in range(128):
    points = [tuple(math.ldexp(rng.randrange(-8, 9), rng.randrange(-500, 501))
                    for _ in range(2))+(0.,) for _ in range(4)]
    for operation in ('onsegment', 'orient2'):
        cases.append((operation, points, None))
for _ in range(128):
    points = [tuple(math.ldexp(rng.randrange(-8, 9), rng.randrange(-30, 31))
                    for _ in range(2))+(0.,) for _ in range(4)]
    cases.append(('incircle', points, None))
for _ in range(64):
    p, q, r = [tuple(math.ldexp(rng.randrange(-8, 9), rng.randrange(-500, 501))
                     for _ in range(2))+(0.,) for _ in range(3)]
    for points, ids in (((p, q, p, r), (7, 100, 7, 11)),
                        ((p, q, r, p), (7, 100, 11, 7)),
                        ((p, q, q, r), (7, 100, 100, 11)),
                        ((p, q, r, q), (7, 100, 11, 100))):
        cases.append(('indexedsegments', points, ids))
# Exact 3D orientation is checked with the same C `tg_orient3` convention as
# `planeValue`: rows are a-d, b-d and c-d. Low-coordinate grids cover many
# degenerate/coplanar cases; random dyadic triples cover nonzero signs at a
# range of exponents.
grid3 = [(float(x), float(y), float(z)) for x, y, z in product(range(-1, 2), repeat=3)]
for index, points in enumerate(product(grid3, repeat=4)):
    if index >= 128:
        break
    cases.append(('orient3', points, None))
for _ in range(256):
    points = [tuple(math.ldexp(rng.randrange(-8, 9), rng.randrange(-30, 31))
                    for _ in range(3)) for _ in range(4)]
    cases.append(('orient3', points, None))
# Axis-dominant extreme-exponent orientations stay within C's default work
# budget; exact huge arbitrary cases may still exhaust the C bound.
for index in range(128):
    exponent = (-1000, -500, -10, 0, 10, 500)[index % 6]
    v = math.ldexp(1.5, exponent)
    sign = 1 if (index // 6) % 2 == 0 else -1
    swap = bool((index // 12) % 2)
    if swap:
        points = [(0., 0., 0.), (0., sign*v, 0.), (0., 0., 1.), (1., 0., 0.)]
    else:
        points = [(0., 0., 0.), (sign*v, 0., 0.), (0., 1., 0.), (0., 0., 1.)]
    cases.append(('orient3', points, None))
for exponent in (-1000, -500, -10, 0, 500, 1000):
    v = math.ldexp(1., exponent)
    for offset in (0., math.ulp(v), -math.ulp(v)):
        cases.append(('incircle', [(0., 0., 0.), (v, 0., 0.), (v, v, 0.), (0., v+offset, 0.)], None))

def parse_hex_q(token):
    numerator, denominator = token.split('/')
    sign = 1
    if numerator.startswith('-'):
        sign, numerator = -1, numerator[1:]
    assert numerator.startswith('0x') and denominator.startswith('0x')
    return Q(sign * int(numerator[2:], 16), int(denominator[2:], 16))


def parse_planecut_line(line, probe):
    tokens = line.split()
    if tokens == ['0']:
        return None
    assert tokens[0] == '1' and len(tokens) == 4, (probe, line)
    if probe == 'c':
        return tuple(parse_hex_q(token) for token in tokens[1:])
    return tuple(Q(token) for token in tokens[1:])


commands_c, commands_lean, answers = [], [], []
for index, (operation, points, ids) in enumerate(cases):
    points = [tuple(float(x) for x in p) for p in points]
    coordinate_text = ' '.join(x.hex() for p in points for x in p)
    coordinates = [Q(x) for p in points for x in p[:2]]
    rational_text = ' '.join(f'{q.numerator}/{q.denominator}' for q in coordinates)
    if operation == 'indexedsegments':
        id_text = ' '.join(str(index) for index in ids)
        commands_c.append(f'indexedsegments {coordinate_text} {id_text}\n')
        commands_lean.append(f'indexedsegments {rational_text} {id_text}\n')
        answers.append(indexed_conflict(points, ids))
    elif operation == 'orient3':
        commands_c.append(f'orient3 {coordinate_text}\n')
        coordinates = [Q(x) for p in points for x in p]
        rational_text = ' '.join(f'{q.numerator}/{q.denominator}' for q in coordinates)
        commands_lean.append(f'orient3 {rational_text}\n')
        answers.append(expected(operation, points))
    elif operation == 'tricontact':
        coordinate_text_3d = ' '.join(x.hex() for p in points for x in p)
        coordinates = [Q(x) for p in points for x in p]
        rational_text_3d = ' '.join(f'{q.numerator}/{q.denominator}' for q in coordinates)
        commands_c.append(f'tricontact {coordinate_text_3d}\n')
        commands_lean.append(f'tricontact {rational_text_3d}\n')
        answers.append(expected(operation, points))
    elif operation == 'planecut':
        coordinates = [Q(x) for p in points for x in p]
        rational_text_3d = ' '.join(f'{q.numerator}/{q.denominator}' for q in coordinates)
        commands_c.append(f'planecut {coordinate_text}\n')
        commands_lean.append(f'planecut {rational_text_3d}\n')
        answers.append(expected_planecut(points))
    elif operation == 'contains2':
        coordinates = [Q(x) for p in points for x in p]
        rational_text = ' '.join(f'{q.numerator}/{q.denominator}' for q in coordinates)
        commands_c.append(f'contains2 {coordinate_text}\n')
        commands_lean.append(f'contains2 {rational_text}\n')
        answers.append(expected_contains2(points))
    elif operation == 'triaudit':
        # C's diagnostic auditor is compared against the Fraction oracle; the
        # Lean fixture has no executable for the coplanar/shared-index path.
        id_text = ' '.join(str(index) for index in ids)
        commands_c.append(f'triaudit {coordinate_text} {id_text}\n')
        commands_lean.append(None)
        answers.append(int(audit3(points, ids[:3], ids[3:])))
    else:
        commands_c.append(operation+' '+coordinate_text+'\n')
        commands_lean.append(operation+' '+rational_text+'\n')
        answers.append(expected(operation, points))
assert len(cases) < 24000 and len(''.join(line for line in commands_lean if line).encode()) < 8388608
jobs_lean = [(index, line) for index, line in enumerate(commands_lean) if line is not None]

def run_probe(probe, jobs):
    outputs = []
    for offset in range(0, len(jobs), 19000):
        chunk = jobs[offset:offset + 19000]
        checked = subprocess.run([probe], input=''.join(line for _, line in chunk),
                                 text=True, capture_output=True, timeout=300)
        assert checked.returncode == 0, (probe, checked.returncode, checked.stderr)
        outputs.extend(line for line in checked.stdout.splitlines() if line)
    assert len(outputs) == len(jobs), (probe, len(outputs), len(jobs))
    return outputs

for probe, name, jobs in ((c_probe, 'c', list(enumerate(commands_c))),
                          (lean_probe, 'lean', jobs_lean)):
    actual = run_probe(probe, jobs)
    for (index, _), line in zip(jobs, actual):
        operation = cases[index][0]
        if operation == 'planecut':
            got = parse_planecut_line(line, name)
            wanted = answers[index]
            assert (got is None) == (wanted is None) and \
                (got is None or all(left == right for left, right in zip(got, wanted))), \
                (probe, index, cases[index], line, wanted)
        else:
            got = int(line)
            assert got == answers[index], (probe, index, cases[index], got, answers[index])

# Frozen mixed-exponent incircle fixture: the default 100-million-unit C
# predicate budget is exhausted. It must produce no invented sign, and Lean
# still agrees with the unbounded Fraction construction. Seed 0xC1EA4, first
# mixed-exponent sample, before splitting the accepted/resource workloads.
resource_q = [Q(x) for p in RESOURCE_POINTS for x in p[:2]]
resource_lean = 'incircle '+' '.join(f'{q.numerator}/{q.denominator}' for q in resource_q)+'\n'
check_resource(c_probe)
exact = subprocess.run([lean_probe], input=resource_lean, text=True, capture_output=True, timeout=60)
assert exact.returncode == 0 and int(exact.stdout) == expected('incircle', RESOURCE_POINTS), exact

# Frozen mixed-exponent orient3 and tricontact fixtures exhaust the C
# default budget; Lean still agrees with the unbounded Fraction construction.
orient3_q = [Q(x) for p in ORIENT3_RESOURCE_POINTS for x in p]
orient3_lean = 'orient3 '+' '.join(f'{q.numerator}/{q.denominator}' for q in orient3_q)+'\n'
exact = subprocess.run([lean_probe], input=orient3_lean, text=True, capture_output=True, timeout=60)
assert exact.returncode == 0 and int(exact.stdout) == expected('orient3', ORIENT3_RESOURCE_POINTS), exact
tricontact_q = [Q(x) for p in TRICONTACT_RESOURCE_POINTS for x in p]
tricontact_lean = 'tricontact '+' '.join(f'{q.numerator}/{q.denominator}' for q in tricontact_q)+'\n'
exact = subprocess.run([lean_probe], input=tricontact_lean, text=True, capture_output=True, timeout=60)
assert exact.returncode == 0 and int(exact.stdout) == expected('tricontact', TRICONTACT_RESOURCE_POINTS), exact

# The new validation parser fails explicitly on malformed or oversized fixtures.
valid = b'orient2 0/1 0/1 1/1 0/1 0/1 1/1 0/1 0/1\n'
indexed_valid = b'indexedsegments 0/1 0/1 1/1 0/1 0/1 0/1 1/1 1/1 0 1 0 2\n'
orient3_valid = b'orient3 0/1 0/1 0/1 1/1 0/1 0/1 0/1 1/1 0/1 0/1 0/1 1/1\n'
tricontact_valid = b'tricontact 0/1 0/1 0/1 2/1 0/1 0/1 0/1 2/1 0/1 0/1 0/1 2/1 1/1 0/1 2/1 1/1 1/1 2/1 0/1 1/1 2/1\n'
planecut_valid = b'planecut 0/1 0/1 0/1 1/1 0/1 0/1 0/1 1/1 0/1 1/2 1/2 -1/1 1/2 1/2 1/1\n'
contains2_valid = b'contains2 0/1 0/1 4/1 0/1 0/1 4/1 1/1 1/1\n'
inconsistent_indexed = b'indexedsegments 0/1 0/1 1/1 0/1 2/1 0/1 1/1 1/1 0 1 0 2\n'
for data, code in ((b'unknown '+valid.split(b' ', 1)[1], 1),
    (valid.replace(b'0/1', b'0/0', 1), 1), (valid.replace(b'0/1', b'bad/1', 1), 1),
    (b'orient2 0/1\n', 1), (b'orient3 0/1\n', 1), (b'tricontact 0/1\n', 1), (b'\xff\n', 1), (b'\x00\n', 1),
    (valid.replace(b'0/1', b'1'*1025+b'/1', 1), 3),
    (b'x'*32769+b'\n', 3), (valid*20001, 3), (b'\n'*20001, 3),
    (b'x'*8388609, 3),
    (indexed_valid.replace(b' 0 1 0 2', b' 0 1 0'), 1),
    (indexed_valid.replace(b' 0 1 0 2', b' 0 1 -1 2'), 1),
    (indexed_valid.replace(b' 0 1 0 2', b' 0 1 0 1024'), 3),
    (inconsistent_indexed, 1),
    (orient3_valid.replace(b' 1/1', b''), 1),
    (tricontact_valid.replace(b' 0/1', b'', 1), 1),
    (planecut_valid.replace(b' 1/2', b'', 1), 1),
    (contains2_valid.replace(b' 1/1', b'', 1), 1),
    (b'triaudit 0/1\n', 1)):
    checked = subprocess.run([lean_probe], input=data, capture_output=True, timeout=30)
    assert checked.returncode == code, (code, checked.returncode, checked.stderr)
usage = subprocess.run([lean_probe, '--unknown'], capture_output=True, timeout=30)
assert usage.returncode == 2
# Mutation campaigns also check accepted arithmetic against Fraction rather than
# merely accepting any noncrashing exit code. C receives only exact dyadics above.
mutation_count = 0
for base in (valid, tricontact_valid, planecut_valid, contains2_valid):
    for _ in range(64):
        mutated = bytearray(base)
        position = rng.randrange(len(mutated)-1)
        mutated[position] = rng.randrange(256)
        checked = subprocess.run([lean_probe], input=mutated, capture_output=True, timeout=30)
        assert checked.returncode in (0, 1, 3), (base.decode(), checked.returncode, checked.stderr)
        if checked.returncode == 0:
            words = mutated.decode('ascii').split()
            coordinates = [Q(value) for value in words[1:]]
            if words[0] == 'orient2':
                assert len(coordinates) == 8
                points = [tuple(coordinates[2*i:2*i+2])+(Q(0),) for i in range(4)]
                expected_value = expected(words[0], points)
                assert int(checked.stdout) == expected_value
            elif words[0] == 'tricontact':
                assert len(coordinates) == 18
                points = [tuple(coordinates[3*i:3*i+3]) for i in range(6)]
                expected_value = expected(words[0], points)
                assert int(checked.stdout) == expected_value
            elif words[0] == 'planecut':
                assert len(coordinates) == 15
                points = [tuple(coordinates[3*i:3*i+3]) for i in range(5)]
                tokens = checked.stdout.decode('ascii').split()
                if tokens == ['0']:
                    got = None
                else:
                    assert tokens[0] == '1' and len(tokens) == 4, (words, checked.stdout)
                    got = tuple(Q(token) for token in tokens[1:])
                assert got == expected_planecut(points)
            elif words[0] == 'contains2':
                assert len(coordinates) == 8
                points = [tuple(coordinates[2*i:2*i+2])+(Q(0),) for i in range(4)]
                assert int(checked.stdout) == expected_contains2(points)
            else:
                raise AssertionError(('unexpected accepted operation', words[0]))
        mutation_count += 1
print(f'{len(cases)} C/Lean/Fraction predicate comparisons passed; seed=0xC1EA4; parser reject/resource/usage cases and {mutation_count} mutations passed; frozen C budget exhaustion checked')
