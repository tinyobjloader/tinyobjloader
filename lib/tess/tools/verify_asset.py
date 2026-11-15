#!/usr/bin/env python3
"""Check an OBJ bundle against caller-held input/request and the Lean checker.

The framed container and OBJ-to-patch association are checked here; the Lean
executable checks each actual decoded patch. This script is not a formal proof
of tinyobjloader, patch assembly, or the serialization/parser boundary.
"""
import argparse
from fractions import Fraction
import json
import pathlib
import subprocess
import tempfile

LIMIT = 256 * 1024 * 1024

class ResourceLimit(ValueError):
    pass

def bounded_read(path):
    with pathlib.Path(path).open('rb') as stream:
        data = stream.read(LIMIT + 1)
    if len(data) > LIMIT:
        raise ResourceLimit('file exceeds verifier byte limit')
    return data

def records(path, header):
    data = bounded_read(path)
    if not data.startswith(header + b'\n'):
        raise ValueError('invalid or oversized bundle')
    position = len(header) + 1
    out = []
    while True:
        stop = data.index(b'\n', position)
        if stop - position > 64:
            raise ValueError('invalid record kind')
        kind = data[position:stop].decode('ascii')
        position = stop + 1
        if kind == 'END':
            if position != len(data):
                raise ValueError('trailing bundle data')
            return out
        stop = data.index(b'\n', position)
        count_text = data[position:stop]
        if not count_text or len(count_text) > 20 or not count_text.isdigit():
            raise ValueError('invalid record size')
        count = int(count_text)
        if str(count).encode() != count_text or count > LIMIT:
            raise ValueError('invalid record size')
        position = stop + 1
        end = position + count
        if end > len(data):
            raise ValueError('truncated record')
        if len(out) >= 200000:
            raise ResourceLimit('too many bundle records')
        out.append((kind, data[position:end]))
        position = end

def rational(text):
    n, d = text.split('/')
    return Fraction(int(n, 16), int(d, 16))

def output_mesh(data):
    lines = data.decode('ascii').splitlines()
    version = lines[0]
    if version not in ('TESS1', 'TESS2'):
        raise ValueError('unsupported patch certificate')
    nr = int(lines[4])
    position = 6 + nr
    if version == 'TESS2':
        if lines[position] != 'RUN2':
            raise ValueError('missing run request')
        owners = int(lines[position + 7])
        position += 19 + owners
    for section in range(2):
        nv, nf, ne = map(int, lines[position:position+3])
        position += 8
        points, ids = [], []
        for _ in range(nv):
            position += 2
            if version == 'TESS2':
                ids.append(int(lines[position])); position += 1
            else:
                ids.append(len(ids))
            points.append(tuple(rational(x) for x in lines[position:position+3]))
            position += 3
        faces = []
        for _ in range(nf):
            faces.append(tuple(map(int, lines[position:position+3])))
            position += 4 if version == 'TESS2' else 3
        position += ne * (8 if version == 'TESS2' else 4)
        if section == 1:
            if lines[position:] != ['END']:
                raise ValueError('trailing patch data')
            return points, faces, ids

def verify(args):
    request = records(args.request, b'TESS-ASSET-REQUEST1')
    bundle = records(args.bundle, b'TESS-ASSET1')
    for kind in ('SOURCE', 'OPTIONS'):
        expected = [data for key, data in request if key == kind]
        actual = [data for key, data in bundle if key == kind]
        if len(expected) != 1 or actual != expected:
            raise ValueError(kind + ' binding mismatch')
    source = bounded_read(args.source)
    if source != next(data for key, data in request if key == 'SOURCE'):
        raise ValueError('caller-held source mismatch')
    obj = bounded_read(args.obj)
    if [data for key, data in bundle if key == 'OBJ'] != [obj]:
        raise ValueError('actual OBJ bytes mismatch')
    requests = [data for key, data in request if key == 'PATCH_REQUEST']
    if [data for key, data in bundle if key == 'PATCH_REQUEST'] != requests:
        raise ValueError('caller-held patch requests mismatch')
    request_maps = [json.loads(data) for key, data in request if key == 'REQUEST_MAP']
    maps = [json.loads(data) for key, data in bundle if key == 'PATCH_MAP']
    exact = [data for key, data in bundle if key == 'PATCH_EXACT']
    rounded = [data for key, data in bundle if key == 'PATCH_ROUNDED']
    if not requests or len({len(requests),len(maps),len(exact),len(rounded),len(request_maps)}) != 1:
        raise ValueError('patch record count mismatch')
    vertices, faces = [], []
    for line in obj.decode('ascii').splitlines():
        words = line.split()
        if not words or words[0].startswith('#'):
            continue
        if words[0] == 'v' and len(words) == 4:
            vertices.append(tuple(Fraction.from_float(float(x)) for x in words[1:]))
        elif words[0] in ('g', 'o', 'usemtl', 's'):
            continue
        elif words[0] == 'f' and len(words) == 4:
            faces.append(tuple(int(x)-1 for x in words[1:]))
        else:
            raise ValueError('unexpected geometry-only OBJ syntax')
    covered, sources = set(), set()
    with tempfile.TemporaryDirectory() as temporary:
        temporary = pathlib.Path(temporary)
        for i, (req, ex, rd, mapping, initial) in enumerate(zip(requests, exact, rounded, maps, request_maps)):
            for key in ('patch','source_faces','input_global_vertices'):
                if mapping[key] != initial[key]:
                    raise ValueError('patch source mapping mismatch')
            for source_face in mapping['source_faces']:
                if source_face in sources:
                    raise ValueError('duplicate source face ownership')
                sources.add(source_face)
            points, local_faces, ids = output_mesh(rd)
            indices = mapping['output_global_vertices']
            seed_count = len(initial['input_global_vertices'])
            if (indices[:seed_count] != initial['input_global_vertices'] or
                    ids[:seed_count] != initial['output_stable_ids']):
                raise ValueError('original vertex provenance mismatch')
            if len(indices) != len(points) or mapping['output_stable_ids'] != ids:
                raise ValueError('vertex mapping mismatch')
            for j, point in zip(indices, points):
                if not 0 <= j < len(vertices) or vertices[j] != point:
                    raise ValueError('actual rounded OBJ coordinate mismatch')
            start = mapping['output_global_face_start']
            for j, face in enumerate(local_faces, start):
                if j in covered or not 0 <= j < len(faces) or faces[j] != tuple(indices[k] for k in face):
                    raise ValueError('actual OBJ face mapping mismatch')
                covered.add(j)
            req_path = temporary / 'request.tess'
            result_path = temporary / 'result.tess'
            req_path.write_bytes(req)
            for artifact in (ex, rd):
                result_path.write_bytes(artifact)
                checked = subprocess.run([args.lean_checker, str(req_path), str(result_path)],
                    capture_output=True, text=True, timeout=args.timeout)
                if checked.returncode == 3:
                    raise ResourceLimit(f'Lean resource limit on patch {i}: {checked.stderr.strip()}')
                if checked.returncode:
                    raise ValueError(f'Lean rejected patch {i}: {checked.stderr.strip()}')
    if covered != set(range(len(faces))):
        raise ValueError('uncertified OBJ faces')
    audited=subprocess.run([args.audit_exe,'--max-operations','2000000000',args.obj],
        capture_output=True,text=True,timeout=args.timeout)
    if audited.returncode == 3:
        raise ResourceLimit('assembled OBJ audit resource limit: '+audited.stderr.strip())
    if audited.returncode:
        raise ValueError('assembled OBJ audit failed: '+audited.stderr.strip())
    print(f'checked {len(requests)} patches, {len(faces)} actual OBJ triangles; caller-held source/request bound')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source','request','bundle','obj','lean-checker','audit-exe'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--timeout', type=int, default=120)
    try:
        verify(parser.parse_args())
    except (ResourceLimit, MemoryError, RecursionError, subprocess.TimeoutExpired) as error:
        parser.exit(3, str(error) + '\n')
    except (ValueError, KeyError, IndexError, TypeError, OSError) as error:
        parser.exit(1, str(error) + '\n')
