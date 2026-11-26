#!/usr/bin/env python3
"""Globally locate only requested same-byte Lean files; print metadata only."""
import collections
import hashlib
import json
import os
from pathlib import Path
import stat
import time

START = time.monotonic()
ROWS = PAYLOAD['rows']
WANTED = {}
for index, row in enumerate(ROWS):
    stem = row['module'].split('.')[-1]
    WANTED[stem + '.olean'] = (index, 'object')
    WANTED[stem + '.lean'] = (index, 'source')
CACHE = {}
FOUND = collections.defaultdict(lambda: collections.defaultdict(list))
STATS = {'directories': 0, 'regular_candidate_files': 0, 'symlink_candidate_files': 0}
SKIPPED = []
ERRORS = []


def fp(path):
    path = Path(path)
    st = path.stat()
    if not stat.S_ISREG(st.st_mode):
        raise ValueError('not regular')
    key = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns)
    if key not in CACHE:
        h = hashlib.sha256()
        with path.open('rb') as incoming:
            for chunk in iter(lambda: incoming.read(1024 * 1024), b''):
                h.update(chunk)
        after = path.stat()
        if (after.st_size, after.st_mtime_ns) != (st.st_size, st.st_mtime_ns):
            raise ValueError('candidate changed during hash: ' + str(path))
        CACHE[key] = (st.st_size, h.hexdigest())
    size, sha = CACHE[key]
    return {'path': str(path), 'bytes': size, 'sha256': sha}


def same(actual, expected):
    return all(actual[key] == expected[key] for key in ('bytes', 'sha256'))


def onerror(error):
    ERRORS.append({'scan_error': str(error)})


for folder, dirs, files in os.walk('/workspace', followlinks=False, onerror=onerror):
    # .lake is intentionally included. Only irrelevant metadata/generated caches
    # and the blocked row001 completed-evidence directory are excluded.
    dirs[:] = sorted(d for d in dirs if d not in ('.git', '.compile-home', 'node_modules', '__pycache__')
                     and not ('row001' in d.lower() and 'completed' in d.lower()))
    STATS['directories'] += 1
    if time.monotonic() - START > 250:
        ERRORS.append({'scan_budget_exceeded': True})
        break
    for filename in set(files).intersection(WANTED):
        path = Path(folder) / filename
        if path.is_symlink():
            STATS['symlink_candidate_files'] += 1
            continue
        index, kind = WANTED[filename]
        try:
            actual = fp(path)
        except (OSError, ValueError) as error:
            ERRORS.append({'candidate_error': str(error), 'path': str(path)})
            continue
        STATS['regular_candidate_files'] += 1
        FOUND[index][kind].append(actual)

items = []
object_match = source_match = sidecar_count = object_bytes = sidecar_bytes = 0
for index, row in enumerate(ROWS):
    item = {'module': row['module'], 'expected_source': row['source'],
            'expected_object': row['expected_object'], 'source': None,
            'object': None, 'sidecars': [], 'same_object_locations': [],
            'object_variants': []}
    sources = [pin for pin in FOUND[index]['source'] if same(pin, row['source'])]
    objects = [pin for pin in FOUND[index]['object'] if same(pin, row['expected_object'])]
    if sources:
        source_match += 1
        sources.sort(key=lambda pin: (not pin['path'].endswith(row['module'].replace('.', '/') + '.lean'), len(pin['path']), pin['path']))
        item['source'] = sources[0]
        item['same_source_location_count'] = len(sources)
    if objects:
        object_match += 1
        objects.sort(key=lambda pin: (len(pin['path']), pin['path']))
        item['object'] = objects[0]
        item['same_object_locations'] = [pin['path'] for pin in objects]
        object_bytes += objects[0]['bytes']
        op = Path(objects[0]['path'])
        for side in (Path(str(op) + '.server'), Path(str(op) + '.private'), op.with_suffix('.ir')):
            if side.is_file():
                pin = fp(side)
                item['sidecars'].append(pin)
                sidecar_count += 1
                sidecar_bytes += pin['bytes']
    variants = collections.defaultdict(list)
    for pin in FOUND[index]['object']:
        if not same(pin, row['expected_object']):
            variants[(pin['bytes'], pin['sha256'])].append(pin['path'])
    for (size, sha), paths in variants.items():
        item['object_variants'].append({'bytes': size, 'sha256': sha,
                                        'location_count': len(paths), 'example_paths': paths[:5]})
    items.append(item)

print(json.dumps({'schema': 'p26_p3_global_exact_objects_result_v1',
                  'task_scope': 'Only requested 225 canonical Lean source/object filenames',
                  'status': 'SCAN_COMPLETE' if not ERRORS else 'SCAN_ERRORS_OR_INCOMPLETE',
                  'wanted_modules': len(ROWS), 'object_matches': object_match,
                  'source_matches': source_match, 'object_bytes': object_bytes,
                  'sidecar_count': sidecar_count, 'sidecar_bytes': sidecar_bytes,
                  'still_missing_objects': [item['module'] for item in items if not item['object']],
                  'objects_with_different_byte_variants': sum(bool(item['object_variants']) for item in items),
                  'items': items, 'statistics': STATS, 'unique_file_hashes': len(CACHE),
                  'elapsed_seconds': round(time.monotonic() - START, 3), 'errors': ERRORS,
                  'archives_opened': False, 'proof_commands_executed': False,
                  'remote_files_written': False, 'bodies_emitted': False},
                 sort_keys=True, separators=(',', ':')))
