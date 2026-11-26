#!/usr/bin/env python3
"""Read-only metadata inventory. PAYLOAD is prepended by the submitting host.

Never opens an archive or emits source, object, receipt, or log bodies.
Row001 is limited to matching source/object file pins; its evidence is omitted.
"""
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import time

START = time.monotonic()
BASE = Path('/workspace/p26-continuation-59264dd64286')
ROWS = PAYLOAD['rows']
BY_MODULE = {row['module']: row for row in ROWS}
CACHE = {}
ERRORS = []


def fp(path):
    path = Path(path)
    st = path.stat()
    if not stat.S_ISREG(st.st_mode):
        raise ValueError('not_regular_file: ' + str(path))
    key = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns)
    if key not in CACHE:
        h = hashlib.sha256()
        with path.open('rb') as incoming:
            for chunk in iter(lambda: incoming.read(1024 * 1024), b''):
                h.update(chunk)
        after = path.stat()
        if (after.st_size, after.st_mtime_ns) != (st.st_size, st.st_mtime_ns):
            raise ValueError('file_changed_during_hash: ' + str(path))
        CACHE[key] = {'bytes': st.st_size, 'sha256': h.hexdigest()}
    return {'path': str(path), **CACHE[key]}


def same(actual, expected):
    return all(actual.get(key) == value for key, value in expected.items()
               if key in ('bytes', 'sha256'))


def read_json(path):
    path = Path(path)
    if path.suffix != '.json' or 'row001' in str(path).lower():
        raise ValueError('out_of_metadata_scope: ' + str(path))
    return json.loads(path.read_text())


def try_pin(path, expected=None):
    try:
        path = Path(path)
        if not path.is_file():
            return None
        if expected and 'bytes' in expected and path.stat().st_size != expected['bytes']:
            return None
        actual = fp(path)
        if expected is None or same(actual, expected):
            return actual
    except OSError:
        return None
    return None


def pin_schema(value):
    if isinstance(value, dict):
        return {key: sorted(child) if isinstance(child, dict) else
                ('list:' + (str(sorted(child[0])) if child and isinstance(child[0], dict)
                            else type(child[0]).__name__ if child else 'empty'))
                if isinstance(child, list) else type(child).__name__
                for key, child in value.items()}
    return type(value).__name__


evidence = []
row_acceptances = {}
schemas = {}
finite_stage = BASE / 'cell01-rest-finite-v2'
for name, ordinals in [('cell01-batch-A-v2', range(2, 50)),
                       ('cell01-batch-B-v2', range(50, 98)),
                       ('cell01-rows107-143-v2', range(107, 144))]:
    root = finite_stage / 'verification' / name
    entry = {'attempt_root': str(root), 'expected_ordinals': list(ordinals)}
    if not root.is_dir():
        entry['exists'] = False
        evidence.append(entry)
        continue
    run_path, success_path = root / 'RUN.json', root / 'SUCCESS.json'
    run, success = read_json(run_path), read_json(success_path)
    entry.update({'exists': True, 'run': fp(run_path), 'success': fp(success_path),
                  'status': success.get('status'),
                  'accepted_targets': success.get('accepted_targets'),
                  'record_count': len(success.get('records', [])),
                  'completed_rows_exact': success.get('completed_rows') == list(ordinals),
                  'runtime_context_sha256': run.get('runtime_context_sha256'),
                  'context_refs': {key: run.get(key) for key in
                                   ('input_fingerprints', 'supplier_installation',
                                    'supplier_manifest', 'driver', 'mature_helper',
                                    'verifier_manifest', 'lean_binary', 'leanchecker_binary')},
                  'row_source_object_pin_matches': 0,
                  'chain_receipt_pins_match': 0})
    for ordinal in ordinals:
        module = f'ImbalancedChen.P2OriginalSaving19Cell01Row{ordinal:03d}Finite'
        ra_path = root / module.split('.')[-1] / 'ROW_ACCEPTED.json'
        ra = read_json(ra_path)
        if (ra.get('module') != module or ra.get('original_ordinal') != ordinal or
                not same(ra['source'], BY_MODULE[module]['source'])):
            ERRORS.append({'kind': 'row_acceptance_identity_mismatch', 'module': module})
            continue
        source, obj = try_pin(ra['source']['path'], ra['source']), try_pin(ra['object']['path'], ra['object'])
        if source and obj:
            entry['row_source_object_pin_matches'] += 1
            row_acceptances[module] = {'source': source, 'object': obj,
                                       'accepted_row': fp(ra_path),
                                       'chain': ra.get('chain', [])}
        else:
            ERRORS.append({'kind': 'row_source_or_object_pin_mismatch', 'module': module})
        for pin in ra.get('chain', []):
            if try_pin(pin['path'], pin):
                entry['chain_receipt_pins_match'] += 1
            else:
                ERRORS.append({'kind': 'row_chain_pin_mismatch', 'module': module})
        if ordinal == 2:
            schemas = {'RUN': pin_schema(run), 'SUCCESS': pin_schema(success),
                       'ROW_ACCEPTED': pin_schema(ra)}
            for mode in ('normal', 'kernel', 'owned'):
                p = ra_path.parent / (mode + '-result.json')
                result = read_json(p)
                command = read_json(result['command']['path'])
                schemas[mode + '_result'] = pin_schema(result)
                schemas[mode + '_command'] = pin_schema(command)
    evidence.append(entry)

known = {}
for index, row in enumerate(ROWS):
    module = row['module']
    rel = module.replace('.', '/')
    source = obj = None
    if module in row_acceptances:
        source = row_acceptances[module]['source']
        obj = row_acceptances[module]['object']
        row['expected_object'] = {key: obj[key] for key in ('bytes', 'sha256')}
    source_hints = list(row.get('source_hint', []))
    object_hints = list(row.get('object_hint', []))
    for stage in ('cell01-rest-finite-v2', 'cell01-row001-finite', 'cell01-row000'):
        source_hints.append(str(BASE / stage / 'project' / (rel + '.lean')))
        object_hints.append(str(BASE / stage / 'objects' / (rel + '.olean')))
    if source is None:
        for path in source_hints:
            source = try_pin(path, row['source'])
            if source:
                break
    if obj is None and row.get('expected_object'):
        for path in object_hints:
            obj = try_pin(path, row['expected_object'])
            if obj:
                break
    known[index] = {'source': source, 'object': obj}

# Only exact requested module filenames are candidates. The directory walk
# never reads archive files or receipt/log contents and excludes the blocked
# row001 completed-evidence directory entirely.
missing_names = {}
for index, row in enumerate(ROWS):
    stem = row['module'].split('.')[-1]
    if known[index]['source'] is None:
        missing_names[stem + '.lean'] = (index, 'source')
    if known[index]['object'] is None:
        missing_names[stem + '.olean'] = (index, 'object')
top_dirs = sorted(str(p) for p in Path('/workspace').iterdir()
                  if p.is_dir() and not p.name.startswith('.'))
scan_roots = [Path(path) for path in top_dirs
              if Path(path).name.startswith(('p26', 'p25'))]
visited = 0
candidates_without_accepted_pin = collections.defaultdict(list)
for scan_root in scan_roots:
    if not missing_names:
        break
    for folder, dirs, files in os.walk(scan_root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if not d.startswith('.')
                         and not ('row001' in d.lower() and 'completed' in d.lower())
                         and d not in ('node_modules', '__pycache__'))
        visited += 1
        if visited > 200000:
            ERRORS.append({'kind': 'directory_scan_bound_hit'})
            break
        for name in set(files).intersection(missing_names):
            index, kind = missing_names[name]
            path = Path(folder) / name
            if path.is_symlink():
                continue
            row = ROWS[index]
            expected = row['source'] if kind == 'source' else row.get('expected_object')
            if expected is None:
                actual = try_pin(path)
                if actual and len(candidates_without_accepted_pin[index]) < 5:
                    candidates_without_accepted_pin[index].append(actual)
                continue
            actual = try_pin(path, expected)
            if actual:
                known[index][kind] = actual
                del missing_names[name]

groups = collections.defaultdict(list)
additional_objects = []
sidecars = []
missing = []
matched_source = matched_object = complete = 0
canonical_complete = additional_complete = 0
for index, row in enumerate(ROWS):
    source, obj = known[index]['source'], known[index]['object']
    matched_source += source is not None
    matched_object += obj is not None
    rel = row['module'].replace('.', '/')
    source_root = source['path'][:-len(rel + '.lean')] if source else None
    object_root = obj['path'][:-len(rel + '.olean')] if obj else None
    groups[(source_root, object_root)].append(index)
    if source and obj:
        complete += 1
        if row['class'] == 'canonical':
            canonical_complete += 1
        else:
            additional_complete += 1
    if row['class'] != 'canonical' and obj:
        additional_objects.append([index, obj['bytes'], obj['sha256']])
    if not source or not obj:
        missing.append({'index': index, 'module': row['module'],
                        'source_missing': source is None, 'object_missing': obj is None})
    if obj:
        op = Path(obj['path'])
        paths = [Path(str(op) + '.server'), Path(str(op) + '.private'), op.with_suffix('.ir')]
        for path in paths:
            actual = try_pin(path)
            if actual:
                sidecars.append({'index': index, 'pin': actual})

export_refs = []
for item in PAYLOAD['evidence_refs']:
    verified = {'name': item['name']}
    for key in ('manifest', 'review_report'):
        expected = item[key]
        actual = try_pin(expected['path'], expected)
        verified[key] = {'expected': expected, 'matches': actual is not None}
    export_refs.append(verified)

result = {
    'schema': 'p26_p3_supplier_metadata_inventory_result_v1',
    'status': 'METADATA_CHECK_FINISHED' if not ERRORS else 'METADATA_CHECK_HAS_ERRORS',
    'expected_suppliers': len(ROWS), 'source_manifest_sha256': PAYLOAD['source_manifest_sha256'],
    'supplier_delta_sha256': PAYLOAD['supplier_delta_sha256'],
    'source_matches': matched_source, 'object_matches': matched_object,
    'complete_source_object_pairs': complete, 'canonical_complete': canonical_complete,
    'additional_complete': additional_complete, 'sidecar_count': len(sidecars),
    'provider_groups': [{'source_root': a, 'object_root': b, 'indices': indices}
                        for (a, b), indices in groups.items()],
    'additional_object_pins': additional_objects, 'sidecars': sidecars, 'missing': missing,
    'unproven_object_candidates': dict(candidates_without_accepted_pin),
    'finite_attempts': evidence, 'export_metadata': export_refs,
    'schema_sample_row002': schemas, 'errors': ERRORS,
    'scan_roots': list(map(str, scan_roots)), 'workspace_directory_names': top_dirs,
    'visited_directories': visited, 'unique_file_hashes': len(CACHE),
    'elapsed_seconds': round(time.monotonic() - START, 3),
    'archive_opened': False, 'row001_receipt_or_log_body_read': False,
    'source_or_object_bodies_emitted': False, 'proof_command_executed': False,
    'remote_file_written': False,
    'acceptance_scope': 'Locations and byte identity only; full chain and runtime validation remains required.'}
print(json.dumps(result, sort_keys=True, separators=(',', ':')))
