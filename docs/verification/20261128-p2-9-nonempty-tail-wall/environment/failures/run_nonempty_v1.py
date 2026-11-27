#!/usr/bin/env python3
"""One exact NonemptyTailWallCount target; no supplier proof replay or network I/O.

The original controller supplies only AST-selected helpers, never its main.
All old authority metadata stays in place. Recovery indexes may relocate exact
accepted bytes; they cannot bless different bytes or an unknown imported part.
"""
import argparse
import ast
import collections
import datetime
import fcntl
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time
import tomllib
import traceback

P = pathlib.Path
sys.dont_write_bytecode = True
TARGET = 'ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount'
OLD_TARGET = 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall'
SOURCE_SHA = '1d95db22b754d89b3d7336d6c66b64733bd7600aab5d22ed53a5f5b1d5294e1a'
SOURCE_BLOB = 'eaaa2b2d78c26668c3c4d54dca00876cd5bc1c8a'
OLD_BASE = P('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
OLD_OUT = OLD_BASE / 'verification-finset-prod-resume-v6'
OLD_ROOT = OLD_BASE / 'project'
OLD_LIB = OLD_ROOT / '.lake/build/lib/lean'
RECEPTION = P('/workspace/p29-nonempty-inputs-20261126-14206fd')
PIN = 'leanprover/lean4:v4.33.0-rc1'
TOOLCHAIN = P('/workspace/toolchains/lean-4.33.0-rc1-linux')
MATHLIB_REV = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
HELPER_SHA = 'f509c0fec28d99291ee224920dadb68958cbaa6f243100e7e3696ebbdd2805ea'
MANIFEST_SHA = '9c6092358690df4615ae8f99f2383e06528f18077b25448c2a724569ac393a02'
OLD_GRAPH_SHA = '9ca216b1d0c19c50050f2d16028359ceb42d6f3f3f2fc4ac10a9d389413de8f8'
INDEX_SHA = '2b8b20b150f16b54c1be3ccb39df33f292c92767ef1f94bbd011b9a6536cce7f'
RECEIPT_SHA = '1104d485e61164f2b2c1eb6e7c7a06ac4af212599cec0c511f0299106d17d6c3'
TOOLS = {
    'ci_runtime_guard.py': '837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877',
    'run_guarded.py': 'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526',
    'validate_member_roots_owned.py': 'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201',
}
FACETS = {'.olean', '.olean.server', '.olean.private', '.ir.sig', '.ir'}
HELPERS = {'stamp', 'save', 'utc', 'stage', 'compile_audit_text', 'named_kernel', 'full_owned'}
protected = {}
relocations = {}
relocation_observations = {}
runs = []
owned_base = False
active_run = False


class VerificationError(RuntimeError):
    pass


def require(condition, message, detail=None):
    if not condition:
        raise VerificationError(message + (': ' + json.dumps(detail, ensure_ascii=False) if detail is not None else ''))


def sha(path):
    with P(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def stamp(path):
    s = P(path).stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_exact(path, data):
    """Idempotent exclusive creation, rejecting symlinks and changed content."""
    path = P(path)
    require(not path.is_symlink(), 'Refusing a symlink write', str(path))
    require(all(not p.is_symlink() for p in path.parents), 'Write parent is a symlink', str(path))
    if path.exists():
        require(path.is_file() and path.read_bytes() == data, 'Existing output differs; refusing overwrite', str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def put_json(path, data, compact=False):
    text = json.dumps(data, ensure_ascii=False, sort_keys=True,
                      separators=(',', ':') if compact else None,
                      indent=None if compact else 2) + '\n'
    write_exact(path, text.encode())


def claim_base(path, resume):
    path = P(path)
    require(not path.is_symlink(), 'Independent base must not be a symlink', str(path))
    if resume:
        require(path.is_dir() and (path / 'RUN_IDENTITY.json').is_file(), 'No recognized run to resume', str(path))
        return False
    require(not path.exists(), 'Independent base already exists; inspect it and use --resume', str(path))
    path.mkdir()
    return True


def check_identity(expected):
    path = P(expected['path'])
    require(path.is_absolute() and path.is_file(), 'Missing bound file', str(path))
    require(str(path.resolve(strict=True)) == expected['path'], 'Bound path is not its exact resolved path', str(path))
    before = stamp(path)
    digest = sha(path)
    require(stamp(path) == before, 'File changed while hashing', str(path))
    require('bytes' not in expected or before[2] == expected['bytes'], 'Bound bytes differ', str(path))
    require(digest == expected['sha256'], 'Bound sha256 differs', str(path))
    return {'path': str(path), 'bytes': before[2], 'sha256': digest}


def select_identity(original):
    """An explicit relocation preserves identity bytes and exposes old absence."""
    entry = relocations.get(original['path'])
    if entry is None:
        return check_identity(original)
    require(entry['original'] == original, 'Recovery does not join the exact accepted identity', original)
    old = P(original['path'])
    if old.is_file():
        check_identity(original)  # Do not hide a changed original behind a relocation.
        status = 'ORIGINAL_STILL_EXACT'
    else:
        require(not old.exists() or old.is_symlink(), 'Original has become a non-file', str(old))
        status = 'ORIGINAL_MISSING'
    selected = check_identity(entry['selected'])
    relocation_observations[original['path']] = {'original': original, 'selected': selected,
                                              'original_observation': status, 'provenance': entry['provenance']}
    return selected


def protect(path, expected_sha=None, expected_bytes=None):
    path = P(path).resolve(strict=True)
    expected = {'path': str(path), 'sha256': expected_sha or sha(path)}
    if expected_bytes is not None:
        expected['bytes'] = expected_bytes
    identity = check_identity(expected)
    previous = protected.setdefault(str(path), identity)
    require(previous == identity, 'Protected file identity conflict', str(path))
    return identity


def load_pinned(path, expected_sha, expected_bytes=None):
    identity = protect(path, expected_sha, expected_bytes)
    with P(identity['path']).open() as stream:
        return json.load(stream)


def load_relocations(path, expected_sha):
    require(bool(path) == bool(expected_sha), 'Recovery file and SHA must be supplied together')
    if not path:
        return {}
    data = load_pinned(path, expected_sha)
    require(data['schema'] == 'p29_exact_old_byte_relocations_v1', 'Unexpected recovery schema')
    result = {}
    for row in data['mappings']:
        old, new = row['original'], row['selected']
        require(set(old) == set(new) == {'path', 'bytes', 'sha256'}, 'Invalid recovery identity fields')
        require(old['bytes'] == new['bytes'] and old['sha256'] == new['sha256'], 'Recovery changes accepted bytes', row)
        require(P(old['path']).is_absolute() and P(new['path']).is_absolute(), 'Recovery paths must be absolute')
        require(P(new['path']).is_relative_to('/workspace/p29-recovered-inputs-20261128'), 'Recovery escapes the independent recovery root')
        require(old['path'] not in result and isinstance(row.get('provenance'), dict), 'Duplicate or unprovenanced recovery row')
        result[old['path']] = row
    return result


def merge_parts(*groups):
    result = {}
    for rows in groups:
        for row in rows:
            key = (row['module'], row['facet'])
            require(row['facet'] in FACETS, 'Unrecognized input facet', key)
            if key in result:
                require(result[key]['identity'] == row['identity'], 'Module/facet identity conflict', key)
            else:
                result[key] = row
    return result


def relocate_part(row):
    original = row['identity']
    selected = select_identity(original)
    result = {**row, 'identity': selected, 'qualified_identity': original}
    if original['path'] in relocations:
        result.pop('stat_snapshot', None)
    elif 'stat_snapshot' in row:
        require(stamp(selected['path']) == row['stat_snapshot'], 'Accepted part stat changed', original['path'])
    return result


def source_imports(text):
    return re.findall(r'^import\s+(\S+)', text, re.M)


def adapt_lakefile(raw):
    before = tomllib.loads(raw.decode())
    expected = [{'name': 'ImbalancedChen', 'roots': [OLD_TARGET], 'globs': [OLD_TARGET]}]
    require(before.get('lean_lib') == expected, 'Unexpected original Lake target configuration')
    require([r['name'] for r in before['require']] == ['mathlib'], 'Unexpected Lake requirements')
    require(raw.count(OLD_TARGET.encode()) == 2, 'Unexpected extra target name occurrences')
    result = raw.replace(OLD_TARGET.encode(), TARGET.encode())
    after = tomllib.loads(result.decode())
    changed = dict(before)
    changed['lean_lib'] = [{'name': 'ImbalancedChen', 'roots': [TARGET], 'globs': [TARGET]}]
    require(after == changed, 'Lake adaptation changed more than the root and glob')
    return result


def symlink_exact(destination, selected):
    destination, selected = P(destination), P(selected)
    require(selected.exists(), 'Selected link target is missing', str(selected))
    require(all(not p.is_symlink() for p in destination.parents), 'Symlink destination parent escapes owned tree', str(destination))
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.is_symlink():
        require(os.readlink(destination) == str(selected), 'Existing selection changed', str(destination))
    else:
        require(not destination.exists(), 'Refusing existing non-link selection', str(destination))
        destination.symlink_to(selected, target_is_directory=selected.is_dir())


def bind_parts(rows, authorities):
    records, missing, seen = [], [], set()
    for row in rows:
        module = row['module']
        leaf = module.rsplit('.', 1)[-1]
        for part in row['parts']:
            resolved, requested = P(part['resolved_path']), P(part['path'])
            require(resolved.name.startswith(leaf + '.'), 'Imported module/path mismatch', part)
            facet = resolved.name[len(leaf):]
            key = (module, facet)
            require(facet in FACETS and key not in seen, 'Duplicate or invalid imported part', key)
            seen.add(key)
            require(requested.resolve(strict=True) == resolved.resolve(strict=True), 'Probe path no longer resolves as recorded', part)
            known = authorities.get(key)
            if known is None:
                identity = check_identity({'path': str(resolved), 'sha256': sha(resolved)})
                missing.append({'module': module, 'facet': facet, 'identity': identity,
                                'requested_path': str(requested), 'authority': 'UNQUALIFIED'})
                continue
            require(str(resolved) == known['identity']['path'], 'Actual path differs from accepted selection', {'key': key, 'actual': str(resolved), 'expected': known['identity']['path']})
            identity = check_identity(known['identity'])
            records.append({'module': module, 'facet': facet, 'identity': identity,
                            'qualified_identity': known.get('qualified_identity', identity),
                            'requested_path': str(requested), 'stat_snapshot': stamp(resolved),
                            'authority': known.get('authority', 'pinned_input'),
                            'provider': known.get('provider', {})})
    return {'parts': records, 'missing': missing}


def compare_pre_post(before, after):
    old, new = merge_parts(before), merge_parts(after)
    require(set(new) - set(old) == {(TARGET, '.olean')} and not (set(old) - set(new)),
            'Postprobe must add only the single target olean', {'added': sorted(set(new) - set(old)), 'missing': sorted(set(old) - set(new))})
    for key, row in old.items():
        require(row['identity'] == new[key]['identity'], 'Old input changed after normal', key)


def verify_final_part_stability(parts):
    for number, row in enumerate(parts, 1):
        check_identity(row['identity'])
        if number % 4000 == 0:
            print(json.dumps({'stage': 'final-all-actual-byte-stability', 'parts_hashed': number,
                              'total': len(parts)}), flush=True)


def load_helpers(path):
    protect(path, HELPER_SHA)
    raw = P(path).read_text()
    tree = ast.parse(raw)
    nodes = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in HELPERS]
    nodes += [n for n in tree.body if isinstance(n, ast.Assign) and
              any(isinstance(t, ast.Name) and t.id == 'AUDIT_TEMPLATE' for t in n.targets)]
    require(len(nodes) == len(HELPERS) + 1, 'Original helper AST selection is incomplete')
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), 'exec'), globals())
    return {n.name if isinstance(n, ast.FunctionDef) else 'AUDIT_TEMPLATE':
            hashlib.sha256(ast.get_source_segment(raw, n).encode()).hexdigest() for n in nodes}


def successful_stage(label, command, stdin=None):
    path = out / (label + '-process.json')
    if not path.exists():
        return None
    record = json.loads(path.read_text())
    require(record['exit_code'] == 0, 'A failed stage is preserved and is not automatically rerun', label)
    require(record['command'] == command and record['cwd'] == str(root), 'Resumed command differs', label)
    require(record['log_path'] == str(out / (label + '.log')), 'Resumed log path differs', label)
    require(sha(record['log_path']) == record['log_sha256'], 'Completed stage log changed', label)
    require(record.get('stdin_sha256') == (hashlib.sha256(stdin).hexdigest() if stdin is not None else None), 'Resumed stdin differs', label)
    if not any(r['stage'] == label for r in runs):
        runs.append(record)
    return record


def begin_invocation(label, command, stdin=None):
    path = out / (label + '-invocation.json')
    require(not path.exists() and not (out / (label + '.log')).exists(), 'Interrupted stage needs explicit inspection; refusing a replay', label)
    put_json(path, {'command': command, 'cwd': str(root), 'started_utc': utc(),
                    'stdin_sha256': hashlib.sha256(stdin).hexdigest() if stdin is not None else None})


def run_stage_once(label, command, stdin=None, **kwargs):
    old = successful_stage(label, command, stdin)
    if old is not None:
        print(json.dumps({'stage': label, 'status': 'REUSED_EXACT_SUCCESS', 'new_invocations': 0}), flush=True)
        return old
    begin_invocation(label, command, stdin)
    return stage(label, command, stdin=stdin, **kwargs)


def verify_setup_record(record, command, state_file, log_file):
    require(record['exit_code'] == 0 and record['command'] == command, 'Prior setup did not complete successfully')
    require(sha(log_file) == record['log_sha256'], 'Setup log changed')
    require(sha(state_file) == record['state_sha256'], 'Original prepared state changed')


def probe_once(label, roots):
    code = compile_audit_text(roots)
    write_exact(out / (label + '.lean'), code)
    run_stage_once(label, viewprefix + ['lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', '--stdin'], stdin=code, allow_audit=True)
    with (out / (label + '.log')).open() as stream:
        rows = [json.loads(line[len('P29_ACTUAL_IMPORT '):]) for line in stream if line.startswith('P29_ACTUAL_IMPORT ')]
    require(rows and len(rows) == len({r['module'] for r in rows}) and set(roots) <= {r['module'] for r in rows}, 'Incomplete actual import graph', label)
    return rows


def check_headers(rows, expected_projects, sources, old_headers):
    actual = {r['module']: r for r in rows}
    require({m for m in actual if m.startswith('ImbalancedChen.')} == set(expected_projects), 'Actual project module set differs')
    for module, row in actual.items():
        if module in old_headers:
            old = old_headers[module]
            require(row['is_module'] == old['is_module'] and row['direct_imports'] == old['direct_imports'], 'Accepted compiled header changed', module)
        if module in sources:
            # All source files are exact pinned originals. No imports are inferred from names.
            declared = source_imports(P(sources[module]['path']).read_text())
            require([m for m in row['direct_imports'] if m != 'Init'] == declared, 'Compiled header/source import mismatch', module)


def qualify_probe(label, rows, authorities, expected_projects, sources, old_headers):
    check_headers(rows, expected_projects, sources, old_headers)
    bound = bind_parts(rows, authorities)
    if bound['missing']:
        missing = {'schema': 'p29_nonempty_unqualified_actual_parts_v1', 'probe': label,
                   'probe_log_sha256': sha(out / (label + '.log')), 'missing_count': len(bound['missing']),
                   'missing': bound['missing'], 'normal_invocations_permitted': 0,
                   'successful_probe_is_reusable': True, 'same_pin_is_not_authority': True}
        digest = hashlib.sha256(json.dumps(missing, sort_keys=True).encode()).hexdigest()[:12]
        path = out / ('MISSING_INPUT_AUTHORITIES-' + digest + '.json')
        put_json(path, missing)
        print('P29_MISSING ' + json.dumps({'path': str(path), 'count': len(bound['missing']),
                                          'first': bound['missing'][0]}), flush=True)
        raise VerificationError('Actual import parts lack exact old qualification; see ' + str(path))
    data = {'schema': 'p29_nonempty_exact_actual_input_parts_v1', 'module_count': len(rows),
            'part_count': len(bound['parts']), 'actual_modules': rows, 'parts': bound['parts'],
            'unknown_parts': 0, 'supplier_proof_replays': 0}
    path = out / (label + '-bindings.json')
    if path.exists():
        prior = json.loads(path.read_text())
        require(prior == data, 'Previously qualified import binding changed', label)
    else:
        put_json(path, data, compact=True)
    return data


def verify_guard_sources():
    rows = [json.loads(line) for line in guardlog.read_text().splitlines()]
    calls = []
    for row in rows:
        if row['tool'] != 'lean':
            continue
        for arg in row['input_args']:
            if arg.endswith('.lean'):
                path = P(arg) if P(arg).is_absolute() else P(row['cwd']) / arg
                require(path.resolve() == src.resolve(), 'Unauthorized source invocation in complete guard log', row)
                calls.append(row)
    require(len(calls) == 1, 'Expected exactly one new target source invocation', len(calls))
    return calls


def source_outputs():
    paths = [src, lib / (TARGET.replace('.', '/') + '.olean'), lib / (TARGET.replace('.', '/') + '.ilean')]
    require(all(path.is_file() and not path.is_symlink() for path in paths), 'Target source/output must remain regular files')
    return {str(path): protect(path) for path in paths}


def seal_archive(owned_count):
    members = {}
    for path in out.rglob('*'):
        if path.is_file():
            require(not path.is_symlink(), 'Evidence archive must contain regular files', str(path))
            members['verification/' + path.relative_to(out).as_posix()] = path
    for path in [src, root / 'lean-toolchain', root / 'lakefile.toml', root / 'lake-manifest.json',
                 lib / (TARGET.replace('.', '/') + '.olean'), lib / (TARGET.replace('.', '/') + '.ilean')]:
        require(path.is_file() and not path.is_symlink(), 'Target artifact is not a regular file', str(path))
        members['project/' + path.relative_to(root).as_posix()] = path
    for name in TOOLS:
        members['original-tools/' + name] = OLD_BASE / 'original-tools' / name
    members['RUN_IDENTITY.json'] = base / 'RUN_IDENTITY.json'
    manifest = {'schema': 'p29_nonempty_complete_single_target_evidence_v1',
                'files': {name: {'bytes': path.stat().st_size, 'sha256': sha(path)} for name, path in sorted(members.items())},
                'excludes': ['FILE_MANIFEST.json'], 'old_supplier_objects_not_duplicated': True}
    put_json(base / 'FILE_MANIFEST.json', manifest)
    members['FILE_MANIFEST.json'] = base / 'FILE_MANIFEST.json'
    archive = base / 'qualified-nonempty-tail-wall-count.tar.xz'
    if archive.exists():
        transport = json.loads((base / 'ARCHIVE_TRANSPORT.json').read_text())
        check_identity({'path': str(archive), 'bytes': transport['bytes'], 'sha256': transport['sha256']})
        return transport
    with tarfile.open(archive, 'x:xz', preset=6) as stream:
        for name, path in sorted(members.items()):
            stream.add(path, arcname=name, recursive=False)
    transport = {'path': str(archive), 'bytes': archive.stat().st_size, 'sha256': sha(archive),
                 'members': len(members), 'manifest_sha256': sha(base / 'FILE_MANIFEST.json'),
                 'new_module': TARGET, 'new_owned_count': owned_count, 'supplier_replays': 0}
    put_json(base / 'ARCHIVE_TRANSPORT.json', transport)
    return transport


def main():
    global base, root, out, lib, src, base_env, state_path, guardlog, viewprefix, auditor
    global owned_base, active_run, relocations
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-file', required=True, type=P)
    parser.add_argument('--input-index', type=P, default=RECEPTION / 'provenance/NONEMPTY_EXISTING_INPUT_INDEX.json')
    parser.add_argument('--base', type=P, default=P('/workspace/p29-nonempty-20261128'))
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--only-preflight', action='store_true', help='Bind bytes, construct independent view and run original setup, with no Lean compilation or probe')
    parser.add_argument('--recovery-index', type=P)
    parser.add_argument('--recovery-sha256')
    parser.add_argument('--additional-bindings', type=P)
    parser.add_argument('--additional-bindings-sha256')
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Python optimization would disable original helper assertions')
    base = args.base.absolute()
    require(base.parent == P('/workspace') and base.name.startswith('p29-nonempty-') and base != RECEPTION, 'Unexpected independent base', str(base))
    root, out = base / 'project', base / 'verification'
    lib, src = root / '.lake/build/lib/lean', root / (TARGET.replace('.', '/') + '.lean')
    source_pin = protect(args.source_file, SOURCE_SHA, 6727)
    source = args.source_file.read_bytes()
    require(hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest() == SOURCE_BLOB, 'Target Git blob differs')
    index = load_pinned(args.input_index, INDEX_SHA, 65615)
    receipt = load_pinned(RECEPTION / 'BYTE_RECEPTION_RECEIPT.json', RECEIPT_SHA, 67406)
    require(index['target']['module'] == TARGET and index['target']['source']['sha256'] == SOURCE_SHA, 'Wrong target index')
    require(source_imports(source.decode()) == index['target']['source_declared_imports'], 'Target source imports differ')
    relocations = load_relocations(args.recovery_index, args.recovery_sha256)
    manifest = load_pinned(OLD_BASE / 'FILE_MANIFEST.json', MANIFEST_SHA)

    def old_file(name, json_file=True):
        key = 'verification/' + name
        require(key in manifest['files'], 'Old manifest does not contain required evidence', key)
        pin = manifest['files'][key]
        path = OLD_OUT / name
        protect(path, pin['sha256'], pin['bytes'])
        return json.loads(path.read_text()) if json_file else path

    old_graph = old_file('consumer-actual-imports-bindings.json')
    require(sha(OLD_OUT / 'consumer-actual-imports-bindings.json') == OLD_GRAPH_SHA, 'Wrong accepted Omitted graph')
    require(old_graph['module_count'] == 6343 and old_graph['part_count'] == 31075, 'Unexpected old graph counts')
    old_borrowed = old_file('BORROWED_OBJECTS.json')
    old_result = old_file('VALIDATION_RESULTS.json')
    old_outputs = old_file('SOURCE_AND_OUTPUTS_AFTER.json')
    package_view = old_file('REUSED_V4_PACKAGE_VIEW.json')
    native_view = old_file('COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json')
    require(old_result['result'] == 'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED' and old_result['owned_count'] == 13, 'Omitted supplier gates are not the accepted successful result')
    require(all(old_result[k]['exit_code'] == 0 for k in ['normal', 'kernel', 'owned']), 'Failed Omitted supplier stage')
    helper_pins = load_helpers(old_file('driver.py', False))
    for name, digest in TOOLS.items():
        protect(OLD_BASE / 'original-tools' / name, digest)
    owned_base = claim_base(base, args.resume)
    lock = (base / 'controller.lock').open('a+b')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    identity = {'schema': 'p29_nonempty_exact_single_target_run_v1', 'base': str(base), 'module': TARGET,
                'source': {**source_pin, 'git_blob': SOURCE_BLOB}, 'driver_sha256': sha(__file__),
                'old_manifest_sha256': MANIFEST_SHA, 'old_actual_imports_sha256': OLD_GRAPH_SHA,
                'input_index_sha256': INDEX_SHA, 'reception_receipt_sha256': RECEIPT_SHA,
                'original_helper_controller_sha256': HELPER_SHA, 'helper_source_sha256': helper_pins}
    put_json(base / 'RUN_IDENTITY.json', identity)
    active_run = True
    out.mkdir(exist_ok=True)
    write_exact(out / 'driver.py', P(__file__).read_bytes())
    write_exact(src, source)
    for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
        pin = manifest['files']['project/' + name]
        protect(OLD_ROOT / name, pin['sha256'], pin['bytes'])
        raw = (OLD_ROOT / name).read_bytes()
        write_exact(root / name, adapt_lakefile(raw) if name == 'lakefile.toml' else raw)
        protect(root / name)
    require((root / 'lean-toolchain').read_text().strip() == PIN, 'Unexpected Lean pin')
    packages = json.loads((root / 'lake-manifest.json').read_text())['packages']
    paths = package_view['selected_package_paths']
    require(len(paths) == 10 and set(paths) == {r['name'] for r in packages}, 'Package view does not match original manifest')
    require(next(r['rev'] for r in packages if r['name'] == 'mathlib') == MATHLIB_REV, 'Mathlib manifest pin differs')
    for name, path in paths.items():
        symlink_exact(root / '.lake/packages' / name, P(path))
    require(subprocess.check_output(['git', '-C', paths['mathlib'], 'rev-parse', 'HEAD'], text=True).strip() == MATHLIB_REV, 'Mathlib checkout changed')

    old_headers = {r['module']: r for r in old_graph['actual_modules']}
    old_parts = []
    for number, row in enumerate(old_graph['parts'], 1):
        old_parts.append(relocate_part(row))
        if number % 2000 == 0:
            print(json.dumps({'stage': 'old-byte-binding', 'parts_hashed': number, 'total': len(old_graph['parts'])}), flush=True)
    authorities = merge_parts(old_parts)
    old_projects = {m for m, _ in authorities if m.startswith('ImbalancedChen.')}
    require(len(old_projects) == 59 and set(old_borrowed) == old_projects - {OLD_TARGET}, 'Unexpected old project source set')
    sources, project_links = {}, {}
    for module in sorted(old_projects):
        if module == OLD_TARGET:
            path = OLD_ROOT / (module.replace('.', '/') + '.lean')
            pin = {'path': str(path), **old_outputs[str(path)]}
        else:
            b = old_borrowed[module]
            pin = {'path': b['source'], 'bytes': b['source_bytes'], 'sha256': b['source_sha256']}
        sources[module] = select_identity(pin)
        protected[sources[module]['path']] = sources[module]
        direct = [m for m in source_imports(P(sources[module]['path']).read_text()) if m.startswith('ImbalancedChen.')]
        if module != OLD_TARGET:
            require(direct == old_borrowed[module]['direct_project_imports'], 'Old source import projection differs', module)
        require(set(direct) <= old_projects, 'Old source escapes accepted project set', module)
        project_links[module] = authorities[(module, '.olean')]['identity']
    new_rows = []
    require(set(receipt['selected_objects']) == set(index['new_branch_existing_objects']) and len(receipt['selected_objects']) == 13, 'Wrong thirteen-input reception')
    for module, received in receipt['selected_objects'].items():
        fixed = index['new_branch_existing_objects'][module]
        for key in ['bytes', 'sha256']:
            require(received[key] == fixed['object'][key] and received['source'][key] == fixed['source'][key], 'Reception/index byte pin conflict', module)
        require(module not in old_projects, 'Extra project module conflicts with old input', module)
        original = {'path': received['selected_path'], 'bytes': received['bytes'], 'sha256': received['sha256']}
        new_rows.append(relocate_part({'module': module, 'facet': '.olean', 'identity': original,
                                      'authority': 'original_accepted_thirteen_input_reception',
                                      'provider': received['provenance']}))
        sp = received['source']
        sources[module] = select_identity({'path': sp['selected_path'], 'bytes': sp['bytes'], 'sha256': sp['sha256']})
        protected[sources[module]['path']] = sources[module]
        declared = source_imports(P(sources[module]['path']).read_text())
        require(declared == fixed['source_declared_imports'], 'Extra source imports differ from fixed index', module)
        require([m for m in declared if m.startswith('ImbalancedChen.')] == fixed['direct_project_imports'], 'Extra project dependencies differ', module)
    authorities = merge_parts(authorities.values(), new_rows)
    expected_projects = set(index['expected72_input_module_names'])
    require(len(expected_projects) == 72 and set(sources) == expected_projects, 'Selected project union is not the exact expected 72')
    for module in sorted(expected_projects):
        identity_part = authorities[(module, '.olean')]['identity']
        symlink_exact(lib / (module.replace('.', '/') + '.olean'), P(identity_part['path']))
        project_links[module] = identity_part
    require(native_view['selected_native_modules'] == 529, 'Wrong original complete native view')
    for row in native_view['facets']:
        require(not row['module'].startswith('ImbalancedChen.'), 'Native view contains a project module')
        original = {'path': str(P(row['selected_path']).resolve(strict=True)), 'bytes': row['bytes'], 'sha256': row['sha256']}
        chosen = select_identity(original)
        symlink_exact(lib / (row['module'].replace('.', '/') + row['facet']), P(chosen['path']))
    sources[TARGET] = protect(src, SOURCE_SHA, 6727)
    put_json(out / 'SELECTED_PROJECT_SOURCE_OBJECTS.json', {'sources': sources, 'objects': project_links,
              'expected72_input_module_names': sorted(expected_projects), 'old_object_replays': 0})
    put_json(out / 'OMITTED_ACCEPTED_VERSION_JOIN.json', {'index_historical_future_source': index['future_Omitted'],
              'accepted_current_source': sources[OLD_TARGET], 'accepted_current_object': project_links[OLD_TARGET],
              'accepted_validation_sha256': sha(OLD_OUT / 'VALIDATION_RESULTS.json'),
              'source_qualifier_repair_was_accepted_before_this_run': True})
    if args.recovery_index:
        write_exact(out / ('recovery-' + args.recovery_sha256 + '.json'), args.recovery_index.read_bytes())
    put_json(out / 'EXACT_BYTE_RELOCATIONS.json', relocation_observations)
    require(set(relocations) == set(relocation_observations), 'Recovery index contains a path outside the selected accepted inputs', sorted(set(relocations) - set(relocation_observations)))

    # An optional root-reviewed supplement binds previously missing *standard*
    # parts. It never permits a new project/research module or a conflicting key.
    require(bool(args.additional_bindings) == bool(args.additional_bindings_sha256), 'Additional bindings require an exact SHA')
    if args.additional_bindings:
        supplement = load_pinned(args.additional_bindings, args.additional_bindings_sha256)
        require(supplement['schema'] == 'p29_nonempty_accepted_additional_standard_parts_v1', 'Unexpected supplemental authority schema')
        permitted = {'Init', 'Lean', 'Std', 'Lake', 'Mathlib', 'Batteries', 'Qq', 'Aesop', 'Cli', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Plausible'}
        extra = []
        for row in supplement['parts']:
            require(row['module'].split('.')[0] in permitted, 'Supplement cannot qualify research/project inputs', row['module'])
            require(isinstance(row.get('provider'), dict) and row.get('authority') == 'original_accepted_gate_graph', 'Missing original accepted supplement provenance')
            extra.append(relocate_part(row))
        authorities = merge_parts(authorities.values(), extra)
        for row in supplement['actual_modules']:
            if row['module'] in old_headers:
                require(row['direct_imports'] == old_headers[row['module']]['direct_imports'] and row['is_module'] == old_headers[row['module']]['is_module'], 'Supplemental header conflicts with old graph')
            else:
                old_headers[row['module']] = row
        write_exact(out / ('additional-' + args.additional_bindings_sha256 + '.json'), args.additional_bindings.read_bytes())

    guard = OLD_BASE / 'original-tools/ci_runtime_guard.py'
    runner = OLD_BASE / 'original-tools/run_guarded.py'
    owned = OLD_BASE / 'original-tools/validate_member_roots_owned.py'
    base_env = os.environ.copy()
    guard_tree = ast.parse(guard.read_text())
    ambiguous = next(ast.literal_eval(n.value) for n in guard_tree.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'AMBIGUOUS_ENV' for t in n.targets))
    for key in ambiguous:
        base_env.pop(key, None)
    runtime = base / 'runtime'
    runtime.mkdir(exist_ok=True)
    base_env.update(RUNNER_TEMP=str(runtime), LEAN_ACTION_DIR=str(OLD_BASE / 'lean-action'),
                    LEAN_NUM_THREADS='2', ELAN_TOOLCHAIN=PIN, ELAN_HOME='/workspace/.elan',
                    GITHUB_ENV=str(out / 'runtime.env'), GITHUB_PATH=str(out / 'runtime.path'),
                    PYTHONDONTWRITEBYTECODE='1')
    base_env['PATH'] = '/workspace/.elan/bin:' + base_env.get('PATH', '')
    state_path = out / 'runtime-evidence/state.json'
    setup_command = ['python3', str(guard), 'setup', '--evidence', str(state_path.parent)]
    setup = out / 'runtime-setup-process.json'
    if setup.exists():
        record = json.loads(setup.read_text())
        verify_setup_record(record, setup_command, state_path, out / 'runtime-setup.log')
    else:
        require(not state_path.parent.exists() and not (out / 'runtime-setup.log').exists(), 'Interrupted setup must be inspected; no automatic setup replay')
        with (out / 'runtime-setup.log').open('xb') as stream:
            completed = subprocess.run(setup_command, cwd=root, env=base_env, stdout=stream, stderr=subprocess.STDOUT, timeout=120)
        put_json(setup, {'command': setup_command, 'cwd': str(root), 'exit_code': completed.returncode,
                         'log_sha256': sha(out / 'runtime-setup.log'),
                         'state_sha256': sha(state_path) if state_path.is_file() else None})
        require(completed.returncode == 0, 'Original guard setup failed; see runtime-setup.log')
    state = json.loads(state_path.read_text())
    require(state['root'] == str(root) and state['realbin'] == str(TOOLCHAIN / 'bin'), 'Unexpected prepared runtime')
    require(state['shadow'] == str(runtime / 'p0-ci-shadow-toolchain') and
            state['log'] == str(state_path.parent / 'compiler-commands.jsonl'), 'Prepared runtime paths escape the independent run')
    require(state['guard_sha256'] == TOOLS['ci_runtime_guard.py'], 'Prepared guard differs')
    require(state['policy'] == 'Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2', 'Runtime policy changed')
    protect(state_path)
    for mapping in ['runtime_sha256', 'input_sha256', 'action_script_sha256']:
        for path, digest in state[mapping].items():
            protect(path, digest)
    guardlog = P(state['log'])
    runprefix = ['python3', str(runner), '--state', str(state_path)]
    old_paths = [arg.removeprefix('LEAN_PATH=') for arg in old_result['normal']['command'] if arg.startswith('LEAN_PATH=')]
    require(len(old_paths) == 1, 'Missing old composed search path')
    paths = old_paths[0].split(os.pathsep)
    require(paths[0] == str(OLD_LIB) and paths[1] == str(OLD_BASE / 'batteries-native-cache-view-v5/lib'), 'Unexpected old namespace ordering')
    translated = [str(lib) if p == str(OLD_LIB) else str(P(state['shadow']) / 'lib/lean') if p == str(OLD_BASE / 'runtime/p0-ci-shadow-toolchain/lib/lean') else p for p in paths]
    require(all(P(p).is_dir() for p in translated) and str(OLD_LIB) not in translated, 'A selected search path is missing or still uses the erased old project view')
    viewprefix = runprefix + ['lake', 'env', 'env', 'LEAN_PATH=' + os.pathsep.join(translated)]
    put_json(out / 'SEARCH_AND_RUNTIME_BINDING.json', {'LEAN_PATH': translated, 'package_view': package_view,
             'native_view_sha256': sha(OLD_OUT / 'COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json'),
             'original_guard_setup_cli': setup_command, 'old_runtime_not_mutated': True})
    preflight = {'schema': 'p29_nonempty_preflight_v1', 'status': 'PASS_EXACT_BYTES_AND_INDEPENDENT_GUARD_SETUP',
                 'old_parts_freshly_hashed': len(old_parts), 'project_inputs': 72, 'new_target_source_sha256': SOURCE_SHA,
                 'source_normal_kernel_owned_runs': 0, 'relocated_old_paths': len(relocation_observations),
                 'actual_combined_import_graph_qualified': False}
    put_json(out / 'PREFLIGHT.json', preflight)
    if args.only_preflight:
        print('P29_PREFLIGHT ' + json.dumps(preflight), flush=True)
        return

    spec = importlib.util.spec_from_file_location('p29_original_owned_auditor', owned)
    auditor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(auditor)
    run_stage_once('runtime-initial-audit', runprefix + ['python3', str(guard), 'audit', '--state', str(state_path), '--probe'])
    before_rows = probe_once('nonempty-direct-imports', index['target']['source_declared_imports'])
    before = qualify_probe('nonempty-direct-imports', before_rows, authorities, expected_projects, sources, old_headers)
    olean = lib / (TARGET.replace('.', '/') + '.olean')
    ilean = lib / (TARGET.replace('.', '/') + '.ilean')
    normal_command = viewprefix + ['lean', '-DwarningAsError=true', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', '-o', str(olean), '-i', str(ilean), str(src)]
    if not (out / 'normal-build-process.json').exists():
        require(not olean.exists() and not ilean.exists() and not olean.is_symlink() and not ilean.is_symlink(), 'Unrecorded target outputs exist; refusing normal replay')
    normal = run_stage_once('normal-build', normal_command, allow_sources=(str(src.resolve()),))
    produced = source_outputs()
    put_json(out / 'SOURCE_AND_OUTPUTS_AFTER_NORMAL.json', produced)
    target_identity = produced[str(olean)]
    post_authorities = merge_parts(authorities.values(), [{'module': TARGET, 'facet': '.olean',
            'identity': target_identity, 'authority': 'current_normal_output', 'provider': {'source_sha256': SOURCE_SHA}}])
    after_rows = probe_once('consumer-actual-imports', [TARGET])
    after = qualify_probe('consumer-actual-imports', after_rows, post_authorities, expected_projects | {TARGET}, sources, old_headers)
    compare_pre_post(before['parts'], after['parts'])
    put_json(out / 'BEFORE_AFTER_EXACT_OLD_PART_IDENTITY_CHECK.json', {'old_part_count': before['part_count'],
              'every_selected_old_identity_unchanged': True, 'qualified_original_bytes_preserved': True,
              'only_added_part': [TARGET, '.olean'], 'pre_sha256': sha(out / 'nonempty-direct-imports-bindings.json'),
              'post_sha256': sha(out / 'consumer-actual-imports-bindings.json')})
    kernel_command = viewprefix + ['leanchecker', '--verbose', TARGET]
    kernel = successful_stage('named-kernel', kernel_command)
    if kernel is None:
        begin_invocation('named-kernel', kernel_command)
        kernel = named_kernel('named-kernel', [TARGET])
    replayed = [line.removeprefix('replaying ') for line in (out / 'named-kernel.log').read_text().splitlines() if line.startswith('replaying ')]
    require(replayed == [TARGET], 'Named kernel replayed anything other than the single target')
    owned_code = auditor.make_audit_code([TARGET]).encode()
    owned_command = viewprefix + ['lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', '-Dpp.maxSteps=1000000', '--stdin']
    owned_process = successful_stage('full-owned', owned_command, owned_code)
    if owned_process is None:
        begin_invocation('full-owned', owned_command, owned_code)
        owned_process, declarations, inventory, axioms = full_owned('full-owned', [TARGET])
    else:
        declarations, inventory, axioms = auditor.read_audit((out / 'full-owned.log').read_text(), [TARGET], owned_process['exit_code'])
        require((out / 'full-owned.lean').read_bytes() == owned_code, 'Owned audit source changed')
        require(json.loads((out / 'full-owned-DECLARATION_TYPES_AXIOMS.json').read_text()) == declarations, 'Owned declarations changed')
        require(json.loads((out / 'full-owned-INVENTORY_NAME_SET_CHECK.json').read_text()) == inventory, 'Owned inventory changed')
    runtime_final = run_stage_once('runtime-final-audit', runprefix + ['python3', str(guard), 'audit', '--state', str(state_path), '--probe', '--require-source'])
    source_calls = verify_guard_sources()
    require(source_outputs() == produced, 'New target outputs changed during audits')
    for identity_part in protected.values():
        check_identity(identity_part)
    require(set(merge_parts(old_parts)) <= set(merge_parts(after['parts'])), 'An old accepted input is absent from the final actual graph')
    verify_final_part_stability(after['parts'])
    for name, digest in TOOLS.items():
        require(sha(OLD_BASE / 'original-tools' / name) == digest, 'Original tool changed')
    put_json(out / 'SOURCE_AND_OUTPUTS_AFTER.json', produced)
    result = {'schema': 'p29_nonempty_tail_wall_count_validation_v1',
              'result': 'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED', 'module': TARGET,
              'source_git_blob': SOURCE_BLOB, 'source_sha256': SOURCE_SHA, 'source_bytes': 6727,
              'normal': normal, 'kernel': kernel, 'owned': owned_process, 'runtime_final': runtime_final,
              'owned_count': len(declarations), 'inventory': inventory, 'observed_axioms': axioms,
              'normal_warningAsError': True, 'normal_source_invocations': source_calls,
              'actual_input_modules': after['module_count'], 'actual_input_parts': after['part_count'],
              'actual_project_inputs': 72, 'actual_project_modules_including_target': 73,
              'original_guard_runner_owned_parser_unchanged': TOOLS, 'target_normal_invocations': 1,
              'supplier_source_kernel_owned_replays': 0, 'unknown_input_parts': 0,
              'old_qualified_bytes_preserved': True, 'old_part_relocations': len(relocation_observations),
              'direct_Lean_no_Lake_trace_or_setup_output': True, 'full_P2_9_complete': False,
              'whole_standard_import_kernel_replay_claim': False,
              'scope': 'Original explicit-Nonradial NonemptyTailWallCount source only; no mathematical source changes.'}
    put_json(out / 'VALIDATION_RESULTS.json', result)
    transport = seal_archive(len(declarations))
    print('P29_RESULT ' + json.dumps({k: result[k] for k in ['result', 'module', 'owned_count', 'observed_axioms', 'actual_input_modules', 'actual_input_parts']}), flush=True)
    print('P29_ARCHIVE ' + json.dumps(transport), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        failure = {'schema': 'p29_nonempty_preserved_failure_v1', 'error': str(error),
                   'traceback': traceback.format_exc(), 'completed_stages': [r['stage'] for r in runs],
                   'no_automatic_replay': True, 'supplier_proof_replays': 0}
        if active_run and 'out' in globals() and out.is_dir():
            path = out / ('FAILURE-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f') + '.json')
            put_json(path, failure)
        print('P29_FAILURE ' + json.dumps(failure), flush=True)
        raise
