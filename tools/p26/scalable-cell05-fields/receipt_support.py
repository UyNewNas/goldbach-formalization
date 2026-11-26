#!/usr/bin/env python3
"""P3 isolated cell01 verification. Executes supplied Lean sources; writes no Lean.

Usage: python3 tools/p26/Geometry01Decoding_verify.py [--stage STAGE]
The supplied verifier manifest and audit sources must accompany this driver.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time

DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/geometry01')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def fp(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(a.get(k) == b.get(k) for k in ['bytes', 'sha256'])


def read(path):
    return json.loads(Path(path).read_text())


def dump_new(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as out:
        out.write(json.dumps(value, indent=2) + '\n')


def tree_rss(pid):
    total, todo, seen = 0, [pid], set()
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            status = Path(f'/proc/{current}/status').read_text()
            m = re.search(r'(?m)^VmRSS:\s+(\d+)\s+kB', status)
            if m:
                total += int(m.group(1)) * 1024
            todo += [int(x) for x in Path(f'/proc/{current}/task/{current}/children').read_text().split()]
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            pass
    return total


def parse_owned(log_text, module):
    inventory, declarations, completed = [], [], []
    for line in log_text.splitlines():
        for marker, bucket in [('P26_GEOMETRY01_AUDIT_INVENTORY ', inventory),
                               ('P26_GEOMETRY01_AUDIT_DECL ', declarations),
                               ('P26_GEOMETRY01_AUDIT_COMPLETE ', completed)]:
            if line.startswith(marker):
                bucket.append(json.loads(line[len(marker):]))
    assert len(inventory) == len(completed) == 1, 'Missing or duplicate complete ownership inventory'
    inv, done = inventory[0], completed[0]
    assert inv['module'] == done['module'] == module
    names = inv['environment']
    assert names and len(names) == len(set(names))
    assert sorted(names) == sorted(inv['serialized'])
    assert sorted(d['name'] for d in declarations) == sorted(names)
    assert done['count'] == len(names)
    for d in declarations:
        assert d['module'] == module and d['type'] and '⋯' not in d['type']
        assert not d['unsafe'] and not d['partial'] and not d['axiom']
        assert set(d['axioms']) <= ALLOWED, ('Forbidden axiom', d)
    return {'module': module, 'owned_declaration_count': len(names),
            'axioms_union': sorted({a for d in declarations for a in d['axioms']}),
            'inventory': inv, 'declarations': declarations, 'complete': done}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--toolchain-bin', type=Path, default=Path('/toolchains/bin'))
    ap.add_argument('--mathlib', type=Path, default=Path('/mathlib'))
    ap.add_argument('--wall-seconds', type=int, default=900)
    ap.add_argument('--rss-gib', type=int, default=24)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt)
    stage = args.stage.resolve()
    project, objects = stage / 'project', stage / 'objects'
    logs = stage / 'verification'
    assert project.is_dir() and objects.is_dir()
    supplier_path = stage / 'Geometry01Decoding_SUPPLIERS.json'
    verifier_path = Path(__file__).with_name('Geometry01Decoding_VERIFIER.json')
    supplier, verifier = read(supplier_path), read(verifier_path)
    assert same(fp(Path(__file__)), verifier['driver']), 'Driver fingerprint mismatch'
    assert same(fp(supplier_path), verifier['supplier_manifest']), 'Supplier manifest mismatch'
    lean, checker = args.toolchain_bin / 'lean', args.toolchain_bin / 'leanchecker'
    assert lean.is_file() and checker.is_file()
    version = subprocess.run([str(lean), '--version'], text=True, capture_output=True, check=True).stdout.strip()
    assert '4.33.0-rc1' in version and '62eed1db4d67327ec8120be05f1a1b0847d74561' in version, version
    required_packages = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']
    package_roots = [args.mathlib / '.lake/packages' / name / '.lake/build/lib/lean' for name in required_packages]
    for name, path in zip(required_packages, package_roots):
        assert path.is_dir(), ('Missing required mathlib package object root', name, str(path))
    cli_objects = args.mathlib / '.lake/packages/Cli/.lake/build/lib/lean'
    if cli_objects.is_dir():
        package_roots.append(cli_objects)
    mathlib_objects = args.mathlib / '.lake/build/lib/lean'
    assert mathlib_objects.is_dir(), str(mathlib_objects)
    mathlib_commit = subprocess.run(['git', '-C', str(args.mathlib), 'rev-parse', 'HEAD'],
                                   text=True, capture_output=True, check=True).stdout.strip()
    assert re.fullmatch(r'[0-9a-f]{40}', mathlib_commit) and mathlib_commit.startswith('e4c91783'), mathlib_commit
    env = os.environ.copy()
    env['PATH'] = str(args.toolchain_bin) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in [objects, *package_roots, mathlib_objects])
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    frozen = {}
    for row in supplier['accepted'] + supplier['normal_only']:
        for key in ['source', 'object']:
            got = fp(stage / row[key]['archive_member'])
            assert same(got, row[key]), ('Frozen supplier mismatch', row['module'], key)
            frozen[got['path']] = got
    assert len(supplier['accepted']) == 278 and len(supplier['normal_only']) == 1
    expected = {r['module']: r for r in verifier['targets']}
    for module, item in expected.items():
        assert same(fp(project / (module.replace('.', '/') + '.lean')), item['source']), ('Source mismatch', module)
        audit = Path(__file__).parent / item['audit_relative_path']
        assert same(fp(audit), item['audit']), ('Audit source mismatch', module)
    records = []
    run_root = logs / args.attempt
    run_root.mkdir(parents=True, exist_ok=False)
    context = {'attempt': args.attempt, 'stage': str(stage), 'lean_version': version,
               'mathlib_commit': mathlib_commit, 'mathlib_commit_required_prefix': 'e4c91783',
               'required_mathlib_packages': required_packages,
               'mathlib_package_object_roots': [str(p) for p in package_roots],
               'optional_Cli_object_root_present': cli_objects.is_dir(),
               'driver': fp(Path(__file__)), 'verifier_manifest': fp(verifier_path),
               'supplier_manifest': fp(supplier_path), 'LEAN_PATH': env['LEAN_PATH'],
               'cwd': str(project), 'wall_limit_seconds': args.wall_seconds,
               'rss_limit_bytes': args.rss_gib * 1024**3, 'cloud_source_generation': False}
    dump_new(run_root / 'RUN.json', context)

    def accepted_step(module, mode, source, obj, audit_source):
        for path in sorted(logs.glob(f'*/{module.split(".")[-1]}/{mode}-result.json')):
            previous = read(path)
            if previous.get('status') != 'succeeded' or previous.get('exit_code') != 0:
                continue
            if not same(previous.get('source'), source) or not same(previous.get('object'), obj):
                continue
            if mode == 'owned' and not same(previous.get('audit_source'), audit_source):
                continue
            assert same(fp(previous['log']['path']), previous['log']), ('Prior log changed', str(path))
            return fp(path)
        return None

    def execute(module, mode):
        item = expected[module]
        source_path = project / (module.replace('.', '/') + '.lean')
        object_path = objects / (module.replace('.', '/') + '.olean')
        audit_path = Path(__file__).parent / item['audit_relative_path']
        source, audit_source = fp(source_path), fp(audit_path)
        assert same(source, item['source']) and same(audit_source, item['audit'])
        obj_before = fp(object_path) if object_path.exists() else None
        prior = accepted_step(module, mode, source, obj_before, audit_source)
        if prior is not None:
            records.append({'module': module, 'mode': mode, 'reused_successful_receipt': prior})
            print(json.dumps(records[-1]), flush=True)
            return
        folder = run_root / module.split('.')[-1]
        folder.mkdir(parents=True, exist_ok=True)
        object_path.parent.mkdir(parents=True, exist_ok=True)
        if mode == 'normal':
            assert not object_path.exists(), ('Refusing to overwrite an unreceipted object', str(object_path))
            argv = [str(lean), '-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0',
                    '-o', str(object_path), str(source_path.relative_to(project))]
        elif mode == 'kernel':
            assert object_path.exists(), ('Missing object', module)
            argv = [str(checker), '--verbose', module]
        else:
            assert mode == 'owned' and object_path.exists()
            argv = [str(lean), '-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0', str(audit_path)]
        command = {**context, 'module': module, 'mode': mode, 'argv': argv, 'source': source,
                   'object_before': obj_before, 'audit_source': audit_source if mode == 'owned' else None,
                   'started_unix': time.time()}
        dump_new(folder / (mode + '-command.json'), command)
        log = folder / (mode + '.log')
        started, peak, reason = time.monotonic(), 0, None
        print(json.dumps({'module': module, 'mode': mode, 'started': True}), flush=True)
        with log.open('x') as output:
            proc = subprocess.Popen(argv, cwd=project, env=env, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            while proc.poll() is None:
                rss = tree_rss(proc.pid)
                peak = max(peak, rss)
                if rss > args.rss_gib * 1024**3:
                    reason = 'rss_limit'
                elif time.monotonic() - started > args.wall_seconds:
                    reason = 'timeout'
                if reason:
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            rc = proc.wait()
        result = {**command, 'status': reason or ('succeeded' if rc == 0 else 'failed'), 'exit_code': rc,
                  'elapsed_seconds': time.monotonic() - started, 'peak_rss_bytes': peak,
                  'log': fp(log), 'object': fp(object_path) if object_path.exists() else None}
        try:
            assert same(fp(source_path), source), 'Source changed during verification'
            if mode != 'normal':
                assert same(result['object'], obj_before), 'Verified object changed'
            text = log.read_text()
            if rc == 0 and mode == 'normal':
                reported = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text) for a in group.split(',') if a.strip()}
                assert reported <= ALLOWED, ('Forbidden printed axiom', sorted(reported))
                assert result['object'] is not None, 'Successful compile without object'
                result['printed_axioms'] = sorted(reported)
            if rc == 0 and mode == 'owned':
                owned = parse_owned(text, module)
                owned_path = folder / 'owned-declarations.json'
                dump_new(owned_path, owned)
                result['owned_declarations'] = fp(owned_path)
                result['owned_declaration_count'] = owned['owned_declaration_count']
        except Exception as error:
            result['status'] = 'evidence_validation_failed'
            result['validation_error'] = repr(error)
        path = folder / (mode + '-result.json')
        dump_new(path, result)
        records.append({'module': module, 'mode': mode, 'receipt': fp(path), 'status': result['status']})
        print(json.dumps(records[-1]), flush=True)
        if result['status'] != 'succeeded':
            dump_new(run_root / 'STOPPED.json', {'failed_module': module, 'failed_mode': mode, 'records': records})
            raise SystemExit(1)

    row066 = verifier['targets'][0]['module']
    assert row066.endswith('Geometry01DirectDecodedRows066')
    execute(row066, 'kernel')
    execute(row066, 'owned')
    for item in verifier['targets'][1:]:
        for mode in ['normal', 'kernel', 'owned']:
            execute(item['module'], mode)
    for path, expected_fp in frozen.items():
        assert same(fp(path), expected_fp), ('Frozen source/object changed', path)
    dump_new(run_root / 'SUCCESS.json', {**context, 'status': 'succeeded', 'records': records,
                                        'accepted_targets': len(verifier['targets']), 'frozen_inputs_unchanged': True})
    print(json.dumps({'status': 'succeeded', 'run': str(run_root), 'accepted_targets': len(verifier['targets'])}), flush=True)


if __name__ == '__main__':
    main()
