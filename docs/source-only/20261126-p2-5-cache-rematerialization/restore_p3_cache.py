#!/usr/bin/env python3
"""Restore exact old bytes; optional normal-only rematerialization, never v7.

Default mode is read-only. All write modes require publication/runner/selection
bindings and a new receipt directory. Missing old evidence is never synthesized.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time

REL = 'docs/source-only/20261126-p2-5-cache-rematerialization/'
MAX_BLOB = 256 * 1024 * 1024
MAX_KEPT = 512 * 1024 * 1024
CONSUMER005_SHA = 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'
NORMAL_CANDIDATES = {'ImbalancedChen.' + name for name in [
    'P2OriginalSaving16DecoderChars', 'P2OriginalSaving16DecoderCompose',
    'P2OriginalSaving16FiniteCore', 'P2OriginalSaving16OriginalInput',
    'P2Saving16CanonicalCell00Binding', 'P2Saving16Cell00OriginalJson',
    'P2Saving16Cell00PayloadBinding', 'P2Saving16Cell00ScalarDecode',
    'P2Saving16Cell00StoredFloors', 'P2Saving16Cell00TypedPayload']}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def valid_sha(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value)


def load_exact(path, expected):
    require(valid_sha(expected) and digest(path) == expected, 'Pinned JSON hash differs: ' + str(path))
    return json.loads(Path(path).read_text())


def no_symlink_ancestors(path):
    require(path.is_absolute() and '..' not in path.parts, 'Absolute normalized path required')
    for parent in [path, *path.parents]:
        require(not parent.is_symlink(), 'Symlink destination/ancestor refused: ' + str(parent))


def install_link(source, target, expected):
    """Never overwrite; duplicate historical paths share immutable bytes."""
    source, target = Path(source), Path(target)
    no_symlink_ancestors(target)
    require(source.is_file() and not source.is_symlink() and digest(source) == expected,
            'Restoration source bytes differ: ' + str(source))
    if os.path.lexists(target):
        require(target.is_file() and digest(target) == expected,
                'Existing target conflicts; never overwrite: ' + str(target))
        return 'already_exact'
    target.parent.mkdir(parents=True, exist_ok=True)
    require(source.stat().st_dev == target.parent.stat().st_dev,
            'Cross-device hardlink refused: ' + str(target))
    os.link(source, target, follow_symlinks=False)
    require(digest(target) == expected and os.path.samefile(source, target), 'Installed link differs')
    return 'linked_exact_bytes'


class Resolver:
    def __init__(self, wanted):
        self.wanted = set(wanted)
        self.blobs = {}
        self.rejected = []
        self.kept = 0

    def file(self, path, expected, kind):
        if expected in self.blobs:
            return
        path = Path(path)
        if not path.is_file() or path.is_symlink():
            return
        actual = digest(path)
        if actual != expected:
            self.rejected.append({'path': str(path), 'expected': expected, 'actual': actual})
            return
        self.blobs[expected] = {'kind': kind, 'path': str(path), 'bytes': path.stat().st_size}

    def archive(self, path, members=None, expected_archive=None):
        """Read named regular members only; never use tar.extract/all."""
        path = Path(path)
        if not path.is_file():
            return
        if expected_archive is not None and digest(path) != expected_archive:
            self.rejected.append({'archive': str(path), 'error': 'archive_hash_mismatch'})
            return
        needed = self.wanted - self.blobs.keys()
        if not needed:
            return
        seen = set()
        with tarfile.open(path, 'r|*') as tf:
            for item in tf:
                # CAS uses whole SHA names; published mappings use exact names.
                expected = members.get(item.name) if members is not None else item.name
                if expected not in needed:
                    continue
                require(item.name not in seen, 'Duplicate selected archive member: ' + item.name)
                seen.add(item.name)
                if expected in self.blobs:
                    continue
                require(item.isfile() and not item.issym() and not item.islnk()
                        and item.size <= MAX_BLOB, 'Selected archive member is not a bounded regular file')
                stream = tf.extractfile(item)
                data = stream.read(MAX_BLOB + 1)
                require(len(data) == item.size, 'Incomplete archive member')
                actual = hashlib.sha256(data).hexdigest()
                if actual != expected:
                    self.rejected.append({'archive': str(path), 'member': item.name,
                                          'expected': expected, 'actual': actual})
                    continue
                require(self.kept + len(data) <= MAX_KEPT, 'Recovery selected-byte memory bound exceeded')
                self.kept += len(data)
                self.blobs[expected] = {'kind': 'archive_member', 'archive': str(path),
                    'archive_sha256': expected_archive, 'member': item.name,
                    'bytes': len(data), '_data': data}

    def store(self, expected, directory):
        target = directory / expected
        if target.exists():
            require(digest(target) == expected, 'Fresh content store differs')
            return target
        row = self.blobs[expected]
        directory.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            if '_data' in row:
                out.write(row['_data'])
            else:
                with Path(row['path']).open('rb') as src:
                    shutil.copyfileobj(src, out, 1024 * 1024)
        require(digest(target) == expected and target.stat().st_size == row['bytes'],
                'Content store copy differs')
        return target


def resolve(cfg, repo, args):
    requirements = {row['path']: row['sha256'] for row in cfg['requirements']}
    require(len(requirements) == len(cfg['requirements']) and all(valid_sha(h) for h in requirements.values()),
            'Duplicate paths or malformed expected hashes')
    allowed = Path(cfg['target_root'])
    runners = {p for p in requirements if Path(p).parent == Path('/workspace') and p.endswith('.py')}
    for p in requirements:
        path = Path(p)
        require(path.is_absolute() and '..' not in path.parts and
                (path.is_relative_to(allowed) or path.is_relative_to('/workspace/goldbach-research') or p in runners),
                'Unexpected destination outside frozen recovery scope: ' + p)
    r = Resolver(requirements.values())
    conflicts, existing = [], []
    for p, expected in requirements.items():
        path = Path(p)
        if os.path.lexists(path):
            if path.is_symlink() or not path.is_file() or digest(path) != expected:
                conflicts.append(p)
            else:
                existing.append(p)
                r.file(path, expected, 'existing_target')
    archive_groups = {}
    for h, candidates in cfg['sources_by_sha256'].items():
        for source in candidates:
            if source['kind'] == 'repo_file':
                r.file(repo / source['path'], h, 'repository_file')
            elif source['kind'] == 'remote_file':
                r.file(source['path'], h, 'verified_p3_inventory_file')
            elif source['kind'] == 'repo_archive':
                key = (str(repo / source['path']), source['archive_sha256'])
                archive_groups.setdefault(key, {})[source['member']] = h
            elif source['kind'] == 'remote_archive':
                archive_groups.setdefault((source['path'], None), {})[source['member']] = h
    for (archive, archive_sha), members in archive_groups.items():
        r.archive(archive, members, archive_sha)
    if args.payload_manifest:
        manifest = load_exact(args.payload_manifest, args.payload_manifest_sha)
        groups = {}
        for row in manifest['entries']:
            h = row['sha256']
            if h not in r.wanted:
                continue
            if row['kind'] == 'file':
                r.file(row['path'], h, 'external_payload_file')
            elif row['kind'] == 'archive_member':
                archive = args.payload_archive or row['archive']
                key = (archive, row['archive_sha256'])
                groups.setdefault(key, {})[row['member']] = h
            else:
                raise RuntimeError('Unsupported external payload kind')
        require(not args.payload_archive or len(groups) == 1,
                'Payload archive override requires exactly one selected archive')
        for (archive, archive_sha), members in groups.items():
            r.archive(archive, members, archive_sha)
    require(not args.payload_archive or args.payload_manifest, 'Payload archive needs a pinned payload manifest')
    if not args.skip_cas:
        for archive in cfg['cas_archives']:
            r.archive(archive)
    return requirements, r, conflicts, existing


def topological(objects, modules):
    wanted = set(modules)
    done, active, order = set(), set(), []
    def visit(module):
        require(module not in active, 'Cyclic frozen project graph')
        if module in done:
            return
        active.add(module)
        for dep in objects[module]['project_imports']:
            require(dep in objects, 'Unknown project dependency: ' + dep)
            visit(dep)
        active.remove(module)
        done.add(module)
        if module in wanted:
            order.append(module)
    for module in sorted(wanted):
        visit(module)
    return order


def runtime_check(cfg, consumer):
    missing, mismatched = [], []
    checks = {p: h for p, h in consumer['frozen_inputs'].items()
              if p.startswith(('/mathlib/', '/workspace/toolchains/'))}
    for p, h in checks.items():
        if not Path(p).is_file():
            missing.append(p)
        elif digest(p) != h:
            mismatched.append(p)
    mathlib = Path(cfg['runtime']['mathlib_path'])
    pin_ok = False
    if mathlib.is_dir():
        p = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=mathlib,
                           capture_output=True, text=True, timeout=30)
        pin_ok = p.returncode == 0 and p.stdout.strip() == cfg['runtime']['mathlib_commit']
    return {'required_path_count': len(checks), 'missing_count': len(missing),
        'mismatched_count': len(mismatched), 'first_missing': missing[:20],
        'first_mismatched': mismatched[:20], 'mathlib_pin_matches': pin_ok,
        'accepted': not missing and not mismatched and pin_ok}


def check_selection_contract(cfg, consumer, witness_manifest):
    require(cfg['consumer_receipt']['sha256'] == CONSUMER005_SHA,
            'Recovery must use the actual consumer005 receipt')
    decoded = 'ImbalancedChen.P2Saving16Cell00Decoded'
    require(consumer['accepted'] is False and consumer['modules'][decoded]['accepted'] is True,
            'Preserve the failed aggregate and accepted Decoded owner')
    objects = {m: row['sha256'] for m, row in consumer['dependency_objects'].items()}
    objects[decoded] = consumer['modules'][decoded]['object']['sha256']
    require(len(objects) == 41 and {m:r['sha256'] for m,r in cfg['objects'].items()} == objects,
            'Recovery object identities differ from the accepted 41')
    for m, row in cfg['objects'].items():
        old = consumer['source_graph'][m]
        require(row['source'] == old['path'] and row['source_sha256'] == old['source_sha256']
                and row['project_imports'] == old['project_imports'], 'Recovery source graph changed: '+m)
    require(set(cfg['allowed_normal_rebuild_modules']) <= NORMAL_CANDIDATES,
            'Normal scope exceeds the ten actually missing candidates')
    require(cfg['runtime']['strict_flags'] == consumer['strict_flags'] and
            cfg['runtime']['lean'] == consumer['runtime']['lean'] and
            cfg['runtime']['leanchecker'] == consumer['runtime']['leanchecker'] and
            cfg['runtime']['mathlib_commit'] == consumer['runtime']['mathlib_pin'],
            'Strict compiler/runtime identities changed')
    require(cfg['runtime']['LEAN_SYSROOT'] == str(Path(consumer['runtime']['lean']['path']).parent.parent),
            'Lean system root changed')
    require(cfg['witnesses'] == witness_manifest['snapshot']['files'], 'Witness snapshot mapping changed')
    expected = {p:h for p,h in consumer['frozen_inputs'].items()
                if not p.startswith(('/mathlib/', '/workspace/toolchains/'))}
    expected[cfg['target_root']+'/.lake/diagnostic/p25-cell00-five-consumers-attempt005/RESULT.json'] = CONSUMER005_SHA
    for key in ['runner','exception_log']:
        expected[consumer[key]['path']] = consumer[key]['sha256']
    for row in cfg['witnesses']:
        expected[row['realpath']] = row['sha256']
    for row in consumer['source_graph'].values():
        expected[cfg['target_root']+'/'+row['path']] = row['source_sha256']
    require({r['path']:r['sha256'] for r in cfg['requirements']} == expected
            and len(cfg['requirements']) == len(expected), 'Historical restoration requirement set changed')


def witness_snapshot(rows):
    actual = []
    for row in rows:
        path = Path(row['realpath'])
        before = path.stat()
        h = digest(path)
        after = path.stat()
        fields = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns)
        require(fields(before) == fields(after) and after.st_size == row['bytes'] and h == row['sha256'],
                'Original witness bytes/identity changed: ' + str(path))
        actual.append({'path':str(path),'realpath':str(path.resolve()),'bytes':after.st_size,
                       'sha256':h,'device':after.st_dev,'inode':after.st_ino,'mtime_ns':after.st_mtime_ns})
    return actual


def p3_inventory_complete(inventory):
    scope = inventory.get('scope', {})
    return (scope.get('p3_41_scan_completed') is True
            and type(scope.get('p3_scan_exit_code')) is int
            and scope['p3_scan_exit_code'] == 0
            and any(r.get('environment') == 'P3' and r.get('files_scanned', 0) > 0
                    for r in inventory['scan_scope_and_errors']))


def write_receipt(directory, state):
    temporary = directory / 'RECOVERY_RESULT.tmp'
    temporary.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(directory / 'RECOVERY_RESULT.json')


def verify_publication(repo, args):
    require(re.fullmatch(r'[0-9a-f]{40}', args.publication or ''), 'Write mode needs full publication commit')
    require(digest(__file__) == args.runner_sha, 'Runner SHA differs')
    def git(*items):
        return subprocess.check_output(['git', *items], cwd=repo, timeout=120)
    require(git('rev-parse', 'HEAD').decode().strip() == args.publication,
            'Checkout must already be the selected publication')
    require(not git('status', '--porcelain', '--untracked-files=no').strip(), 'Tracked checkout dirty')
    for relative, path in [(REL + 'restore_p3_cache.py', Path(__file__).resolve()),
                           (REL + 'RECOVERY_SELECTION.json', Path(args.selection).resolve())]:
        require(git('show', args.publication + ':' + relative) == path.read_bytes(),
                'Running code/selection is not exact publication bytes: ' + relative)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--plan', action='store_true', help='read-only, default')
    modes.add_argument('--restore', action='store_true', help='restore available bytes, no Lean')
    modes.add_argument('--normal-rebuild', action='store_true', help='restore then only reconstruct missing approved objects')
    parser.add_argument('--repository', default='/workspace/p25-q96-20261125')
    parser.add_argument('--selection', required=True)
    parser.add_argument('--selection-sha', required=True)
    parser.add_argument('--publication')
    parser.add_argument('--runner-sha')
    parser.add_argument('--result-dir')
    parser.add_argument('--payload-manifest')
    parser.add_argument('--payload-manifest-sha')
    parser.add_argument('--payload-archive')
    parser.add_argument('--skip-cas', action='store_true', help='read-only local planning only')
    args = parser.parse_args()
    writing = args.restore or args.normal_rebuild
    require(not (writing and args.skip_cas), 'CAS search cannot be skipped in write modes')
    cfg = load_exact(args.selection, args.selection_sha)
    require(cfg['schema'] == 'p25-cache-rematerialization-selection-v1', 'Unknown selection schema')
    repo = Path(args.repository).resolve()
    consumer = load_exact(repo / cfg['consumer_receipt']['path'], cfg['consumer_receipt']['sha256'])
    witnesses = load_exact(repo / cfg['witness_manifest']['path'], cfg['witness_manifest']['sha256'])
    inventory = load_exact(repo / cfg['object_inventory']['path'], cfg['object_inventory']['sha256'])
    p3_complete = p3_inventory_complete(inventory)
    require(cfg['p3_object_inventory_complete'] is p3_complete and
            set(cfg['allowed_normal_rebuild_modules']) == set(inventory['missing_modules']) and
            {m:r['historical_object_sha256'] for m,r in inventory['objects'].items()} ==
              {m:r['sha256'] for m,r in cfg['objects'].items()}, 'Final object inventory binding differs')
    check_selection_contract(cfg, consumer, witnesses)
    if writing:
        require(repo == Path(cfg['target_root']), 'Writes require the fixed P3 repository')
        verify_publication(repo, args)
    print('P25_RECOVERY_RESOLVE_START', file=sys.stderr, flush=True)
    requirements, resolver, conflicts, existing = resolve(cfg, repo, args)
    missing_hashes = set(requirements.values()) - resolver.blobs.keys()
    object_shas = {r['sha256']: m for m, r in cfg['objects'].items()}
    missing_objects = sorted(object_shas[h] for h in missing_hashes if h in object_shas)
    missing_history = [{'sha256': h, 'paths': [p for p, expected in requirements.items() if expected == h]}
                       for h in sorted(missing_hashes) if h not in object_shas]
    allowed_missing = set(missing_objects) <= set(cfg['allowed_normal_rebuild_modules'])
    print('P25_RECOVERY_RUNTIME_READONLY_START', file=sys.stderr, flush=True)
    runtime = runtime_check(cfg, consumer)
    forbidden = [p for p in cfg['forbidden_v7_target_objects'] if os.path.lexists(p)]
    if os.path.lexists(cfg['future_v7_output']):
        forbidden.append(cfg['future_v7_output'])
    plan = {'schema': 'p25-cache-rematerialization-plan-v1', 'observed_utc': now(),
        'repository_read':str(repo), 'target_paths_evaluated_in_current_process':cfg['target_root'],
        'remote_execution_implied':False,
        'requirements': len(requirements), 'unique_required_hashes': len(set(requirements.values())),
        'exact_existing_paths': len(existing), 'exact_available_unique_hashes': len(resolver.blobs),
        'existing_conflicting_paths': conflicts, 'missing_object_modules': missing_objects,
        'missing_objects_are_within_approved_ten': allowed_missing,
        'p3_object_inventory_complete': p3_complete,
        'object_inventory_sha256':cfg['object_inventory']['sha256'],
        'missing_nonobject_payload_mappings': missing_history,
        'rejected_source_candidates': resolver.rejected, 'runtime': runtime,
        'future_v7_forbidden_existing_paths': forbidden,
        'external_payload': {'manifest':args.payload_manifest,
            'manifest_sha256':args.payload_manifest_sha,'archive_path_override':args.payload_archive},
        'normal_rebuild_order': topological(cfg['objects'], missing_objects),
        'source_locations': {h: {k: v for k, v in r.items() if k != '_data'}
                             for h, r in resolver.blobs.items()},
        'lean_executions': [], 'new_formal_credit': False, 'P2_5_proved': False}
    if not writing:
        print(json.dumps(plan, ensure_ascii=False, indent=2))
        return 2 if conflicts or missing_history or missing_objects or not runtime['accepted'] or forbidden else 0
    require(not conflicts, 'Existing targets conflict; nothing was written')
    require(runtime['accepted'], 'Runtime/external context differs; nothing was written')
    require(not forbidden, 'Preserve existing unaccepted/future-v7 attempt; nothing was written')
    if args.normal_rebuild:
        require(p3_complete, 'P3 final 41-object inventory is still pending; do not recompile')
        require(allowed_missing, 'Do not recompile an object known available in the 31-object payload')
        require(not missing_history, 'Historical/witness byte mappings incomplete; do not start Lean')
    require(args.result_dir is not None, 'Write modes need a fresh result directory')
    result = Path(args.result_dir)
    require(result.is_absolute() and result.parent == repo / '.lake/diagnostic'
            and result.name.startswith('p25-cache-rematerialization-attempt')
            and not os.path.lexists(result), 'Invalid or preexisting recovery result directory')
    no_symlink_ancestors(result)
    write_hashes = {h for p, h in requirements.items() if p not in existing and h in resolver.blobs}
    budget = sum(resolver.blobs[h]['bytes'] for h in write_hashes) + cfg['initial_free_reserve_bytes']
    free = shutil.disk_usage(repo).free
    require(free >= budget, 'Insufficient free bytes for unique payload plus preserved reserve')
    result.mkdir(parents=True)
    state = {'schema': 'p25-cache-rematerialization-result-v1', 'status': 'RESTORING',
        'started_utc': now(), 'publication_commit': args.publication,
        'runner_sha256': args.runner_sha, 'selection_sha256': args.selection_sha,
        'plan': plan, 'restored_paths': [], 'normal_stages': [],
        'replay_stages': [], 'owned_audit_stages': [],
        'old_receipts_changed': False, 'new_formal_credit': False, 'P2_5_proved': False,
        'disk_before': {'free': free, 'required': budget}}
    write_receipt(result, state)
    try:
        store = result / 'bytes'
        for p, h in requirements.items():
            if h not in resolver.blobs or p in existing:
                continue
            action = install_link(resolver.store(h, store), Path(p), h)
            state['restored_paths'].append({'path': p, 'sha256': h, 'action': action})
        write_receipt(result, state)
        if args.normal_rebuild:
            lib, src = result / 'lib', result / 'src'
            for m, row in cfg['objects'].items():
                if row['sha256'] in resolver.blobs:
                    install_link(resolver.store(row['sha256'], store),
                                 lib / (m.replace('.', '/') + '.olean'), row['sha256'])
            env = dict(os.environ)
            env.pop('LEAN_SRC_PATH', None)
            env['LEAN_SYSROOT'] = cfg['runtime']['LEAN_SYSROOT']
            env['LEAN_PATH'] = str(lib) + ':' + ':'.join(consumer['approved_LEAN_PATH'].split(':')[1:])
            env['PATH'] = str(Path(cfg['runtime']['lean']['path']).parent) + os.pathsep + env.get('PATH', '')
            for m in plan['normal_rebuild_order']:
                row = cfg['objects'][m]
                for dep in row['project_imports']:
                    dep_obj = lib / (dep.replace('.', '/') + '.olean')
                    require(dep_obj.is_file() and digest(dep_obj) == cfg['objects'][dep]['sha256'],
                            'Normal prerequisite not exact: ' + dep)
                inputs_before = witness_snapshot(cfg['witnesses'])
                require(shutil.disk_usage(repo).free >= cfg['per_stage_free_reserve_bytes'],
                        'Stage free-space reserve not met')
                source = src / (m.replace('.', '/') + '.lean')
                install_link(resolver.store(row['source_sha256'], store), source, row['source_sha256'])
                obj = lib / (m.replace('.', '/') + '.olean')
                require(not os.path.lexists(obj), 'Refuse a preexisting normal target')
                obj.parent.mkdir(parents=True, exist_ok=True)
                log = result / (m.split('.')[-1] + '-NORMAL.log')
                cmd = [cfg['runtime']['lean']['path'], *cfg['runtime']['strict_flags'],
                       '--root=' + str(src), '-o', str(obj), str(source)]
                stage = {'module': m, 'command': cmd, 'cwd': str(repo), 'LEAN_PATH': env['LEAN_PATH'],
                         'started_utc': now(), 'status': 'RUNNING', 'log': str(log),
                         'input_snapshot_before':inputs_before}
                state['normal_stages'].append(stage)
                write_receipt(result, state)
                started = time.monotonic()
                print('P25_REMATERIALIZE_NORMAL_START', m, flush=True)
                with log.open('xb') as stream:
                    process = subprocess.Popen(cmd, cwd=repo, env=env, stdout=stream,
                        stderr=subprocess.STDOUT, start_new_session=True)
                    timed_out = False
                    try:
                        code = process.wait(timeout=cfg['normal_stage_wall_seconds'])
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait(timeout=30)
                        code = 124
                stage.update(exit_code=code, timed_out=timed_out, seconds=round(time.monotonic()-started,3),
                    ended_utc=now(), log_sha256=digest(log), log_bytes=log.stat().st_size,
                    status='PASSED' if code == 0 else 'FAILED')
                write_receipt(result, state)
                require(code == 0 and not timed_out, 'Normal rematerialization failed: ' + m)
                stage['input_snapshot_after'] = witness_snapshot(cfg['witnesses'])
                require(stage['input_snapshot_after'] == inputs_before,
                        'Original witness identity changed during normal stage')
                actual = digest(obj)
                stage.update(object_sha256=actual, expected_object_sha256=row['sha256'],
                             exact_historical_object_match=actual == row['sha256'])
                write_receipt(result, state)
                require(actual == row['sha256'], 'New object SHA differs; stop without filling old object paths: ' + m)
                require(not any(Path(str(obj)+s).exists() for s in ['.private','.server']),
                        'Unexpected new project object companions')
                resolver.file(obj, row['sha256'], 'new_normal_exact_historical_match')
                for p, h in requirements.items():
                    if h == row['sha256']:
                        action = install_link(obj, Path(p), h)
                        state['restored_paths'].append({'path':p,'sha256':h,'action':action})
                write_receipt(result, state)
        unresolved = []
        for p, h in requirements.items():
            if not Path(p).is_file():
                unresolved.append({'path':p,'sha256':h})
            else:
                require(digest(p) == h, 'Historical bytes changed during recovery: ' + p)
        runtime_after = runtime_check(cfg, consumer)
        require(runtime_after['accepted'], 'Runtime/external bytes changed during recovery')
        verify_publication(repo, args)
        state.update(status='EXACT_BYTES_RESTORED' if not unresolved else 'PARTIAL_RESTORE_ONLY',
            ended_utc=now(), unresolved_paths=unresolved, runtime_after=runtime_after,
            ready_for_original_v7_preflight=not unresolved,
            original_v7_executed=False, original_v7_preflight_claimed_passed=False)
        write_receipt(result, state)
        print(json.dumps({'status':state['status'],'receipt':str(result/'RECOVERY_RESULT.json'),
                          'normal_count':len(state['normal_stages']),'unresolved_paths':len(unresolved)}))
        return 0 if not unresolved else 2
    except Exception as exc:
        state.update(status='FAILED', ended_utc=now(), error=type(exc).__name__+': '+str(exc))
        write_receipt(result, state)
        raise


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        print(type(error).__name__ + ': ' + str(error), file=sys.stderr)
        raise SystemExit(1)
