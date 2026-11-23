#!/usr/bin/env python3
"""Use only the new90 qualified T01 family; copy and stock are separate phases."""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
BASE = Path('/workspace/artifacts/member-t01-project90-20261123')
STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
OPEN = Path('/workspace/blue-member-aggregate-evidence/REUSE_WINDOW_OPEN.json')
RELEASED = Path('/workspace/blue-member-aggregate-evidence/STOCK_RELEASED.json')


def read(p):
    return json.loads(p.read_text())


def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def stamp(p):
    s = p.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def write_new(p, value):
    with p.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def active_paths():
    paths = set()
    for p in Path('/proc').glob('[0-9]*/cmdline'):
        try:
            args = [x.decode(errors='replace') for x in p.read_bytes().split(b'\0') if x]
            if not args:
                continue
            names = {'lean', 'lean-runtime', 'leanir', 'clang', 'lean-wrapper.py', 'clang-wrapper.py', 'leanir-wrapper.py'}
            exe = Path(args[0]).name
            wrapper = exe.startswith('python') and len(args) > 1 and Path(args[1]).name in names
            if exe not in names and not wrapper:
                continue
            paths.update(str(Path(a).resolve()) for a in args if a.startswith('/') and a.endswith(('.lean', '.c', '.ir')))
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            pass
    return paths


class Audit:
    def __init__(self, rows):
        self.by_path = {r['path']: r for r in rows}
        self.by_stamp = {}
        for r in rows:
            key = tuple(r['stat_identity'])
            if key in self.by_stamp:
                assert self.by_stamp[key]['sha256'] == r['sha256'], 'Conflicting same-physical-file audit'
            self.by_stamp[key] = r
        self.used = {}
        self.counts = collections.Counter()

    def check(self, p, expected, size=None):
        before = stamp(p)
        if size is not None:
            assert before[2] == size, 'Size mismatch: ' + str(p)
        old = self.by_stamp.get(tuple(before))
        if old is not None:
            got = old['sha256']
            method = 'AUTHENTICATED_SHA_SAME_DEVICE_INODE_SIZE_MTIME_CTIME'
        else:
            got = sha(p)
            method = 'FRESH_CHANGED_OR_NEW90_UNSEEN_PHYSICAL_FILE'
        assert stamp(p) == before, 'Changed during read: ' + str(p)
        assert got == expected, 'SHA256 mismatch: ' + str(p)
        row = {'path': str(p), 'sha256': got, 'stat_identity': before, 'method': method}
        self.used[str(p)] = row
        self.by_stamp[tuple(before)] = row
        self.counts[method] += 1
        return before


def atomic_missing(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp = tempfile.mkstemp(prefix='.member-t01-reuse-', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(raw)
            f.flush()
            os.fsync(f.fileno())
        os.link(temp, path, follow_symlinks=False)
    finally:
        Path(temp).unlink(missing_ok=True)


def copy_phase(args, d, helper_sha):
    assert OPEN.is_file(), 'Owner reuse window is not open'
    assert not RELEASED.exists(), 'Copy gate has already been released'
    args.out.mkdir(parents=True, exist_ok=False)
    input_audit = Path(d['physical_audit']['path'])
    assert sha(input_audit) == d['physical_audit']['sha256']
    audit = Audit(read(input_audit))
    config = tomllib.loads((PROJECT / 'lakefile.toml').read_text())
    assert config['name'] == 'imbalancedChen' and config['moreLeanArgs'] == ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000']
    assert not config.get('leanOptions') and not config.get('weakLeanArgs')
    assert all(not r.get('leanOptions') and not r.get('moreLeanArgs') and not r.get('weakLeanArgs') for r in config.get('lean_lib', []))
    runtime_rows = d['runtime_binary_checks'] + [r for r in d['abi_checks'] if r['kind'] == 'pinned-toolchain-shared-library-ABI']
    for r in runtime_rows:
        audit.check(Path(r['local']), r['expected'])
    assert d['runtime_policy_matches']
    # The independent12GiB guard is immutable during this reuse window.
    old_guard = read(Path('/workspace/artifacts/cdc-generated-c-completion-20261123-v3-p6-member/CORRECTION_RECEIPT.json'))
    assert sha(STATE) == old_guard['protected_originals'][str(STATE)]['sha256'], 'Member guard state changed'
    parts = d['import_parts']
    groups = d['modules']
    eligible = {n for n, r in groups.items() if not r['reasons']}
    assert all(set(groups[n]['checkpoint_dependencies']) <= eligible for n in eligible), 'Qualified provider closure is not closed'
    accepted, skipped = [], {}
    remaining = set(eligible)
    while remaining:
        ready = sorted(n for n in remaining if not (set(groups[n]['checkpoint_dependencies']) & remaining))
        assert ready, 'Provider cycle'
        for name in ready:
            remaining.remove(name)
            r = groups[name]
            if set(r['checkpoint_dependencies']) & set(skipped):
                skipped[name] = 'Skipped checkpoint provider'; continue
            source = PROJECT / r['source']['install_path']
            try:
                assert str(source.resolve()) not in active_paths(), 'Queued/running source'
                source_stamp = audit.check(source, r['source']['sha256'], r['source'].get('bytes', r['source'].get('identity', {}).get('bytes')))
                watched = [(source, source_stamp)]
                imported_modules = set()
                for index in r['import_part_indices']:
                    part = parts[index]
                    imported_modules.add(part['module'])
                    p = Path(part['local'])
                    watched.append((p, audit.check(p, part['sha256'], part['bytes'])))
                for imported in imported_modules:
                    s = d['import_source_checks'][imported]
                    assert s['status'] == 'MATCH'
                    p = Path(s['local'])
                    watched.append((p, audit.check(p, s['expected'])))
                payloads = []
                for f in r['facets']:
                    rel = Path(f['install_path'])
                    assert not rel.is_absolute() and '..' not in rel.parts and rel.parts[:2] == ('.lake', 'build')
                    dest = PROJECT / rel
                    assert dest.resolve().is_relative_to((PROJECT / '.lake/build').resolve())
                    stage = BASE / 'qualification-v1/candidate-tree' / rel
                    audit.check(stage, f['sha256'], f['bytes'])
                    if dest.exists():
                        audit.check(dest, f['sha256'], f['bytes'])
                    payloads.append((dest, stage, f))
                assert all(stamp(p) == s for p, s in watched), 'Inputs changed before use'
                assert str(source.resolve()) not in active_paths(), 'Source became active'
                # Publish readable artifacts first, each sidecar after its body,
                # and the authentic original trace last. No existing file is replaced.
                def order(x):
                    text = str(x[0]); base = text.removesuffix('.hash')
                    rank = 100 if base.endswith('.trace') else 80 if base.endswith('.olean') else 60
                    return rank + int(text.endswith('.hash')), text
                installed = []
                for dest, stage, f in sorted(payloads, key=order):
                    assert OPEN.is_file() and not RELEASED.exists(), 'Owner copy gate changed'
                    assert str(source.resolve()) not in active_paths(), 'Source became active during copy'
                    assert stamp(source) == source_stamp, 'Source changed during copy'
                    if dest.exists():
                        audit.check(dest, f['sha256'], f['bytes'])
                        continue
                    event = {'module': name, 'path': str(dest), 'sha256': f['sha256'], 'bytes': f['bytes'], 'phase': 'INTENT'}
                    with (args.out / 'RESTORE_JOURNAL.jsonl').open('a') as journal:
                        journal.write(json.dumps(event) + '\n'); journal.flush(); os.fsync(journal.fileno())
                    try:
                        raw = stage.read_bytes()
                        assert len(raw) == f['bytes'] and hashlib.sha256(raw).hexdigest() == f['sha256'], 'Staged payload changed before use'
                        atomic_missing(dest, raw)
                    except FileExistsError:
                        audit.check(dest, f['sha256'], f['bytes'])
                        continue
                    audit.check(dest, f['sha256'], f['bytes'])
                    installed.append(dict(f, path=str(dest)))
                    event['phase'] = 'INSTALLED_AUTHENTIC_MISSING_FACET'
                    with (args.out / 'RESTORE_JOURNAL.jsonl').open('a') as journal:
                        journal.write(json.dumps(event) + '\n'); journal.flush(); os.fsync(journal.fileno())
                assert all(stamp(p) == s for p, s in watched), 'Inputs changed during copy'
                accepted.append({'module': name, 'source_sha256': r['source']['sha256'],
                                 'original_actual_import_map_sha256': r['actual_import_map_sha256_verified'],
                                 'installed_facets': installed})
            except (AssertionError, FileNotFoundError, KeyError) as e:
                skipped[name] = str(e)
    assert sha(Path(__file__)) == helper_sha, 'Installer source changed during execution'
    write_new(args.out / 'COPY_INPUT_AUDIT.json', list(audit.used.values()))
    value = {'schema': 'new90-authentic-module-copy-v1', 'helper_sha256': helper_sha,
             'manifest': str(args.manifest), 'manifest_sha256': args.manifest_sha256,
             'owner_window_marker': str(OPEN), 'owner_window_marker_sha256': sha(OPEN),
             'accepted_groups': accepted, 'skipped_during_use': skipped,
             'blocked_by_original_qualification': {n: r['reasons'] for n, r in groups.items() if r['reasons']},
             'copied_group_count': sum(bool(r['installed_facets']) for r in accepted),
             'copied_facet_count': sum(len(r['installed_facets']) for r in accepted),
             'identity_methods': dict(audit.counts), 'source_files_written': False,
             'existing_files_overwritten': False, 'original_hashes_or_traces_rebased': False,
             'Lean_Lake_or_compiler_invoked_during_copy': False,
             'member_guard_state_sha256': sha(STATE),
             'stock_required_after_owner_releases_external_compiler_gate': str(RELEASED)}
    write_new(args.out / 'COPY_COMPLETE.json', value)
    print(json.dumps({k: value[k] for k in ['copied_group_count', 'copied_facet_count', 'skipped_during_use']}))


def stock_phase(args, d, helper_sha):
    assert RELEASED.is_file(), 'Owner has not released its external compiler gate'
    copy = read(args.out / 'COPY_COMPLETE.json')
    assert copy['manifest_sha256'] == args.manifest_sha256 and copy['helper_sha256'] == helper_sha
    assert sha(STATE) == copy['member_guard_state_sha256'], 'Member guard changed before stock'
    names = [r['module'] for r in copy['accepted_groups']]
    state = read(STATE)
    log = Path(state['log'])
    start = log.stat().st_size
    command = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', str(STATE),
               'lake', '--no-build', 'build'] + ['+' + n + ':leanArts' for n in names]
    if names:
        with (args.out / 'stock.stdout').open('xb') as stdout, (args.out / 'stock.stderr').open('xb') as stderr:
            result = subprocess.run(command, cwd=PROJECT, stdout=stdout, stderr=stderr)
        exit_code = result.returncode
    else:
        exit_code = None
    with log.open('rb') as f:
        f.seek(start)
        events = [json.loads(line) for line in f.read().splitlines() if line]
    member = [e for e in events if e.get('cwd') == str(PROJECT)]
    metadata = [e for e in member if e['tool'] == 'lean' and e['input_args'] in [['--githash'], ['--print-prefix']]]
    source = [e for e in member if e not in metadata]
    # Stock replay must preserve the exact authenticated originals just copied.
    own_audit = Audit(read(args.out / 'COPY_INPUT_AUDIT.json'))
    unchanged, contradictions = True, []
    for name in names:
        r = d['modules'][name]
        try:
            own_audit.check(PROJECT / r['source']['install_path'], r['source']['sha256'])
            for f in r['facets']:
                own_audit.check(PROJECT / f['install_path'], f['sha256'], f['bytes'])
        except (AssertionError, FileNotFoundError) as e:
            unchanged = False
            contradictions.append({'module': name, 'reason': str(e)})
    assert sha(Path(__file__)) == helper_sha
    value = {'schema': 'new90-actual-stock-no-build-result-v1', 'helper_sha256': helper_sha,
             'command': command, 'cwd': str(PROJECT), 'exit_code': exit_code, 'modules': names,
             'member_fresh_source_or_native_compiler_events': source,
             'member_fresh_source_or_native_compiler_event_count': len(source),
             'member_metadata_events': metadata, 'other_project_concurrent_guard_events': [e for e in events if e not in member],
             'compiler_log_start_byte': start, 'compiler_log_end_byte': log.stat().st_size,
             'original_source_and_restored_artifacts_unchanged_after_stock': unchanged,
             'post_stock_contradictions': contradictions,
             'stock_pass_with_zero_Member_source_calls': exit_code == 0 and not source and unchanged,
             'source_compilation_or_kernel_acceptance_claimed': False}
    write_new(args.out / 'STOCK_RESULT.json', value)
    print(json.dumps({k: value[k] for k in ['exit_code', 'member_fresh_source_or_native_compiler_event_count', 'stock_pass_with_zero_Member_source_calls']}))
    raise SystemExit(0 if value['stock_pass_with_zero_Member_source_calls'] else 1)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--phase', choices=['copy', 'stock'], required=True)
    p.add_argument('--manifest', type=Path, default=BASE / 'COMPACT_MANIFEST.json')
    p.add_argument('--manifest-sha256', required=True)
    p.add_argument('--out', type=Path, default=BASE / 'install-v1')
    a = p.parse_args()
    helper_sha = sha(Path(__file__))
    assert sha(a.manifest) == a.manifest_sha256
    d = read(a.manifest)
    assert d['scope_new_project_candidates'] == 90 and d['target_project'] == str(PROJECT)
    if a.phase == 'copy':
        copy_phase(a, d, helper_sha)
    else:
        stock_phase(a, d, helper_sha)


if __name__ == '__main__':
    main()
