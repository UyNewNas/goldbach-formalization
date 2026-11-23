"""Owner-only no-clobber adoption of two previously qualified authentic groups.

No default execution: an explicit immutable owner quiescence receipt is required.
The original qualification files and all original producer bytes stay unchanged.
"""
from pathlib import Path
from controlled_window_gate_candidate import controlled_owner_window
import argparse, datetime, fcntl, hashlib, json, os, subprocess, tempfile, time

BASE = Path('/workspace/p1-complete-proof/prototype-two-proposed-post-object-qualification')
MEMBER = Path('/workspace/blue-member-build')
MAIN = Path('/workspace/goldbach-formalization')
STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
ORDER = ['ImbalancedChen.P5RealTruncatedMobiusSupport', 'ImbalancedChen.P5RealCutoffHeathBrownThree']

def sha(p):
    with Path(p).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def dump(p, obj):
    Path(p).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def identity(p):
    p = Path(p).resolve(strict=True)
    s = p.stat()
    return {'resolved': str(p), 'bytes': s.st_size, 'dev': s.st_dev, 'ino': s.st_ino,
            'mtime_ns': s.st_mtime_ns, 'ctime_ns': s.st_ctime_ns}

def compiler_processes():
    result = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            argv = [a for a in (p / 'cmdline').read_text().split('\0') if a]
        except (OSError, UnicodeError):
            continue
        if not argv:
            continue
        is_runtime = Path(argv[0]).name == 'lean-runtime'
        is_wrapper = len(argv) > 1 and argv[1].endswith('/p0-ci-shadow-toolchain/bin/lean')
        if is_runtime or is_wrapper:
            result.append({'pid': int(p.name), 'argv': argv})
    return result

def assert_no_target_writers():
    targets = {str(MEMBER / (m.replace('.', '/') + '.lean')) for m in ORDER}
    targets |= {str(Path('/workspace/blue-reindex-build') / (m.replace('.', '/') + '.lean')) for m in ORDER}
    found = [p for p in compiler_processes() if targets.intersection(p['argv'])]
    assert not found, ('active_or_waiting_target_writer', found)

def atomic_bytes(dst, data, no_clobber):
    dst = Path(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix='.qualified-p1-', dir=dst.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        if no_clobber:
            os.link(tmp, dst, follow_symlinks=False)
        else:
            os.replace(tmp, dst)
    finally:
        Path(tmp).unlink(missing_ok=True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--owner-window', required=True)
    ap.add_argument('--root-review', required=True)
    ap.add_argument('--evidence', required=True)
    ap.add_argument('--apply', action='store_true')
    args = ap.parse_args()
    assert args.apply, 'explicit --apply required; this script never starts by default'
    out = Path(args.evidence)
    out.mkdir(exist_ok=False)
    w = Path(args.owner_window)
    root_review = Path(args.root_review)
    with controlled_owner_window(root_review, w, caller_path=Path(__file__)) as controlled:
        manifest_path = BASE / 'MANIFEST.json'
        assert sha(manifest_path) == '373e844976c6509847657f78552b97aea06c74dee6b9869f22eb797d602a61e7'
        manifest = json.loads(manifest_path.read_text())
        # Authenticate the smaller metadata ledgers through the already pinned
        # immutable manifest before using their inherited physical digests.
        for name, expected_digest in manifest['additional_files'].items():
            assert Path(name).name == name, ('nonlocal_metadata_name', name)
            entry = BASE / name
            assert sha(entry) == expected_digest, ('qualification_metadata_changed', str(entry))
        state = json.loads(STATE.read_text())
        assert sha(STATE) == manifest['runtime_state']['sha256']
        physical = {x['resolved']: x for x in json.loads((BASE / 'PHYSICAL_IDENTITIES.json').read_text())['files']}
        checks = json.loads((BASE / 'IMPORT_PART_CHECKS.json').read_text())['checks']
        source_keys = {g['actual_current_source_identity_key'] for g in manifest['groups'].values()}
        verified = {}

        def verify(path, expected=None):
            path = Path(path)
            key = str(path.resolve(strict=True))
            old = physical[key]
            cur = identity(path)
            unchanged = all(cur[k] == old[k] for k in ['resolved', 'bytes', 'dev', 'ino', 'mtime_ns', 'ctime_ns'])
            digest = old['sha256'] if unchanged else sha(path)
            assert digest == (expected or old['sha256']), ('qualified_input_changed', str(path))
            verified[str(path)] = dict(cur, sha256=digest,
                method='REUSED_PRIOR_SHA_SAME_COMPLETE_PHYSICAL_IDENTITY' if unchanged else 'FRESH_SHA_AFTER_IDENTITY_CHANGE')
            return digest

        for key in physical:
            if key not in source_keys:
                verify(key)
        for pair in checks.values():
            expected = verify(pair['producer_path'])
            dst = Path(pair['prospective_Member_path'])
            if dst.exists():
                assert verify(dst) == expected, ('actual_import_part_mismatch', str(dst))
            else:
                assert pair['provider'] != 'EXISTING_SHARED_PHYSICAL_IMPORT', ('missing_import', str(dst))
        sources = []
        for mod in ORDER:
            g = manifest['groups'][mod]
            src = Path(g['proposed_source_identity_key'])
            dst = Path(g['actual_current_source_identity_key'])
            assert sha(src) == g['proposed_source_post_sha256']
            assert sha(dst) == g['actual_current_source_pre_sha256']
            for facet in g['facets']:
                d = Path(facet['destination_path'])
                expected = physical[facet['identity_key']]['sha256']
                assert not d.exists() or sha(d) == expected, ('no_clobber_conflict', str(d))
            sources.append((mod, g, src, dst))
        dump(out / 'PREFLIGHT.json', {'utc': now(), 'owner_window': str(w), 'owner_window_sha256': sha(w),
            'manifest_sha256': sha(manifest_path), 'physical_input_checks': verified,
            'all_groups_preflight_before_any_source_or_object_mutation': True})
        copied, source_adoptions = [], []
        with controlled.compiler_mutation_window():
            controlled.assert_before_each_write()
            for path, snap in verified.items():
                assert identity(path) == {k: snap[k] for k in ['resolved', 'bytes', 'dev', 'ino', 'mtime_ns', 'ctime_ns']}
            for mod, g, src, dst in sources:
                assert sha(dst) == g['actual_current_source_pre_sha256']
                backup = out / (mod.split('.')[-1] + '.source-before.lean')
                backup.write_bytes(dst.read_bytes())
                main_src = MAIN / (mod.replace('.', '/') + '.lean')
                main_sync = main_src.exists() and sha(main_src) == g['actual_current_source_pre_sha256']
                controlled.assert_before_each_write()
                atomic_bytes(dst, src.read_bytes(), False)
                if main_sync:
                    controlled.assert_before_each_write()
                    atomic_bytes(main_src, src.read_bytes(), False)
                source_adoptions.append({'module': mod, 'pre_sha256': g['actual_current_source_pre_sha256'],
                    'post_sha256': g['proposed_source_post_sha256'], 'exact_producer_source_bytes': True,
                    'main_synced_identical_preimage_only': main_sync, 'baseline_backup': str(backup)})
                for facet in sorted(g['facets'], key=lambda f: f['relative_path'].endswith('.trace')):
                    dest = Path(facet['destination_path'])
                    payload = Path(facet['producer_path']).read_bytes()
                    expected = physical[facet['identity_key']]['sha256']
                    assert hashlib.sha256(payload).hexdigest() == expected
                    action = 'PRESERVED_IDENTICAL'
                    if not dest.exists():
                        controlled.assert_before_each_write()
                        atomic_bytes(dest, payload, True)
                        action = 'COPIED_NO_CLOBBER_AUTHENTIC_BYTES'
                    assert sha(dest) == expected
                    copied.append(dict(facet, action=action, sha256=expected))
            for pair in checks.values():
                dst = Path(pair['prospective_Member_path'])
                # Shared imports retain the already authenticated physical identity;
                # only the newly installed prospective project import needs hashing.
                key = str(dst.resolve(strict=True))
                expected = physical[pair['producer_identity_key']]['sha256']
                if key in physical:
                    assert verify(dst) == expected
                else:
                    assert sha(dst) == expected, ('installed_prospective_import_mismatch', str(dst))
            dump(out / 'COPY_COMPLETE.json', {'utc': now(), 'source_adoptions': source_adoptions,
                'facets': copied, 'trace_fields_or_expected_hashes_edited': False, 'source_tests_run': 0})
        controlled.assert_stock_phase_ready()
        # Compiler locks released; BOTH validation lanes and aggregate lease remain held through stock.
        log_paths = {json.loads(Path(p).read_text())['log'] for p in [STATE, Path('/workspace/blue-build-tools/runtime-evidence/state.json')]}
        positions = {p: Path(p).stat().st_size for p in log_paths}
        argv = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', str(STATE),
                'lake', '--no-build', 'build'] + ['+' + m + ':leanArts' for m in ORDER]
        started = now()
        t0 = time.monotonic()
        with (out / 'stock.log').open('x') as f:
            result = subprocess.run(argv, cwd=MEMBER, stdout=f, stderr=subprocess.STDOUT)
        events = []
        for path, offset in positions.items():
            with Path(path).open('rb') as f:
                f.seek(offset)
                for line in f:
                    e = json.loads(line)
                    if e.get('tool') == 'lean' and e.get('cwd') == str(MEMBER) and any(a.endswith('.lean') for a in e.get('command', [])):
                        events.append(e)
        stable = all(sha(x['destination_path']) == x['sha256'] for x in copied)
        stable &= all(sha(MEMBER / (x['module'].replace('.', '/') + '.lean')) == x['post_sha256'] for x in source_adoptions)
        receipt = {'window_policy': 'ROOT_REVIEWED_CONTROLLED_CHECKPOINT_CURRENT_QUIESCENT_WINDOW',
            'historical_aggregate_exit': 241, 'historical_completion_was_natural': False,
            'root_review_sha256': sha(root_review), 'owner_window_sha256': sha(w),
            'candidate_gate_sha256': sha(Path(__file__).with_name('controlled_window_gate_candidate.py')),
            'candidate_caller_sha256': sha(__file__),
            'argv': argv, 'started_utc': started, 'finished_utc': now(), 'elapsed_seconds': time.monotonic()-t0,
            'exit_code': result.returncode, 'Member_fresh_source_events_both_original_guard_logs': events,
            'source_and_all_installed_facets_unchanged': stable, 'stock_log_sha256': sha(out / 'stock.log'),
            'prior_normal_kernel_public_evidence_reused_not_reexecuted': True}
        dump(out / 'STOCK_RESULT.json', receipt)
        assert result.returncode == 0 and not events and stable, receipt
        print(json.dumps({'status': 'PASS_AUTHENTIC_PORTABLE_REUSE_STOCK_ZERO_MEMBER_SOURCE_CALLS',
                          'evidence': str(out), 'new_facets': sum(x['action'].startswith('COPIED') for x in copied)}))

if __name__ == '__main__':
    main()
