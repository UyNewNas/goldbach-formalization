import base64, hashlib, json, lzma, os, pathlib, stat, subprocess, sys
if not __debug__: raise SystemExit('requires assertions')
R = pathlib.Path('/workspace/p2-1-20261125')
BRANCH = 'work/p2-1-formal-proof-20261125'
SHA = '14b99ccec7595965607eca3083ae3b0fe5cfbb5c1b21458c3fb7afcc06b94f6a'
AFTER = '5b8b079384b7e70e941513766105234639f93250'
BASE = pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
env = dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')
def git(*args, data=None):
    return subprocess.check_output(['git', '-C', str(R), *args], env=env, input=data)
def digest(data): return hashlib.sha256(data).hexdigest()
def available():
    s = os.statvfs(R); return s.f_bavail * s.f_frsize
def entries():
    return {e.split(b'\t', 1)[1].decode(): e.split(b'\t', 1)[0].decode().split()
            for e in git('ls-files', '-s', '-z').split(b'\0') if e}
def flags():
    return {e[2:].decode(): e[:1].decode() for e in git('ls-files', '-v', '-z').split(b'\0') if e}
def signature(p):
    s = p.lstat(); return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_nlink)
def check_sparse():
    e, f = entries(), flags()
    for r in rows:
        assert e[r['path']] == ['100644', r['git_blob'], '0'] and f[r['path']] == 'S'
        p = R / r['path']; assert not p.exists() and not p.is_symlink()
    assert not git('status', '--porcelain', '--untracked-files=no').strip()
raw = lzma.decompress(base64.b64decode(sys.argv[1])); assert digest(raw) == SHA
m = json.loads(raw); rows = m['candidates']; names = {r['path'] for r in rows}
assert R.resolve() == R and git('rev-parse', '--show-toplevel').decode().strip() == str(R)
assert git('branch', '--show-current').decode().strip() == BRANCH
assert git('rev-parse', 'HEAD').decode().strip() == m['head']
assert not git('status', '--porcelain', '--untracked-files=no').strip()
assert git('rev-parse', '--absolute-git-dir').decode().strip() == m['git_dir']
index = pathlib.Path(git('rev-parse', '--git-path', 'index').decode().strip())
assert str(index) == m['index'] == '/workspace/p2-dot-winner9-20261125/.git/worktrees/p2-1-20261125/index'
assert not git('rev-parse', '--shared-index-path').strip() and not pathlib.Path(str(index) + '.lock').exists()
assert len(rows) == len(names) == 1103 and m['io_markers'] == []
allowed = ('docs/evidence/', 'docs/source-only/', 'verification/proof-continuation/', 'verification/parts/', 'proof-continuation-data/')
suffixes = ('.gz', '.xz', '.bz2', '.zst', '.zip', '.json', '.jsonl', '.csv', '.tsv', '.txt', '.log')
e, f = entries(), flags(); before_signatures = {}
for r in rows:
    name = r['path']; p = R / name
    assert name.startswith(allowed) and name.endswith(suffixes) and '..' not in pathlib.PurePosixPath(name).parts
    assert not name.startswith('docs/source-only/20261124-p2-winner9/') and p.resolve() == p
    assert e[name] == ['100644', r['git_blob'], '0'] and f[name] == 'H'
    assert git('rev-parse', m['head'] + ':' + name).decode().strip() == r['git_blob']
    s = p.lstat(); assert stat.S_ISREG(s.st_mode) and s.st_nlink == 1 and s.st_size == r['bytes']
    data = p.read_bytes(); assert digest(data) == r['sha256'] and git('cat-file', 'blob', r['git_blob']) == data
    before_signatures[name] = signature(p)
plan_path = R / 'docs/verification/20261125-p2-1/TARGETS.json'
plan = json.loads(plan_path.read_bytes())
sources = [R / r['source'] for r in plan['modules']]
for r in plan['modules']: assert digest((R / r['source']).read_bytes()) == r['source_sha256']
refs = sources + list((R / 'verification/part2').glob('*.py')) + list((R / 'verification/part2').glob('*.lean'))
refs += list((R / '.lake/p2-private').rglob('*.json')) + list(plan_path.parent.glob('*')) + [BASE]
for p in refs:
    if p.is_file() and not p.is_symlink():
        data = p.read_bytes(); assert not any(name.encode() in data for name in names), str(p)
protected = [BASE, plan_path, R / '.lake/p2-private/records.json'] + list((R / '.lake/p2-private/audit').glob('*/latest.json'))
protected_hashes = {str(p): digest(p.read_bytes()) for p in protected}
assert protected_hashes[str(BASE)] == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
recovery = R / '.lake/p2-private/P21_SPARSE_WORKTREE.json'
result_path = R / '.lake/p2-private/P21_SPARSE_RESULT.json'
for p in (recovery, result_path):
    assert p.parent.resolve() == p.parent and not os.path.lexists(p)
space_before = available(); bootstrap = max(rows, key=lambda r: r['allocated_bytes']); bp = R / bootstrap['path']
assert bootstrap['allocated_bytes'] > 2 * index.stat().st_size + len(raw) + 1048576
assert signature(bp) == before_signatures[bootstrap['path']]
print('P21_SPARSE_PREFLIGHT', json.dumps({'manifest_sha256': SHA, 'count': len(rows), 'allocated_bytes': sum(r['allocated_bytes'] for r in rows), 'index_bytes': index.stat().st_size, 'free_before': space_before, 'bootstrap': bootstrap}), flush=True)
bp.unlink()
with recovery.open('xb') as stream: stream.write(raw)
try:
    git('update-index', '--skip-worktree', '-z', '--stdin', data=b'\0'.join(r['path'].encode() for r in rows) + b'\0')
except subprocess.CalledProcessError:
    print('P21_SPARSE_STOP_AFTER_BOOTSTRAP', json.dumps({'removed': bootstrap, 'recovery': str(recovery)}), flush=True)
    raise
for r in rows:
    if r['path'] == bootstrap['path']: continue
    p = R / r['path']; assert signature(p) == before_signatures[r['path']]
    p.unlink()
check_sparse()
for path, h in protected_hashes.items(): assert digest(pathlib.Path(path).read_bytes()) == h
for r in plan['modules']: assert digest((R / r['source']).read_bytes()) == r['source_sha256']
space_after = available()
assert space_after > space_before
print('P21_SPARSE_COMPLETED', json.dumps({'missing_copies': len(rows), 'free_after': space_after, 'actual_free_increase': space_after - space_before, 'protected_hashes_unchanged': True, 'all_140_sources_unchanged': True, 'recovery': str(recovery), 'manifest_sha256': SHA}), flush=True)
git('-c', 'gc.auto=0', '-c', 'maintenance.auto=false', 'fetch', 'origin', BRANCH)
new = git('rev-parse', 'FETCH_HEAD').decode().strip(); assert new == AFTER
changed = {p.decode() for p in git('diff', '--no-renames', '--name-only', '-z', m['head'], new).split(b'\0') if p}
assert not names & changed
print('P21_SPARSE_FAST_FORWARD_GUARD', json.dumps({'old': m['head'], 'new': new, 'retired_path_changes': 0}), flush=True)
git('merge', '--ff-only', new)
check_sparse()
new_plan = json.loads(plan_path.read_bytes())
for r in new_plan['modules']: assert digest((R / r['source']).read_bytes()) == r['source_sha256']
report = {'manifest_sha256': SHA, 'manifest': str(recovery), 'old_head': m['head'], 'new_head': new, 'removed_worktree_copies': len(rows), 'raw_archived_bytes': sum(r['bytes'] for r in rows), 'free_before': space_before, 'free_after_cleanup': space_after, 'free_after_fetch': available(), 'protected_receipts_and_base_preserved': True, 'source_snapshot_commit': new_plan['source_snapshot_commit'], 'all_140_source_hashes_match': True, 'skip_flags_oid_absence_verified': True, 'proof_credit': False, 'restore': 'Read each retained git_blob with git cat-file blob, restore its exact bytes to its listed own worktree path, then clear skip-worktree only for these paths. Reserve sufficient space before restoring.'}
with result_path.open('xb') as stream: stream.write((json.dumps(report, indent=2) + '\n').encode())
print('P21_SPARSE_RESULT', json.dumps(report), flush=True)
audit = R / '.lake/p2-private/audit/ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Data/latest.json'
v = json.loads(audit.read_bytes()); name = v.get('audit', {}).get('log')
if name:
    p = (R / name).resolve(); assert p.is_relative_to((R / '.lake/p2-private/audit').resolve())
    data = p.read_bytes(); assert digest(data) == v['audit']['log_sha256']
    print('P21_OLD_DATA_AUDIT_LOG', json.dumps({'path': str(p), 'bytes': len(data), 'sha256': digest(data), 'error': v.get('error'), 'text': data.decode(errors='replace')[-8000:]}), flush=True)
