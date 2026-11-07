"""Root source-intake guard and path-only Git publication. Never runs Lean."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
name = sys.argv[1]
assert name.startswith('20261028-resume-30') and '/' not in name and '\\' not in name
batch_path = 'docs/source-only/' + name
B = REPO / batch_path

def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p, value): p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
def strings(x):
    if isinstance(x, str): return [x]
    if isinstance(x, list): return [s for v in x for s in strings(v)]
    if isinstance(x, dict): return [s for v in x.values() for s in strings(v)]
    return []
def rows(x, tid):
    result = []
    if isinstance(x, dict):
        if (x.get('task_id') or x.get('task') or x.get('id')) == tid:
            result.append(x)
        for value in x.values(): result.extend(rows(value, tid))
    elif isinstance(x, list):
        for value in x: result.extend(rows(value, tid))
    return result

snapshot = read(HERE / (name + '.json'))
summary = snapshot['summary']
assert summary['tasks'] == summary['delivered_tasks'] == summary['reviewed_tasks'] == 30, summary
assert not summary['source_scan_issues'], summary['source_scan_issues']
assert (B / 'IMPORT_MAP.json').exists(), 'Final direct import map is required'
assert (B / '.gitattributes').read_bytes() == b'* -text\n'
accepted = []
for task in snapshot['tasks']:
    tid = task['id']
    assert task['review_status'] == 'SOURCE_REVIEW_PASS' and not task['author_original_task_complete'], tid
    reg, report = B / tid / 'REGISTRY.json', B / tid / 'REPORT.md'
    assert task['registry_sha256'] == sha(reg), (tid, 'registry changed')
    assert task['report_sha256'] == sha(report), (tid, 'report changed')
    review = read(REPO / task['review_path'])
    matches = rows(review, tid)
    assert matches, (tid, 'missing independent task row')
    recorded = set(s for row in matches for s in strings(row))
    for source in task['sources']:
        assert sha(REPO / source['path']) == source['sha256'], (tid, source['path'], 'changed')
        assert source['sha256'] in recorded, (tid, source['path'], 'not independently hash-locked')
    for row in matches:
        for key, path in [('registry_sha256', reg), ('report_sha256', report)]:
            if row.get(key): assert row[key] == sha(path), (tid, key, 'stale review')
    accepted.append({'id': tid, 'review_path': task['review_path'], 'registry_sha256': sha(reg),
                     'report_sha256': sha(report), 'task_complete': False})

now = datetime.datetime.now(datetime.timezone.utc).isoformat()
write(B / 'ROOT_ACCEPTANCE.json', {'captured_utc': now, 'acceptance': '30 local static mathematical SOURCE_REVIEW_PASS scopes only',
                                  'main_theorem': 'OPEN', 'all_original_targets_open': True,
                                  'compiled': False, 'kernel_verified': False, 'formal_credit': 0,
                                  'summary': summary, 'tasks': accepted})
write(B / 'DELIVERABLES.json', snapshot)
(B / 'README.md').write_text(
    '# Manuscript-internal source batch ' + name + '\n\n' +
    f"{summary['source_files']} Lean proposals; {summary['raw_lines']} raw text lines; {summary['lexical_declarations']} lexical declarations. " +
    'Thirty independent local source reviews. Every original broad target remains OPEN. No compiler, numerical replay, kernel verification or new formal credit.\n\n' +
    'ROOT_ACCEPTANCE.json records exact intake scope. Author REGISTRY/REPORT files and reviews/ retain every actual hypothesis and implementation gap. ' +
    'IMPORT_MAP.json is a direct-import source map, not recursive import/axiom closure. Missing external package bytes are not API verification. ' +
    'All source-only dependencies require the user compiler workflow. No production import root was modified.\n', encoding='utf-8')
files = [p for p in B.rglob('*') if p.is_file() and p.name != 'SOURCE_MANIFEST.json']
manifest = {'captured_utc': now, 'scope': 'Exact raw delivery/source/review bytes; no proof receipt',
            'files': [{'path': p.relative_to(REPO).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size} for p in sorted(files)]}
write(B / 'SOURCE_MANIFEST.json', manifest)

def git(*args): return subprocess.run(['git', *args], cwd=REPO, capture_output=True, check=True).stdout
old = git('rev-parse', 'HEAD').decode().strip()
before = git('diff', '--cached', '--raw', '--', '.', ':(exclude)' + batch_path)
hooks = Path(r'C:\Users\timot\AppData\Local\Temp\goldbach-nohooks-20261028-resume30')
hooks.mkdir(exist_ok=True)
assert not list(hooks.iterdir()), 'Hook bypass directory must be empty'
git('add', '--', batch_path)
git('-c', 'core.hooksPath=' + hooks.as_posix(), 'commit', '--only', '-m',
    'Add ' + name + ' actual manuscript proof connections and independent reviews', '--', batch_path)
assert before == git('diff', '--cached', '--raw', '--', '.', ':(exclude)' + batch_path), 'Unrelated staged state changed'
changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()
assert all(path.startswith(batch_path + '/') for path in changed), changed
for entry in manifest['files']:
    assert hashlib.sha256(git('show', 'HEAD:' + entry['path'])).hexdigest() == entry['sha256'], entry['path']
head = git('rev-parse', 'HEAD').decode().strip()
git('push', 'origin', 'HEAD:refs/heads/codex/proof-continuation-20261015')
remote = git('ls-remote', 'origin', 'refs/heads/codex/proof-continuation-20261015').decode().split()[0]
assert remote == head
receipt = read(HERE / 'PUBLICATION.json')
receipt['captured_utc'] = now
receipt['head'] = head
receipt['batches'].append({'batch': name, 'commit': head, 'parent': old, 'manifest_entries_exact_in_git': len(files)})
write(HERE / 'PUBLICATION.json', receipt)
print(json.dumps({'commit': head, 'batch': name, 'files': len(files), 'remote_exact': True, 'unrelated_staged_preserved': True}))
