"""Root maintenance only: preserve reviewed extra or paused partial bytes; no compiler."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
name, mode = sys.argv[1:]
assert (name, mode) in [('20261028-adopted-query', 'reviewed-extra'),
                        ('20261028-resume-30g', 'paused-partial')]
rel = 'docs/source-only/' + name
folder = REPO / rel
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p, v): p.write_text(json.dumps(v, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
def git(*args): return subprocess.run(['git', *args], cwd=REPO, capture_output=True, check=True).stdout
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
assert (folder / '.gitattributes').read_bytes() == b'* -text\n'
if mode == 'reviewed-extra':
    review = read(folder / 'reviews/independent.json')
    assert review['status'] == 'SOURCE_REVIEW_PASS'
    for source in review['sources']:
        assert sha(REPO / source['path']) == source['expected_sha256'] == source['actual_sha256']
    for item in review['artifact_hashes']:
        assert sha(folder / item['path']) == item['sha256']
    write(folder / 'ROOT_ACCEPTANCE.json', {
        'captured_utc': now, 'scope': review['status_scope'],
        'review_sha256': sha(folder / 'reviews/independent.json'),
        'acceptance': 'SOURCE_REVIEW_PASS for three local source modules only',
        'main_theorem': 'OPEN', 'all_original_targets_open': True,
        'counts_toward_regular_thirty': False, 'compiled': False,
        'kernel_verified': False, 'formal_credit': 0})
else:
    pause = read(HERE / 'PAUSE_STATE.json')
    write(folder / 'ROOT_PAUSE_SNAPSHOT.json', {
        'captured_utc': now, 'status': 'PAUSED_PARTIAL_UNREVIEWED',
        'pause_evidence': pause, 'scope': 'Existing bytes only after author/reviewer interrupts. Some files and metadata are incomplete. Individual review evidence, if present, is not whole-batch acceptance.',
        'main_theorem': 'OPEN', 'all_original_targets_open': True,
        'batch_source_review_pass': False, 'compiled': False,
        'kernel_verified': False, 'formal_credit': 0,
        'literal_data_note': 'Large literal transcriptions are unevaluated source data, not checked certificate values or proof progress.'})
    (folder / 'README.md').write_text('# Paused seventh source batch\n\nExisting partial source and metadata bytes are preserved at the root quota stop. No whole-batch acceptance, compilation, numerical replay or formal credit. All original proof targets remain OPEN. Literal archives are source transcriptions only. ROOT_PAUSE_SNAPSHOT.json records the stop scope; SOURCE_MANIFEST.json locks exact delivered bytes.\n', encoding='utf-8')
files = [p for p in sorted(folder.rglob('*')) if p.is_file() and p.name != 'SOURCE_MANIFEST.json']
manifest = {'captured_utc': now, 'scope': mode + '; exact raw bytes only; no proof receipt',
            'files': [{'path': p.relative_to(REPO).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size} for p in files]}
write(folder / 'SOURCE_MANIFEST.json', manifest)
old = git('rev-parse', 'HEAD').decode().strip()
before = git('diff', '--cached', '--raw', '--', '.', ':(exclude)' + rel)
hooks = Path(r'C:\Users\timot\AppData\Local\Temp\goldbach-nohooks-20261028-resume30')
hooks.mkdir(exist_ok=True)
assert not list(hooks.iterdir())
git('add', '--', rel)
git('-c', 'core.hooksPath=' + hooks.as_posix(), 'commit', '--only', '-m',
    'Preserve ' + name + ' ' + mode + ' source snapshot', '--', rel)
assert before == git('diff', '--cached', '--raw', '--', '.', ':(exclude)' + rel)
changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines()
assert all(p.startswith(rel + '/') for p in changed)
for item in manifest['files']:
    assert hashlib.sha256(git('cat-file', 'blob', 'HEAD:' + item['path'])).hexdigest() == item['sha256']
head = git('rev-parse', 'HEAD').decode().strip()
receipt = {'captured_utc': now, 'commit': head, 'parent': old, 'mode': mode,
           'path': rel, 'manifest_entries_exact_in_git': len(files),
           'unrelated_staged_state_preserved': True, 'remote_exact_sha_verified': False,
           'compiled': False, 'formal_credit': 0}
target = 'EXTRA_QUERY_PUBLICATION.json' if mode == 'reviewed-extra' else 'PAUSED_G_PUBLICATION.json'
write(HERE / target, receipt)
print(json.dumps(receipt))
