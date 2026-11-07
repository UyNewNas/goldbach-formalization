"""Check archived bytes and optionally stage only explicitly scoped paths.

This is archive integrity, not a new Lean proof check or cache acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-c', 'core.autocrlf=false', *args], cwd=ROOT)


parser = argparse.ArgumentParser()
parser.add_argument('--stage', action='store_true')
args = parser.parse_args()
manifest = json.loads((DEST / 'manifest.json').read_text(encoding='utf-8'))
candidates = json.loads((DEST / 'unaccepted-candidates.json').read_text(encoding='utf-8'))
assert not manifest['main_theorem_proved']
assert not manifest['aggregate_build_claimed']
assert not manifest['external_closure_replay_claimed']
assert not candidates['main_theorem_proved']
assert not (set(manifest['modules']) & set(candidates['candidates']))
assert git('branch', '--show-current').decode().strip() == 'codex/proof-continuation-20261015'
records = {**manifest['modules'], **candidates['candidates']}
sources = {}
for module, entry in records.items():
    relative = module.replace('.', '/') + '.lean'
    assert sha(ROOT / relative) == entry['source_sha256'], relative
    sources[relative] = entry['source_sha256']
for relative, digest in manifest['files'].items():
    assert sha(DEST / relative) == digest, relative
for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
    assert (ROOT / name).read_bytes() == git('show', 'HEAD:' + name), name
    assert (DEST / 'pins' / name).read_bytes() == (ROOT / name).read_bytes(), name
report = 'docs/PROOF_CONTINUATION_2026-10-15.md'
allowed = set(sources) | {'.gitattributes', report}
prefix = 'verification/proof-continuation/2026-10-15/'
if args.stage:
    git('add', '--', '.gitattributes', report, *sorted(sources), prefix)
    staged = git('diff', '--cached', '--name-only', '-z').decode('utf-8').split('\0')
    assert all(not p or p in allowed or p.startswith(prefix) for p in staged)
    for relative, digest in sources.items():
        assert hashlib.sha256(git('show', ':' + relative)).hexdigest() == digest, relative
    for relative, digest in manifest['files'].items():
        assert hashlib.sha256(git('show', ':' + prefix + relative)).hexdigest() == digest, relative
    assert git('show', ':' + prefix + 'manifest.json') == (DEST / 'manifest.json').read_bytes()
    git('diff', '--cached', '--check')
print(json.dumps({'scope': 'ARCHIVE_AND_INDEX_INTEGRITY_ONLY',
                  'accepted_modules': len(manifest['modules']),
                  'owned_declarations': manifest['declaration_count'],
                  'unaccepted_sources': len(candidates['candidates']),
                  'archived_files': len(manifest['files']),
                  'staged': args.stage, 'main_theorem_proved': False}))
