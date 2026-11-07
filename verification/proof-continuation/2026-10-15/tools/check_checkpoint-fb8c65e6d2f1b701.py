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

PUBLICATION_SOURCE_BINDINGS = {'ImbalancedChen.Part3SharedFirstFactorSupportedCoreCauchy': '13a0733609f30d51af3649566b4d85053f866ab785fd35bac3c2f317c95a794e', 'ImbalancedChen.Part3NonresonantManuscriptCostAlgebra': 'dc943c841bc0d570c9a90d5009d2e05b95ee288209f9a60cb6490142849c5cd2', 'ImbalancedChen.Part3SharedFirstFactorGeneralDRootPacket': '7e284bf1d7bdfac5ad59f7c509cedc218b10db3b4ccc1aced33e208abb3395af', 'ImbalancedChen.Part3SharedFirstFactorGeneralDPairedFourier': '024842983e6a72164d07d06685ea7b18f49833bc6b6dcfc4e1997fc63fd53a6e'}
PUBLICATION_ACCEPTANCE = 'source-reviews/20261021-supported13a0-root-actual13-terminal-acceptance.json'
PUBLICATION_ACCEPTANCE_SHA256 = '711dc0aa8b5ae32951e5d5e35bf0395b61f5bf36ec4105f15bea4d520f3ac1c2'
PUBLICATION_CENSUS = 'source-reviews/20261021T101322959323Z-runtime-fresh-current-terminal-owned-census.json'
PUBLICATION_CENSUS_SHA256 = '00445cc0bc388a70374ed800d7d634332199280bd52415c46b83a240774a04e9'


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
    # Append exact-byte source rules while preserving the original mixed endings.
    attributes = ROOT / '.gitattributes'
    contents = attributes.read_bytes()
    existing_rules = set(contents.splitlines())
    additions = [f'{relative} -text'.encode('utf-8') for relative in sorted(sources)
                 if f'{relative} -text'.encode('utf-8') not in existing_rules]
    if additions:
        attributes.write_bytes(contents + (b'' if contents.endswith(b'\n') else b'\n') +
                               b'\n'.join(additions) + b'\n')
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
