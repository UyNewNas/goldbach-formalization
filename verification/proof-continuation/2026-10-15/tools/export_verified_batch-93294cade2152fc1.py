"""Archive successful owned proof evidence without upgrading its scope.

This copies existing terminal receipts byte for byte. It does not run Lean,
repair a receipt, accept a cache, or claim an aggregate proof.
"""
from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'
MODULES = [
    'ImbalancedChen.CurrentChenPairLevelGeometry',
    'ImbalancedChen.CurrentChenPairRosser',
    'ImbalancedChen.CurrentChenUpsilon6KernelBuffer',
    'ImbalancedChen.CurrentChenUpsilon6OrdinarySieveKernel',
    'ImbalancedChen.Part3CenteredFourier',
    'ImbalancedChen.Certificates.PairedV2FullBuchstab',
    'ImbalancedChen.ActualSieveGapTailDecay',
    'ImbalancedChen.ActualSieveGapTailBounds',
    'ImbalancedChen.ActualThirdPrefixTailIntegral',
]


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def copy(source, dest):
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        assert sha(source) == sha(dest), f'Existing evidence differs: {dest}'
    else:
        shutil.copyfile(source, dest)
    assert sha(source) == sha(dest)


def main():
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == \
        '3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af', 'Unexpected pre-publication baseline'
    frozen = {m: sha(ROOT / (m.replace('.', '/') + '.lean')) for m in MODULES}
    audits = []
    accepted = {}
    for receipt in sorted((STATE / 'audits').glob('*/receipt.json')):
        r = json.loads(receipt.read_text())
        if r.get('status') != 'PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS':
            continue
        if not r['targets'] or any(frozen.get(m) != h for m, h in r['targets'].items()):
            continue
        assert r['inputs_before'] == r['inputs_after']
        assert not r['external_closure_replay_claimed'] and not r['unconditional_main_claimed']
        for m, h in r['targets'].items():
            accepted[m] = {'source_sha256': h, 'declarations': r['declaration_counts'][m],
                           'audit': str(Path('audits') / receipt.parent.name / 'receipt.json')}
        audits.append(receipt.parent)
    assert len(accepted) >= 4, 'Rosser and the first three leaves must have complete audits'
    assert all(m in accepted for m in MODULES[:4])
    for module, record in accepted.items():
        options = []
        for receipt in (STATE / 'runs').glob('*/receipt.json'):
            r = json.loads(receipt.read_text())
            if r.get('module') == module and r.get('status') == 'PASS' and \
                    r.get('binding', {}).get('source_sha256') == record['source_sha256']:
                assert r['binding'] == r['binding_after']
                options.append(receipt)
        assert options, 'No successful actual source compile: ' + module
        receipt = sorted(options)[-1]
        r = json.loads(receipt.read_text())
        assert r['warnings_as_errors'] and r['exit_code'] == 0
        record['compile'] = str(Path('compilation') / receipt.parent.name / 'receipt.json')
        record['object_parts'] = r['object_parts']
        for name in ('receipt.json', 'stdout.log'):
            copy(receipt.parent / name, DEST / 'compilation' / receipt.parent.name / name)
    for directory in audits:
        for file in directory.iterdir():
            if file.is_file():
                copy(file, DEST / 'audits' / directory.name / file.name)
    for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        copy(ROOT / name, DEST / 'pins' / name)
    for file in (STATE / 'runtime.py', STATE / 'runtime.before-6144-budget.py',
                 STATE / 'audit_owned.py', Path(__file__),
                 ROOT / 'verification/parts/p0/queue/AuditTemplate.lean',
                 ROOT.parent / 'goldbach-integration/verification/parts/takeover-p0/checker_memory_guard.py'):
        copy(file, DEST / 'tools' / (file.stem + '-' + sha(file)[:16] + file.suffix))
    for module, record in accepted.items():
        assert sha(ROOT / (module.replace('.', '/') + '.lean')) == record['source_sha256']
    files = {str(file.relative_to(DEST)).replace('\\', '/'): sha(file)
             for file in sorted(DEST.rglob('*')) if file.is_file() and file.name != 'manifest.json'}
    manifest = {
        'schema': 'proof-continuation-owned-evidence-v1',
        'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'baseline': '3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af',
        'manuscript': 'ba6ec11d800eccc54406490631895e174de85766',
        'scope': 'Strict actual source compilation, owned original-object stock replay, complete owned types/inventory/transitive axioms only',
        'main_theorem_proved': False,
        'aggregate_build_claimed': False,
        'external_closure_replay_claimed': False,
        'modules': accepted,
        'declaration_count': sum(r['declarations'] for r in accepted.values()),
        'files': files,
        'notes': [
            'Archive files are copied byte for byte; no old receipt was rewritten.',
            'Absolute paths in receipts are historical execution paths, not portable commands.',
            'Archived runtime versions may not include every earlier producer version; receipt hashes remain authoritative.',
            'Inherited remote-cache prerequisites remain development-only; this archive does not claim their independent replay.',
            'An integrity check of this manifest is not a Lean proof check.',
        ],
    }
    (DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'modules': list(accepted), 'declarations': manifest['declaration_count'],
                      'files': len(files), 'path': str(DEST)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
