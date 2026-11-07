"""Record unaccepted source candidates separately from verified components."""
from pathlib import Path
import hashlib
import json
import shutil

STATE = Path(__file__).resolve().parent
ROOT = STATE.parents[1]
DEST = ROOT / 'verification/proof-continuation/2026-10-15'
CANDIDATES = {
    'ImbalancedChen.CurrentChenPairDensity': 'Actual source attempt failed the permitted Lean resource budget during imports; target proof not elaborated.',
    'ImbalancedChen.CurrentChenUpsilon5OrdinaryMean': 'Final ordinary count-mean assembly has not been executed; it still imports the unaccepted density supplier.',
    'ImbalancedChen.CurrentChenUpsilon6OrdinaryMean': 'Uncompiled source through fixed-buffer selector/harmonic/normalized main-sum layers; final count payment is not written.',
    'ImbalancedChen.Part3ReciprocalAPSupplier': 'New target not executed; limited external prerequisite bootstrap stopped at a resource failure.',
    'ImbalancedChen.Certificates.PairedV2FullCertificate': 'Not executed; requires the full original-strip chain, beyond the frozen baseline pilot.',
    'ImbalancedChen.ActualThirdPrefixTailIntegral': 'Broad arithmetic tuple/profile bridge is not compiled; the separate canonical integral core is verified.',
}


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    verified = json.loads((DEST / 'manifest.json').read_text())['modules']
    rows = {}
    for module, note in CANDIDATES.items():
        path = ROOT / (module.replace('.', '/') + '.lean')
        digest = sha(path)
        assert module not in verified, 'Accepted proof unexpectedly appears in candidate-only list'
        rows[module] = {'status': 'UNACCEPTED_SOURCE', 'source_sha256': digest, 'note': note}
    failures = []
    for receipt in sorted((STATE / 'runs').glob('*/receipt.json')):
        r = json.loads(receipt.read_text())
        module = r.get('module')
        if module not in rows and module != 'ImbalancedChen.CurrentChenUpsilon5FiniteMean':
            continue
        if r.get('status') not in ('FAILED', 'RESOURCE_STOP', 'GUARD_ERROR'):
            continue
        target = DEST / 'unaccepted-attempts' / receipt.parent.name
        target.mkdir(parents=True, exist_ok=True)
        for name in ('receipt.json', 'stdout.log'):
            src = receipt.parent / name
            dst = target / name
            if dst.exists():
                assert sha(src) == sha(dst)
            else:
                shutil.copyfile(src, dst)
        failures.append({
            'module': module, 'status': r['status'],
            'attempt_source_sha256': r['binding']['source_sha256'],
            'matches_current_candidate': module in rows and r['binding']['source_sha256'] == rows[module]['source_sha256'],
            'module_now_has_a_verified_new_source': module in verified,
            'receipt': (target.relative_to(DEST) / 'receipt.json').as_posix(),
        })
    report = {
        'schema': 'unaccepted-candidates-v1',
        'scope': 'Source preservation and original failed-attempt evidence; no proof acceptance',
        'main_theorem_proved': False,
        'candidates': rows,
        'failed_attempts': failures,
    }
    target = DEST / 'unaccepted-candidates.json'
    target.write_text(json.dumps(report, indent=2) + '\n', newline='\n')
    print(json.dumps({'candidate_modules': len(rows), 'failed_attempts': len(failures)}), flush=True)


if __name__ == '__main__':
    main()
