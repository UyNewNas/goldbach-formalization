#!/usr/bin/env python3
"""New canonical word owner; reuse both already accepted historical owners."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
helper = Path('/workspace/p15-continue-20261127/docs/p1/20261127/p15-disagreement-partition/validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_member_validation', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.WORK = ROOT / 'selected-sources'
driver.MODULE = 'ImbalancedChen.P1OriginalHistoricalCanonicalOwnerWord'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P1OriginalHistoricalCanonicalOwnerWord.lean'
driver.OUT = ROOT / 'formal-00000'
driver.__file__ = __file__

if '--worker' in sys.argv:
    records = []
    for folder in (
        Path('/workspace/p1-complete-proof/20261127-p15-residual-carrier-v1/formal-00000'),
        Path('/workspace/p1-complete-proof/20261127-p15-rough-owner-partition-v1/formal-00003')):
        receipt = folder / 'VALIDATION_RESULTS.json'
        result = json.loads(receipt.read_text())
        assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
        assert all(result[k]['exit_code'] == 0 for k in ('normal', 'kernel', 'audit'))
        source = Path(result['source']['path'])
        assert driver.fingerprint(source) == result['source']
        obj = folder / ('build/lib/lean/' + result['module'].replace('.', '/') + '.olean')
        outputs = json.loads((folder / 'OUTPUTS_AFTER_NORMAL.json').read_text())
        assert driver.fingerprint(obj) == outputs[0]
        imported = [source, receipt, obj]
        for suffix in ('.private', '.server'):
            p = Path(str(obj) + suffix)
            if p.exists():
                imported.append(p)
        namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
        namespace.mkdir(parents=True, exist_ok=True)
        for p in imported[2:]:
            (namespace / p.name).symlink_to(p)
        records.extend(driver.fingerprint(p) for p in imported)
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_5_complete': False})
else:
    driver.main()
