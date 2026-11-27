#!/usr/bin/env python3
"""Only the new historical canonical mask owner; reuse all old proofs."""
from pathlib import Path
import hashlib
import importlib.util
import json
import shutil
import sys

ROOT = Path(__file__).resolve().parent
helper = Path('/workspace/p15-continue-20261127/docs/p1/20261127/p15-disagreement-partition/validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_member_validation', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.WORK = ROOT / 'selected-sources'
driver.MODULE = 'ImbalancedChen.P1OriginalHistoricalCanonicalTrace'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P1OriginalHistoricalCanonicalTrace.lean'
driver.OUT = ROOT / 'formal-00000'
driver.__file__ = __file__

if '--worker' in sys.argv:
    shutil.copyfile(driver.SOURCE, driver.OUT / 'SELECTED_SOURCE.lean')
    shutil.copyfile(__file__, driver.OUT / 'EXECUTED_DRIVER.py')
    records = []
    namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
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
        assert driver.fingerprint(obj) == json.loads((folder / 'OUTPUTS_AFTER_NORMAL.json').read_text())[0]
        records.extend([driver.fingerprint(source), driver.fingerprint(receipt)])
        for suffix in ('', '.private', '.server'):
            path = Path(str(obj) + suffix)
            if path.exists():
                (namespace / path.name).symlink_to(path)
                records.append(driver.fingerprint(path))
    batch = Path('/workspace/p1-complete-proof/20261128-p15-canonical-prefix-integration')
    selection = json.loads((batch / 'SOURCE_SELECTION.json').read_text())
    assert json.loads((batch / 'RESULT.json').read_text())['status'] == 'PASS_CONTEXT_INTEGRATION'
    for row in selection['sources']:
        receipt = batch / 'modules' / row['module'] / 'ACCEPTED.json'
        result = json.loads(receipt.read_text())
        assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
        assert all(result[k]['exit_code'] == 0 for k in ('normal', 'kernel', 'audit'))
        assert driver.fingerprint(Path(result['inputs']['source']['path'])) == result['inputs']['source']
        records.extend([result['inputs']['source'], driver.fingerprint(receipt)])
        for fp in result['objects']:
            path = Path(fp['path'])
            assert driver.fingerprint(path) == fp
            (namespace / path.name).symlink_to(path)
            records.append(fp)
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_5_complete': False})
else:
    driver.main()
