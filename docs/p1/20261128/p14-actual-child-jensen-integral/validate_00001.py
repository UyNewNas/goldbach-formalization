#!/usr/bin/env python3
"""Actual continuation/support bridge; reuse accepted historical and P2 owners."""
import hashlib
import importlib.util
import json
import shutil
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
helper = Path('/workspace/p15-continue-20261127/docs/p1/20261127/p15-disagreement-partition/validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_member_validation', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.WORK = ROOT / 'selected-sources'
driver.MODULE = 'ImbalancedChen.P5OldFifthActualChildJensenIntegral'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P5OldFifthActualChildJensenIntegral.lean'
driver.OUT = ROOT / 'formal-00001'
driver.__file__ = __file__

if '--worker' in sys.argv:
    shutil.copyfile(driver.SOURCE, driver.OUT / 'SELECTED_SOURCE.lean')
    shutil.copyfile(__file__, driver.OUT / 'EXECUTED_DRIVER.py')
    folder = Path('/workspace/p1-complete-proof/20261125-p14-continuation/pointwise-q-profile-alias-retry/4a396d6c413f5bda1c9246b13b0fa64c04a93a97/audits/b6b5cfde009e80400b7e/lane-0')
    receipt = folder / 'VALIDATION_RESULTS.json'
    result = json.loads(receipt.read_text())
    assert result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
    assert result['total_owned_exports'] == 23
    records = [driver.fingerprint(receipt)]
    for relative, fp in result['source_plus_five_outputs']['ImbalancedChen.P5OldFifthPointwiseQ'].items():
        path = Path('/workspace/blue-member-build') / relative
        actual = driver.fingerprint(path)
        assert actual['bytes'] == fp['bytes'] and actual['sha256'] == fp['sha256']
        records.append(actual)
    for label in ['P5OldFifthPointwiseQ-kernel.log', 'all-owned-types-axioms.log']:
        records.append(driver.fingerprint(folder / label))
    first = Path('/workspace/p1-complete-proof/20261128-p14-first-f-concavity/formal-00001')
    rr = first / 'VALIDATION_RESULTS.json'
    old = json.loads(rr.read_text())
    assert old['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    assert old['module'] == 'ImbalancedChen.P5OldFifthFirstFConcavity'
    assert driver.fingerprint(Path(old['source']['path'])) == old['source']
    obj = first / 'build/lib/lean/ImbalancedChen/P5OldFifthFirstFConcavity.olean'
    assert driver.fingerprint(obj) == json.loads((first / 'OUTPUTS_AFTER_NORMAL.json').read_text())[0]
    namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    records.extend([driver.fingerprint(rr), old['source']])
    for suffix in ('', '.private', '.server'):
        path = Path(str(obj) + suffix)
        if path.exists():
            (namespace / path.name).symlink_to(path)
            records.append(driver.fingerprint(path))
    jensen = Path('/workspace/p1-complete-proof/20261128-p14-child-q-jensen/formal-00002')
    rr = jensen / 'VALIDATION_RESULTS.json'
    old = json.loads(rr.read_text())
    assert old['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    assert old['module'] == 'ImbalancedChen.P5OldFifthChildQJensen'
    assert driver.fingerprint(Path(old['source']['path'])) == old['source']
    obj = jensen / 'build/lib/lean/ImbalancedChen/P5OldFifthChildQJensen.olean'
    assert driver.fingerprint(obj) == json.loads((jensen / 'OUTPUTS_AFTER_NORMAL.json').read_text())[0]
    records.extend([driver.fingerprint(rr), old['source']])
    for suffix in ('', '.private', '.server'):
        path = Path(str(obj) + suffix)
        if path.exists():
            (namespace / path.name).symlink_to(path)
            records.append(driver.fingerprint(path))
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_4_complete': False})
else:
    driver.main()
