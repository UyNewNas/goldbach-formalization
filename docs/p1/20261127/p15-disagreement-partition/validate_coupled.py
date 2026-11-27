#!/usr/bin/env python3
"""Validate the strengthened partition with the accepted residual import.

The original validation helper remains frozen. Only isolated paths are added;
the residual owner is neither rebuilt nor replayed here.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

helper = Path(__file__).with_name('validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_partition_validation_helper', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.OUT = Path('/workspace/p1-complete-proof/20261127-p15-disagreement-partition-v1/formal-coupled-00001')
driver.__file__ = __file__

if '--worker' in sys.argv:
    residual = Path('/workspace/p1-complete-proof/20261127-p15-residual-carrier-v1/formal-00000')
    result_file = residual / 'VALIDATION_RESULTS.json'
    result = json.loads(result_file.read_text())
    assert result['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    assert result['module'] == 'ImbalancedChen.P1OriginalHistoricalResidualCarrier'
    source = driver.WORK / 'ImbalancedChen/P1OriginalHistoricalResidualCarrier.lean'
    obj = residual / 'build/lib/lean/ImbalancedChen/P1OriginalHistoricalResidualCarrier.olean'
    assert driver.fingerprint(source) == result['source']
    outputs = json.loads((residual / 'OUTPUTS_AFTER_NORMAL.json').read_text())
    assert driver.fingerprint(obj) == outputs[0]
    original = [driver.fingerprint(p) for p in (source, obj, result_file)]
    namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    alias = namespace / obj.name
    alias.symlink_to(obj)
    driver.save('RESIDUAL_IMPORT_BEFORE.json', original)
    driver.main()
    after = [driver.fingerprint(p) for p in (source, obj, result_file)]
    assert after == original and alias.is_symlink() and alias.resolve() == obj
    driver.save('RESIDUAL_IMPORT_AFTER.json', after)
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'reused_residual_owner': result['module'],
        'original_residual_validation': original[2],
        'new_residual_normal_or_kernel_commands': 0,
        'whole_P1_5_complete': False})
else:
    driver.main()
