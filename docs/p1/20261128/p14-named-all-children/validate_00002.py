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
driver.MODULE = 'ImbalancedChen.P5NamedFifthAllChildren'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P5NamedFifthAllChildren.lean'
driver.OUT = ROOT / 'formal-00002'
driver.__file__ = __file__

original_run = driver.run

def original_proof_options(label, command, environment):
    if label == 'normal':
        command = [command[0], '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', *command[1:]]
    return original_run(label, command, environment)

driver.run = original_proof_options

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
    payload = Path('/workspace/p1-complete-proof/20261128-p14-named-payload-semantics/formal-00006')
    receipt = payload / 'VALIDATION_RESULTS.json'
    accepted = json.loads(receipt.read_text())
    assert accepted['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
    assert accepted['source']['sha256'] == 'ae7d1ab8f3eac1977df657094548b9ffa578443ac087c569850f318c0cb2d623'
    records.append(driver.fingerprint(receipt))
    actual = driver.fingerprint(Path(accepted['source']['path']))
    assert actual == accepted['source']
    records.append(actual)
    for item in json.loads((payload / 'OUTPUTS_AFTER_NORMAL.json').read_text()):
        actual = driver.fingerprint(Path(item['path']))
        assert actual == item
        records.append(actual)
    for label in ['SELECTED_SOURCE.lean', 'EXECUTED_DRIVER.py', 'kernel.log', 'owned-audit.log', 'COUPLED_IMPORT_VALIDATION.json']:
        records.append(driver.fingerprint(payload / label))
    namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    alias_records = []
    for source in (payload / 'build/lib/lean/ImbalancedChen').glob('P5NamedFifthPayloadSemantics.*'):
        assert source.is_file() and not source.is_symlink()
        target = namespace / source.name
        assert not target.exists()
        target.symlink_to(source)
        records.append(driver.fingerprint(source))
        alias_records.append({'path': str(target), 'target': str(source)})
    assert len(alias_records) >= 2
    driver.save('REUSED_EXTRA_ALIAS_LINKS.json', alias_records)
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    assert all(Path(x['path']).is_symlink() and str(Path(x['path']).readlink()) == x['target'] for x in alias_records)
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_4_complete': False})
else:
    driver.main()
