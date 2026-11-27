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
driver.MODULE = 'ImbalancedChen.P5OriginalWireFloorInstantiation'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P5OriginalWireFloorInstantiation.lean'
driver.OUT = ROOT / 'formal-00000'
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
    contexts = [
        ('20261128-p14-first-f-concavity', 'formal-00001', '0be94a2aff75bff8cce2bb7b1c9b7d351fe024ab427c644dcf6ae5cacb4b1c15'),
        ('20261128-p14-child-q-jensen', 'formal-00002', '14580e3aa6745e62144266578819dbe630dc19dab28fd74e5cda572532c9f4fc'),
        ('20261128-p14-actual-child-jensen-integral', 'formal-00001', '60a456311f1cd066a4fa1b600e8fd5a27e8557a1b14838785b13c40a40f08896'),
        ('20261128-p14-named-payload-semantics', 'formal-00006', 'ae7d1ab8f3eac1977df657094548b9ffa578443ac087c569850f318c0cb2d623'),
        ('20261128-p14-named-all-children', 'formal-00002', 'feeb7b01ed49a31a0fee3f7fb0b82dab2d72af89424786298b05f5c3c8b6f9cd'),
        ('20261128-p14-selected-owner-jensen-reserve', 'formal-00002', 'bb57ca6a556c11ac5255a3644325de74a844d679ab32c16387989c55062ac376'),
        ('20261128-p14-named-selected-jensen', 'formal-00000', '5b886d4be9651e26b794e3c0cad75bb6a0daeca8a68b5588fca6be6adf65cf98'),
        ('20261128-p14-sharp-directed-log', 'formal-00000', '96094318b9a7e97231e59a169455b3fb1c9f0f0a1b5753a3f7dc95290d4b8759'),
        ('20261128-p14-named-child-specific-ratio', 'formal-00001', '3223a0568baf695c9fd2c08e9996e19f736f779d37ddd393077fb9d7271b71fa'),
        ('20261128-p14-integer-wire-definition-split', 'formal-00000', '27c5eee98161b643ce70b8f8429b0e095b82e23709cc05c001e133265a3ceaa7'),
        ('20261128-p14-arbitrary-mask-child-ratio', 'formal-00001', 'c965f3ac2d2bfd2349327193c7c7d0a7c0ad2ac0d2f199b1d7dd7b25d672416e'),
        ('20261128-p14-named-q80-floor-soundness', 'formal-00001', 'c87a1be13a0d6f4574fd0854ac265408416b5f486191edc9f75df447d1592562'),
        ('20261128-p14-generic-wire-floor-receiver', 'formal-00002', '013881f9ce1ac123fc1aa5689ece0659885965908dba31b1f02d15f1fcbd0f29'),
        ('20261128-p14-wire-parent-pick-alignment', 'formal-00001', '2d19555a99df321753cf35bb37cff1a1ebdb727139dd9972a4c401f69094138a'),
        ('20261128-p14-wire-child-d-identity', 'formal-00001', '4506d34f68c925a7b491aea6b01e896cb48a38351156eaa46063d961f2b4babd'),
        ('20261128-p14-named-wire-geometry-fields', 'formal-00000', 'ba9630a80acb1d3efe0669fe720d417772dc4c74ca05bd0a07a337baede2ce69'),
        ('20261128-p14-wire-rational-floor-expansion', 'formal-00000', 'c155bebcb51f1b7c2e52e574a33fa7b7c47090511159fb7ad32aa0a6a34b3dd9'),
        ('20261128-p14-wire-expanded-floor-algebra', 'formal-00001', 'c84bf7f7ef585bc15642a4a54923f6c37863794f267d5ccdb8b9bc5e5f641961')]
    namespace = driver.OUT / 'build/lib/lean/ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    aliases = []
    for parent, attempt, source_sha in contexts:
        folder = Path('/workspace/p1-complete-proof') / parent / attempt
        receipt = folder / 'VALIDATION_RESULTS.json'
        accepted = json.loads(receipt.read_text())
        assert accepted['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
        assert accepted['source']['sha256'] == source_sha
        records.append(driver.fingerprint(receipt))
        assert driver.fingerprint(Path(accepted['source']['path'])) == accepted['source']
        records.append(accepted['source'])
        for fp in json.loads((folder / 'OUTPUTS_AFTER_NORMAL.json').read_text()):
            assert driver.fingerprint(Path(fp['path'])) == fp
            records.append(fp)
        for label in ['SELECTED_SOURCE.lean', 'EXECUTED_DRIVER.py', 'kernel.log', 'owned-audit.log', 'COUPLED_IMPORT_VALIDATION.json']:
            records.append(driver.fingerprint(folder / label))
        for source in (folder / 'build/lib/lean/ImbalancedChen').glob(accepted['module'].split('.')[-1] + '.*'):
            assert source.is_file() and not source.is_symlink()
            target = namespace / source.name
            assert not target.exists()
            target.symlink_to(source)
            records.append(driver.fingerprint(source))
            aliases.append({'path': str(target), 'target': str(source)})
    assert len(aliases) == 36
    driver.save('REUSED_EXTRA_ALIAS_LINKS.json', aliases)
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    assert all(Path(x['path']).is_symlink() and str(Path(x['path']).readlink()) == x['target'] for x in aliases)
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_4_complete': False})
else:
    driver.main()
