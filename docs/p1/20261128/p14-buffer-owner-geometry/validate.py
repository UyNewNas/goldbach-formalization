#!/usr/bin/env python3
"""Actual continuation/support bridge; reuse accepted historical and P2 owners."""
import hashlib
import importlib.util
import json
import shutil
from pathlib import Path
import sys
import os

ROOT = Path(__file__).resolve().parent
helper = Path('/workspace/p15-continue-20261127/docs/p1/20261127/p15-disagreement-partition/validate.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '04e67f06c4232a6bbd10be8d6c5419287c51a6c14e4b56e39864f230115ce6f7'
spec = importlib.util.spec_from_file_location('frozen_member_validation', helper)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
driver.WORK = ROOT / 'selected-sources-00002'
driver.MODULE = 'ImbalancedChen.P5OriginalBufferOwnerGeometry'
driver.SOURCE = driver.WORK / 'ImbalancedChen/P5OriginalBufferOwnerGeometry.lean'
driver.OUT = ROOT / 'formal-00002'
driver.__file__ = __file__

original_run = driver.run

def original_proof_options(label, command, environment):
    if label == 'normal':
        command = [command[0], '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000', *command[1:]]
    return original_run(label, command, environment)

driver.run = original_proof_options

if '--worker' in sys.argv:
    seed = Path('/workspace/p1-complete-proof/20261128-p14-parent-four-gate-block000/formal-00000')
    seed_manifests = [seed / 'REUSED_IMPORT_LINKS.json', seed / 'REUSED_EXTRA_ALIAS_LINKS.json']
    seed_before = [driver.fingerprint(p) for p in seed_manifests]
    alias_cache = {}
    for manifest_path in seed_manifests:
        for link in json.loads(manifest_path.read_text()):
            p, target = Path(link['path']), link['target']
            assert Path(target).is_absolute()
            assert p.is_symlink() and os.readlink(p) == target
            alias_cache.setdefault(target, p)
    storage_stats = {'hardlinked_symlink_inodes': 0, 'new_symlinks': 0,
        'only_exact_absolute_targets': True, 'independent_output_namespaces': True}
    original_symlink_to = Path.symlink_to
    def storage_reusing_symlink_to(self, target, target_is_directory=False):
        candidate = alias_cache.get(str(target))
        if candidate is not None:
            assert candidate.is_symlink() and os.readlink(candidate) == str(target)
            os.link(candidate, self, follow_symlinks=False)
            assert self.is_symlink() and os.readlink(self) == str(target)
            storage_stats['hardlinked_symlink_inodes'] += 1
        else:
            original_symlink_to(self, target, target_is_directory=target_is_directory)
            storage_stats['new_symlinks'] += 1
    Path.symlink_to = storage_reusing_symlink_to
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
    contexts = []
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
    assert len(aliases) == 0
    # Already accepted original grid/key/Core owners live in the original
    # Member namespace: fingerprint them, do not create duplicate aliases.
    old_owners = json.loads((ROOT / 'LEGACY_ACCEPTED_OWNERS.json').read_text())
    project = Path('/workspace/blue-member-build')
    for relative, module, source_sha in old_owners:
        folder = Path('/workspace/p1-complete-proof/20261125-p14-continuation') / relative
        receipt = folder / 'VALIDATION_RESULTS.json'
        result = json.loads(receipt.read_text())
        assert result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
        assert result['modules'][module] == source_sha
        records.append(driver.fingerprint(receipt))
        for relative_file, fp in result['source_plus_five_outputs'][module].items():
            actual = driver.fingerprint(project / relative_file)
            assert actual['bytes'] == fp['bytes'] and actual['sha256'] == fp['sha256']
            records.append(actual)
        for label in [module.split('.')[-1] + '-kernel.log', 'all-owned-types-axioms.log']:
            records.append(driver.fingerprint(folder / label))
    # Ordinary, unchanged DATA dependency, as permitted by the original
    # source-plus-five-output capture policy. No independent Data kernel or
    # full-owned acceptance is newly claimed or needlessly added here.
    manifest = Path('/workspace/p1-complete-proof/modern-p1-build/incremental-six-root-after-0007-repairs/ORDINARY_NORMAL_SOURCE_PLUS_FIVE_OUTPUTS.json')
    assert driver.fingerprint(manifest)['sha256'] == '38c538d0544c199e66c23d00a18b31485340312dcb60fd3fc415890c17b016d9'
    captured = json.loads(manifest.read_text())
    assert captured['unchanged_ordinary_dependencies_do_not_need_duplicate_individual_kernel_audits'] is True
    records.append(driver.fingerprint(manifest))
    data_modules = []
    for data_module in data_modules:
        data_inputs = captured['actual_Built_project_modules'][data_module]
        assert len(data_inputs) == 6
        for relative_file, fp in data_inputs.items():
            actual = driver.fingerprint(project / relative_file)
            assert actual['bytes'] == fp['bytes'] and actual['sha256'] == fp['sha256']
            records.append(actual)
    normal_receipt = Path('/workspace/p1-complete-proof/20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27/normal/ImbalancedChen.P1OriginalFifthAdoptedOwnerBank/NORMAL_PASS.json')
    assert driver.fingerprint(normal_receipt)['sha256'] == '3d3d32f615bd4eb96cd2497032012360477d0b871a7beb96bc5b0859a685569e'
    records.append(driver.fingerprint(normal_receipt))
    records.append(driver.fingerprint(ROOT / 'LEGACY_ACCEPTED_OWNERS.json'))
    records.append(driver.fingerprint(ROOT / 'PLAN.md'))
    records.append(driver.fingerprint(ROOT / 'SOURCE_REPAIR_PLAN_00002.json'))
    driver.save('DATA_ORDINARY_REUSE_SCOPE.json', {
        'modules': data_modules,
        'unchanged_source_plus_five_outputs_reused': True,
        'normal_or_kernel_repeated': False,
        'independent_Data_kernel_full_owned_not_claimed': True,
        'original_manifest_policy': 'unchanged_ordinary_dependencies_do_not_need_duplicate_individual_kernel_audits'})
    driver.save('REUSED_EXTRA_ALIAS_LINKS.json', aliases)
    records.append(driver.fingerprint(ROOT / 'SOURCE_GIT_COUPLING.json'))
    records.extend(seed_before)
    driver.save('COUPLED_IMPORTS_BEFORE.json', records)
    driver.main()
    Path.symlink_to = original_symlink_to
    driver.save('IMPORT_ALIAS_STORAGE.json', storage_stats)
    assert seed_before == [driver.fingerprint(p) for p in seed_manifests]
    assert records == [driver.fingerprint(Path(r['path'])) for r in records]
    assert all(Path(x['path']).is_symlink() and str(Path(x['path']).readlink()) == x['target'] for x in aliases)
    driver.save('COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'accepted_import_normal_or_kernel_commands': 0,
        'whole_P1_4_complete': False})
else:
    driver.main()
