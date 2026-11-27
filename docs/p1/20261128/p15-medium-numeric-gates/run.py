#!/usr/bin/env python3
"""Four existing numerical gate owners, reusing the frozen 78-module batch."""
from pathlib import Path
import importlib.util
import json
import shutil
import sys

ROOT = Path(__file__).resolve().parent
OLD = Path('/workspace/p1-complete-proof/20261127-p15-whole-atom-integration')
spec = importlib.util.spec_from_file_location('frozen_whole_atom_driver', OLD / 'run.py')
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
assert driver.sha(OLD / 'run.py') == '7a59df4ab1da60f9a4c25314c0ba9a89db2e6ed8eb1085f5de219c817a0d889e'
driver.ROOT = ROOT
driver.SELECTED = ROOT / 'selected-sources'
driver.LIB = ROOT / 'build/lib/lean'
driver.TARGETS = ['ImbalancedChen.P5OriginalOrdinaryWholeAtomMediumGates']
driver.__file__ = __file__
MODULES = [
    'ImbalancedChen.P5ZU1011SameRhoCompleteScaleSupport',
    'ImbalancedChen.P5ZU1011OriginalFifteenMediumNumericGates',
    'ImbalancedChen.P5OriginalPresievedMediumNumericGates',
    'ImbalancedChen.P5OriginalOrdinaryWholeAtomMediumGates']


def prepare():
    manifest = ROOT / 'SOURCE_SELECTION.json'
    if manifest.exists():
        return json.loads(manifest.read_text())
    previous = json.loads((OLD / 'SOURCE_SELECTION.json').read_text())
    assert json.loads((OLD / 'RESULT.json').read_text())['status'] == 'PASS_CONTEXT_INTEGRATION'
    assert len(previous['sources']) == 78
    records = [driver.fp(OLD / n) for n in
               ('run.py', 'SOURCE_SELECTION.json', 'RESULT.json', 'READONLY_VERIFICATION.json')]
    reused = list(previous['member_reused_boundary'])
    for row in previous['sources']:
        receipt = OLD / 'modules' / row['module'] / 'ACCEPTED.json'
        accepted = json.loads(receipt.read_text())
        assert accepted['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
        source = accepted['inputs']['source']
        assert driver.fp(source['path']) == source
        records.extend([source, driver.fp(receipt)])
        for obj in accepted['objects']:
            assert driver.fp(obj['path']) == obj
            records.append(obj)
        reused.append({'module': row['module'], 'object': accepted['objects'][0]})
    driver.save(ROOT / 'REUSED_78_INPUTS.json', records)
    rows = []
    available = {r['module'] for r in reused}
    for module in MODULES:
        relative = module.replace('.', '/') + '.lean'
        source = driver.WORK / relative
        imports = driver.re.findall(r'^import (\S+)', source.read_text(), driver.re.M)
        assert all(not m.startswith('ImbalancedChen.') or m in available or
                   (driver.PROJECT / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')).exists()
                   for m in imports), (module, imports)
        target = driver.SELECTED / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        rows.append({'module': module, 'selected_source': str(target),
                     'initial_selected_sha256': driver.sha(target), 'original_source': driver.fp(source),
                     'origin': 'Existing P1 numerical gate source; new Member-context acceptance',
                     'imports': imports})
        available.add(module)
    data = {'targets': driver.TARGETS, 'sources': rows, 'member_reused_boundary': reused,
            'work_head': '332025d52467814299265dc31aec9ea6879a008c',
            'reused_accepted_batch_commit': '6975ac45f21026f441a852fa52ab854d224ccf72',
            'old_module_normal_or_kernel_commands': 0, 'whole_P1_5_complete': False}
    driver.save(manifest, data)
    return data


original_worker = driver.worker


def worker():
    prepare()
    records = json.loads((ROOT / 'REUSED_78_INPUTS.json').read_text())
    assert all(driver.fp(r['path']) == r for r in records)
    oldlib = OLD / 'build/lib/lean/ImbalancedChen'
    namespace = driver.LIB / 'ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    for source in oldlib.rglob('*'):
        target = namespace / source.relative_to(oldlib)
        if source.is_dir() and not source.is_symlink():
            target.mkdir(parents=True, exist_ok=True)
        elif target.is_symlink():
            assert target.resolve() == source.resolve()
        else:
            assert not target.exists()
            target.symlink_to(source)
    original_worker()
    assert all(driver.fp(r['path']) == r for r in records)
    driver.save(ROOT / 'COUPLED_IMPORT_VALIDATION.json', {
        'status': 'PASS', 'inputs': records, 'old_module_normal_or_kernel_commands': 0,
        'whole_P1_5_complete': False})


driver.prepare = prepare
driver.worker = worker
snapshot = ROOT / 'EXECUTED_DRIVER.py'
if snapshot.exists():
    assert snapshot.read_bytes() == Path(__file__).read_bytes()
else:
    shutil.copyfile(__file__, snapshot)
driver.main()
