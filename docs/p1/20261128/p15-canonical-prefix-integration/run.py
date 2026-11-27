#!/usr/bin/env python3
"""Three existing canonical-prefix owners, reusing the frozen 78-module batch."""
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
driver.TARGETS = ['ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement']
driver.__file__ = __file__
MODULES = ['ImbalancedChen.P2CanonicalWallFullResidualPayment',
           'ImbalancedChen.P4AUpperTaggedMixedWallPayment',
           'ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement']


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
        origin = 'Existing P1/P4A source; new Member-context acceptance'
        if module == 'ImbalancedChen.P2CanonicalWallFullResidualPayment':
            donor = driver.DONOR
            assert driver.subprocess.check_output(['git', '-C', str(donor), 'rev-parse', 'HEAD'], text=True).strip() == '8495b3b274a046060faf2ce9020b2588665634c0'
            original_runner = donor / 'verification/p36/compile_p36_local.py'
            assert driver.sha(original_runner) == 'be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709'
            state = json.loads((donor / '.lake/p36-build/state.json').read_text())['modules']
            record = state[module]
            assert record['exit_code'] == 0
            source = Path(record['source'])
            assert source.is_relative_to(donor) and driver.sha(source) == record['source_sha256']
            assert driver.hashlib.sha256(driver.subprocess.check_output(['git', '-C', str(donor), 'show', 'HEAD:' + relative])).hexdigest() == driver.sha(source)
            assert all(driver.sha(p) == digest for p, digest in record['objects'].items())
            (ROOT / 'provenance').mkdir(exist_ok=True)
            driver.save(ROOT / 'provenance/DONOR_ORIGINAL_RECORDS.json', {
                'module': module, 'source_commit': '8495b3b274a046060faf2ce9020b2588665634c0',
                'original_record': record, 'original_compiler': driver.fp(original_runner),
                'objects': [driver.fp(p) for p in record['objects']],
                'source': driver.fp(source), 'donor_binary_transplant': False,
                'new_donor_math_credit': 0})
            origin = 'Committed P3.6 source/API repairs; no new donor credit'
        imports = driver.re.findall(r'^import (\S+)', source.read_text(), driver.re.M)
        assert all(not m.startswith('ImbalancedChen.') or m in available or
                   (driver.PROJECT / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')).exists()
                   for m in imports), (module, imports)
        target = driver.SELECTED / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        rows.append({'module': module, 'selected_source': str(target),
                     'initial_selected_sha256': driver.sha(target), 'original_source': driver.fp(source),
                     'origin': origin,
                     'imports': imports})
        available.add(module)
    data = {'targets': driver.TARGETS, 'sources': rows, 'member_reused_boundary': reused,
            'work_head': '9d546f3db80bc8c5669a6de21d685b5c1d98c209',
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
