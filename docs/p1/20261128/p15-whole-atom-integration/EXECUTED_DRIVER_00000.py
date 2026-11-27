#!/usr/bin/env python3
"""Resume isolated Member-context integration without replaying accepted modules."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
WORK = Path('/workspace/p15-continue-20261127')
PROJECT = Path('/workspace/blue-member-build')
DONOR = Path('/workspace/p36-original-u5-20261125')
STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
STATE_SHA = '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
CORE = Path('/workspace/blue-build-tools/validate_member_roots_owned.py')
CORE_SHA = 'ed4dc724deb5e2cb28cbd461014c59bed52c373f6b18613f07cf663e456d8201'
SELECTED = ROOT / 'selected-sources'
LIB = ROOT / 'build/lib/lean'
TARGETS = ['ImbalancedChen.P5SelectedRealWholeAtomGroups',
           'ImbalancedChen.P5OriginalOrdinaryWholeAtomDelta']


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def fp(path):
    path = Path(path)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)}


def save(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def facets(module):
    obj = LIB / (module.replace('.', '/') + '.olean')
    assert obj.exists(), str(obj)
    return [fp(Path(str(obj) + suffix)) for suffix in ('', '.private', '.server')
            if Path(str(obj) + suffix).exists()]


def prepare():
    assert sha(STATE) == STATE_SHA and sha(CORE) == CORE_SHA
    manifest = ROOT / 'SOURCE_SELECTION.json'
    if manifest.exists():
        return json.loads(manifest.read_text())
    original_runner = DONOR / 'verification/p36/compile_p36_local.py'
    assert sha(original_runner) == 'be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709'
    runner = load_module('p15_source_import_reader', original_runner)
    donor_state = json.loads((DONOR / '.lake/p36-build/state.json').read_text())['modules']
    seen, rows, reused = set(), [], []
    cache = PROJECT / '.lake/build/lib/lean'

    def visit(module):
        if not module.startswith('ImbalancedChen.') or module in seen:
            return
        seen.add(module)
        relative = module.replace('.', '/')
        obj = cache / (relative + '.olean')
        if obj.exists():
            reused.append({'module': module, 'object': fp(obj)})
            return
        source = WORK / (relative + '.lean')
        origin = 'P1 existing source'
        record = donor_state.get(module)
        if record and record['exit_code'] == 0:
            candidate = Path(record['source'])
            assert candidate.is_relative_to(DONOR) and sha(candidate) == record['source_sha256']
            assert all(Path(p).exists() and sha(p) == digest for p, digest in record['objects'].items())
            committed = subprocess.check_output(['git', '-C', str(DONOR), 'show', 'HEAD:' + relative + '.lean'])
            assert hashlib.sha256(committed).hexdigest() == sha(candidate)
            source, origin = candidate, 'Committed P3.6 source/API repairs; no new donor credit'
        assert source.exists(), module
        text = source.read_text()
        imports = runner.parse_imports(text)
        for dep in imports:
            visit(dep)
        target = SELECTED / (relative + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        rows.append({'module': module, 'selected_source': str(target),
                     'initial_selected_sha256': sha(target), 'original_source': fp(source),
                     'origin': origin, 'imports': imports})

    for target in TARGETS:
        visit(target)
    data = {'targets': TARGETS, 'sources': rows, 'member_reused_boundary': reused,
            'work_head': subprocess.check_output(['git', '-C', str(WORK), 'rev-parse', 'HEAD'], text=True).strip(),
            'donor_head': subprocess.check_output(['git', '-C', str(DONOR), 'rev-parse', 'HEAD'], text=True).strip(),
            'source_only_donor_reuse': True, 'donor_binary_reuse_claimed': False,
            'whole_P1_5_complete': False}
    save(manifest, data)
    return data


def run(out, label, command, env):
    log = out / (label + '.log')
    assert not log.exists()
    receipt = {'argv': command, 'cwd': str(PROJECT), 'started_utc':
               datetime.datetime.now(datetime.timezone.utc).isoformat()}
    save(out / (label + '-started.json'), receipt)
    start = time.monotonic()
    with log.open('xb') as f:
        result = subprocess.run(command, cwd=PROJECT, env=env, stdout=f, stderr=subprocess.STDOUT)
    receipt.update(exit_code=result.returncode, wall_seconds=time.monotonic() - start, log=fp(log))
    save(out / (label + '-command.json'), receipt)
    if result.returncode:
        print(log.read_text()[-9000:], flush=True)
        raise RuntimeError(label + ' failed; exact attempt preserved at ' + str(out))
    return receipt


def worker():
    selection = prepare()
    baseline = PROJECT / '.lake/build/lib/lean/ImbalancedChen'
    namespace = LIB / 'ImbalancedChen'
    namespace.mkdir(parents=True, exist_ok=True)
    for source in baseline.rglob('*'):
        target = namespace / source.relative_to(baseline)
        if source.is_dir() and not source.is_symlink():
            target.mkdir(parents=True, exist_ok=True)
        elif target.is_symlink():
            assert target.resolve() == source.resolve()
        else:
            assert not target.exists(), str(target)
            target.symlink_to(source)
    before = [fp(STATE), fp(CORE)] + [r['object'] for r in selection['member_reused_boundary']]
    assert all(fp(row['path']) == row for row in before)
    core = load_module('p15_original_owned_core', CORE)
    env = os.environ.copy()
    env['LEAN_PATH'] = str(LIB) + os.pathsep + env.get('LEAN_PATH', '')
    passed = []
    for row in selection['sources']:
        module = row['module']
        source = Path(row['selected_source'])
        dependencies = {m: facets(m) for m in row['imports'] if m.startswith('ImbalancedChen.')}
        inputs = {'source': fp(source), 'dependencies': dependencies,
                  'guard_state_sha256': STATE_SHA, 'audit_core_sha256': CORE_SHA}
        folder = ROOT / 'modules' / module
        folder.mkdir(parents=True, exist_ok=True)
        accepted = folder / 'ACCEPTED.json'
        if accepted.exists():
            old = json.loads(accepted.read_text())
            assert old['inputs'] == inputs and old['objects'] == facets(module), module
            assert old['status'] == 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED'
            passed.append(old)
            print('REUSE_ACCEPTED ' + module, flush=True)
            continue
        attempts = list(folder.glob('attempt-*'))
        out = folder / ('attempt-' + str(len(attempts)).zfill(5))
        out.mkdir()
        save(out / 'INPUTS.json', inputs)
        shutil.copyfile(source, out / 'SELECTED_SOURCE.lean')
        relative = module.replace('.', '/')
        ir = ROOT / 'build/ir' / (relative + '.c')
        ir.parent.mkdir(parents=True, exist_ok=True)
        print('VERIFY ' + module, flush=True)
        normal = run(out, 'normal', ['lean', '--root=' + str(SELECTED),
            '-o', str(LIB / (relative + '.olean')), '-i', str(LIB / (relative + '.ilean')),
            '-c', str(ir), str(source)], env)
        objects = facets(module)
        kernel = run(out, 'kernel', ['leanchecker', '--verbose', module], env)
        replayed = [s.removeprefix('replaying ') for s in (out / 'kernel.log').read_text().splitlines()
                    if s.startswith('replaying ')]
        assert replayed == [module], replayed
        audit_source = out / 'OwnedAudit.lean'
        audit_source.write_text(core.make_audit_code([module]))
        audit = run(out, 'owned-audit', ['lean', '-Dpp.maxSteps=1000000', str(audit_source)], env)
        declarations, inventory, axioms = core.read_audit((out / 'owned-audit.log').read_text(),
                                                       [module], audit['exit_code'])
        for declaration in declarations:
            for value in [declaration['type'], declaration['type_expression'],
                          *declaration['universe_parameters']]:
                for _ in range(3):
                    value = re.sub(r'\\u([0-9a-fA-F]{4})|\\U([0-9a-fA-F]{8})',
                        lambda m: chr(int(m.group(1) or m.group(2), 16)), value)
                assert not any(t in value for t in ('sorryAx', '…', '⋯', '...'))
        assert fp(source) == inputs['source'] and facets(module) == objects
        assert all(fp(r['path']) == r for r in before)
        assert dependencies == {m: facets(m) for m in dependencies}
        save(out / 'OWNED_EXPORTS.json', declarations)
        save(out / 'OWNED_INVENTORY.json', inventory)
        result = {'status': 'PASS_ISOLATED_NORMAL_KERNEL_FULL_OWNED', 'module': module,
                  'inputs': inputs, 'objects': objects, 'normal': normal, 'kernel': kernel,
                  'audit': audit, 'owned': len(declarations), 'private': inventory['private_name_count'],
                  'axioms': axioms, 'source_origin': row['origin'],
                  'normal_method': 'guarded direct Lean; isolated Member-context integration',
                  'reused_donor_math_counted_as_new': False, 'whole_P1_5_complete': False}
        save(out / 'VALIDATION_RESULTS.json', result)
        save(accepted, result)
        passed.append(result)
        save(ROOT / 'PROGRESS.json', {'accepted_context_modules': len(passed),
             'selected_context_modules': len(selection['sources']), 'last_module': module,
             'whole_P1_5_complete': False})
        print('PASS ' + module + ' owned=' + str(len(declarations)), flush=True)
    save(ROOT / 'RESULT.json', {'status': 'PASS_CONTEXT_INTEGRATION',
        'modules': [r['module'] for r in passed], 'owned_context_total': sum(r['owned'] for r in passed),
        'donor_source_modules_revalidated': sum('P3.6' in r['source_origin'] for r in passed),
        'whole_P1_5_complete': False})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--worker', action='store_true')
    args = ap.parse_args()
    if args.worker:
        worker()
        return
    selection = prepare()
    print('SELECTED ' + str(len(selection['sources'])) + ' context modules', flush=True)
    lane = ROOT / ('LANE-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S') + '.json')
    command = ['python3', '/workspace/blue-build-tools/serialize_validation_lane.py',
        '--state', str(STATE), '--receipt', str(lane), 'python3',
        '/workspace/blue-build-tools/run_guarded.py', '--state', str(STATE),
        'lake', '--no-build', 'env', 'python3', '-B', str(Path(__file__).resolve()), '--worker']
    raise SystemExit(subprocess.run(command, cwd=PROJECT).returncode)


if __name__ == '__main__':
    main()
