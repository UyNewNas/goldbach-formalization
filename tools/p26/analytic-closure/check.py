"""Fresh verification of the current Saving19 higher-moment source context.

Normal compilation, complete owned-declaration auditing, ordinary kernel
replay, and from-empty-environment replay are distinct recorded operations.
The incomplete historical full-snapshot certificate is never promoted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

import psutil

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-analytic-closure-20261127')
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
AUDIT = ROOT / 'tools/p26/analytic-closure/OwnedAudit.lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def main():
    normal = json.loads((STAGE / 'RUN.json').read_text())
    assert normal['status'] == 'normal_build_succeeded_not_formally_accepted'
    assert len(normal['commands']) == len(normal['nodes']) == 228
    objects = STAGE / 'objects'
    for command in normal['commands']:
        assert command['exit_code'] == 0
        assert pin(Path(command['source']['path'])) == command['source']
        assert pin(Path(command['object']['path'])) == command['object']
    scopes = re.findall(r'`(ImbalancedChen\.[A-Za-z0-9_]+)', AUDIT.read_text())
    assert len(scopes) == len(set(scopes)) == 21
    env = os.environ.copy()
    env['PATH'] = str(SYSROOT / 'bin') + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = normal['lean_path']
    env['LEAN_NUM_THREADS'] = '1'
    out = STAGE / 'verification'
    out.mkdir(exist_ok=True)
    state = {
        'schema': 'p26_higher_moment_fresh_verification_v1',
        'status': 'running', 'formal_acceptance': False, 'P2_6_complete': False,
        'original_full_snapshot_verified': False,
        'scope': 'Original Saving19 analytic source, actual simplex moments, degree-six moment formula and unchanged prefix evaluator identity. No original row floor, complete 13-family certificate or global integral endpoint acceptance.',
        'cwd': str(ROOT), 'lean_path': env['LEAN_PATH'], 'scopes': scopes,
        'normal_build': pin(STAGE / 'RUN.json'), 'audit_source': pin(AUDIT),
        'verifier_source': pin(Path(__file__)),
        'runtime': {name: pin(SYSROOT / 'bin' / name)
                    for name in ['lean', 'leanchecker']},
        'commands': [],
    }

    def save():
        (out / 'RUN.json').write_text(json.dumps(state, indent=2) + '\n')

    def run(label, argv, timeout=900):
        record = {'label': label, 'argv': list(map(str, argv)),
                  'cwd': str(ROOT), 'started_at': time.time()}
        state['commands'].append(record)
        save()
        log = out / (label + '.log')
        started = time.monotonic()
        peak, cpu, reason = 0, 0.0, None
        with log.open('wb') as stream:
            proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            root = psutil.Process(proc.pid)
            while proc.poll() is None:
                rss, sampled_cpu = 0, 0.0
                try:
                    processes = [root] + root.children(recursive=True)
                except psutil.Error:
                    processes = []
                for process in processes:
                    try:
                        rss += process.memory_info().rss
                        times = process.cpu_times()
                        sampled_cpu += times.user + times.system
                    except psutil.Error:
                        pass
                peak, cpu = max(peak, rss), max(cpu, sampled_cpu)
                if rss > 12 * 1024**3:
                    reason = 'sampled_memory_limit_12_GiB'
                if time.monotonic() - started > timeout:
                    reason = 'timeout'
                if reason:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(0.1)
            exit_code = proc.wait()
        record.update(exit_code=exit_code, seconds=time.monotonic() - started,
                      sampled_peak_tree_rss_bytes=peak, sampled_cpu_seconds=cpu,
                      stop_reason=reason, log=pin(log))
        save()
        print(label, 'exit=' + str(exit_code), flush=True)
        if exit_code or reason or 'sorryAx' in log.read_text():
            state['status'] = 'failed'
            save()
            print(log.read_text()[-8000:], flush=True)
            raise SystemExit(1)

    run('external-inputs-before', [sys.executable, '-B',
        ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py'])
    external = json.loads((STAGE / 'EXTERNAL_INPUTS_READBACK.json').read_text())
    assert external['status'] == 'matched' and not external['problems']
    state['external_inputs_before'] = external
    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    run('owned', [SYSROOT / 'bin/lean', *flags, AUDIT])
    declarations, completed, inventories, imports = [], {}, {}, None
    for line in (out / 'owned.log').read_text().splitlines():
        if not line.startswith('P26_ANALYTIC_AUDIT_'):
            continue
        tag, payload = line.split(' ', 1)
        item = json.loads(payload)
        if tag.endswith('_IMPORTS'):
            assert imports is None
            imports = item
        elif tag.endswith('_INVENTORY'):
            module = item['module']
            assert module not in inventories
            assert sorted(item['serialized']) == sorted(item['environment'])
            inventories[module] = item
        elif tag.endswith('_DECL'):
            assert not (item['unsafe'] or item['partial'] or item['axiom'])
            assert set(item['axioms']) <= ALLOWED
            assert '⋯' not in item['type']
            declarations.append(item)
        elif tag.endswith('_COMPLETE'):
            assert item['module'] not in completed
            completed[item['module']] = item['count']
    assert set(completed) == set(inventories) == set(scopes)
    assert len({item['name'] for item in declarations}) == len(declarations)
    for module, count in completed.items():
        actual = sorted(x['name'] for x in declarations if x['module'] == module)
        assert len(actual) == count and actual == sorted(inventories[module]['serialized'])
    assert {m for m in imports if m.startswith('ImbalancedChen.')} == set(normal['nodes'])
    native = json.loads((STAGE / 'SELECTED_NATIVE_INPUTS.json').read_text())
    native_roots = {name.split('.')[0] for name in native['nodes']}
    actual_native = {name for name in imports if name.split('.')[0] in native_roots}
    assert actual_native <= set(native['nodes'])
    standard_roots = {'Init', 'Lean', 'Std', 'Lake', 'Mathlib', 'Batteries', 'Qq',
                      'Aesop', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient',
                      'Plausible', 'Cli', 'ImbalancedChen'}
    assert not {name for name in imports
                if name.split('.')[0] not in standard_roots | native_roots}
    (out / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    state.update(owned_counts=completed, owned_declaration_count=len(declarations),
                 imported_module_count=len(imports),
                 actual_native_import_count=len(actual_native),
                 actual_native_imports=sorted(actual_native))
    save()
    for module in scopes:
        run('kernel-' + module, [SYSROOT / 'bin/leanchecker', '--verbose', module])
    run('kernel-from-empty', [SYSROOT / 'bin/leanchecker', '--verbose', '--fresh',
                              normal['target']], timeout=2700)
    run('external-inputs-after', [sys.executable, '-B',
        ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py'])
    state['external_inputs_after'] = json.loads((STAGE / 'EXTERNAL_INPUTS_READBACK.json').read_text())
    assert state['external_inputs_after']['status'] == 'matched'
    assert not state['external_inputs_after']['problems']
    assert pin(STAGE / 'RUN.json') == state['normal_build']
    assert pin(AUDIT) == state['audit_source']
    for command in normal['commands']:
        assert pin(Path(command['source']['path'])) == command['source']
        assert pin(Path(command['object']['path'])) == command['object']
    state.update(status='succeeded', formal_acceptance=True,
                 fresh_kernel_import_replay_succeeded=True)
    save()
    print('Verified owned declarations:', len(declarations), flush=True)


if __name__ == '__main__':
    main()
