"""Join completed original Cell01 finite objects without repeating normal builds."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import time

import psutil

import prepare_finite_join as preparer

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
EXPECTED_PARENT_SHA = 'd20aa91e469b0ad05e1d80297965b2d7838fe35e7af59471f7c63804880702b9'
EQUATIONS = {'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure.' + n + '.eq_1'
             for n in ['factorFloorQ80', 'factorLowerQ80', 'roundDownQ', 'totalLowerQ80']}
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
PREFIX = 'P26_CELL01_FINITE_AUDIT'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def validate(context):
    assert context['accepted_parent']['sha256'] == EXPECTED_PARENT_SHA
    entries = [context['accepted_parent'], context['preparer_source']]
    entries += context['selected_inputs'] + context['native_artifacts'] + list(context['runtime'].values())
    for info in context['project_closure'].values():
        entries.extend([info['source'], info['selected_object']])
    seen = {}
    for item in entries:
        key = (str(Path(item['path']).resolve()), item['bytes'], item['sha256'])
        if key not in seen:
            actual = pin(Path(item['path']))
            assert all(actual[k] == item[k] for k in ['bytes', 'sha256']), item['path']
            seen[key] = True


def main(stage, rows):
    assert pin(preparer.PARENT)['sha256'] == EXPECTED_PARENT_SHA
    out = stage / 'qualification'
    target = out / 'RUN.json'
    assert not target.exists(), 'Keep prior attempts immutable; do not repeat a passed kernel replay.'
    path = preparer.prepare(rows, stage)
    count = len(rows)

    context_pin, context = pin(path), json.loads(path.read_text())
    validate(context)
    modules_path = stage / 'INCOMING_MODULES.json'
    modules = json.loads(modules_path.read_text())
    assert modules == context['incoming_modules'] and len(modules) == len(set(modules)) == count
    out.mkdir(exist_ok=True)
    replay, audit = stage / 'ReplayJoin.lean', stage / 'OwnedAudit.lean'
    state = {'schema': 'p26_cell01_current_finite_join_qualification_v1', 'status': 'running',
             'formal_acceptance': False, 'P2_6_complete': False,
             'original_full_snapshot_verified': False,
             'scope': f'{count} exact finite owners joined to accepted current1341, with all shared generated equation bodies checked; original floor blocks and Cell01 integral remain separate.',
             'recovered_context': context_pin, 'incoming_modules': pin(modules_path),
             'project_closure': context['project_closure'], 'runtime': context['runtime'],
             'lean_path': context['lean_path'], 'replay_source': pin(replay),
             'audit_source': pin(audit), 'verifier_source': pin(Path(__file__)), 'commands': []}

    def save():
        target.write_text(json.dumps(state, indent=2) + '\n')

    env = os.environ.copy()
    env.pop('CONTROL_PLANE_API_KEY', None)
    env['PATH'] = str(SYSROOT / 'bin') + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = context['lean_path']
    env['LEAN_NUM_THREADS'] = '1'
    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']

    def run(label, args, timeout):
        log = out / (label + '.log')
        record = {'label': label, 'argv': [str(a) for a in args], 'cwd': str(ROOT), 'started_at': time.time()}
        state['commands'].append(record)
        save()
        started, peak, cpu, reason = time.monotonic(), 0, 0.0, None
        with log.open('wb') as stream:
            process = subprocess.Popen(record['argv'], cwd=ROOT, env=env,
                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            root = psutil.Process(process.pid)
            while process.poll() is None:
                rss, usage = 0, 0.0
                try:
                    children = [root] + root.children(recursive=True)
                except psutil.Error:
                    children = []
                for child in children:
                    try:
                        rss += child.memory_info().rss
                        times = child.cpu_times()
                        usage += times.user + times.system
                    except psutil.Error:
                        pass
                peak, cpu = max(peak, rss), max(cpu, usage)
                if rss > 12 * 1024**3:
                    reason = 'sampled_memory_limit_12_GiB'
                if time.monotonic() - started > timeout:
                    reason = 'timeout'
                if reason:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(0.1)
            code = process.wait()
        record.update(exit_code=code, seconds=time.monotonic() - started,
            sampled_peak_tree_rss_bytes=peak, sampled_cpu_seconds=cpu,
            stop_reason=reason, log=pin(log))
        save()
        print(label, 'exit=' + str(code), flush=True)
        if code or reason or 'sorryAx' in log.read_text():
            state['status'] = 'failed'
            save()
            print(log.read_text()[-6000:], flush=True)
            raise SystemExit(1)

    run('kernel-join', [SYSROOT / 'bin/lean', *flags, '--run', replay, modules_path], 2200)
    complete, progress, originals = [], [], []
    for line in (out / 'kernel-join.log').read_text().splitlines():
        if line.startswith('P26_CELL01_FINITE_JOIN_COMPLETE '): complete.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL01_FINITE_JOIN_PROGRESS '): progress.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL01_FINITE_ORIGINAL_BYTES '): originals.append(json.loads(line.split(' ', 1)[1]))
    assert len(complete) == 1 and complete[0]['kernel_replay_succeeded']
    assert complete[0]['project_modules'] == count and complete[0]['new_external_modules'] == []
    assert complete[0]['checked_declarations'] == 288 * count
    assert len(progress) == count and {x['module'] for x in progress} == set(modules)
    assert [x['completed_modules'] for x in progress] == list(range(1, count + 1))
    assert progress[-1]['checked_declarations'] == complete[0]['checked_declarations']
    assert originals == [{'geometry_bytes': 470901, 'moment_bytes': 75094, 'embedded_original_bytes_match': True}]
    state.update(kernel_join=complete[0], original_input_readback=originals[0])
    save()
    # This immutable checkpoint permits audit-only continuation after interruption.
    (out / 'PASSED_KERNEL_CHECKPOINT.json').write_text(json.dumps(state, indent=2) + '\n')
    run('owned', [SYSROOT / 'bin/lean', *flags, audit], 1000)
    declarations, shared, inventories, counts = [], [], {}, {}
    for line in (out / 'owned.log').read_text().splitlines():
        if not line.startswith(PREFIX + '_'): continue
        tag, raw = line.split(' ', 1)
        item = json.loads(raw)
        if tag.endswith('_DECL') or tag.endswith('_SHARED'):
            assert not (item['unsafe'] or item['partial'] or item['axiom'])
            assert set(item['axioms']) <= ALLOWED and '⋯' not in item['type']
            if tag.endswith('_SHARED'):
                assert item['identical_metadata'] and item['proof_body_kernel_checked']
                assert item['canonical_module'] in context['project_closure']
                assert item['canonical_module'] not in modules
                assert item['name'] in EQUATIONS
                assert item['canonical_module'] != item['module']
                shared.append(item)
            else:
                declarations.append(item)
        elif tag.endswith('_INVENTORY'):
            module = item['module']
            assert module not in inventories
            assert sorted(item['serialized']) == sorted(item['environment'] + item['shared'])
            assert len(item['serialized']) == len(set(item['serialized']))
            assert not set(item['environment']) & set(item['shared'])
            inventories[module] = item
        elif tag.endswith('_COMPLETE'):
            assert item['module'] not in counts
            counts[item['module']] = item
    assert set(counts) == set(inventories) == set(modules)
    assert len(declarations) == len({x['name'] for x in declarations}) == complete[0]['checked_declarations']
    assert len(shared) == len({(x['module'], x['name']) for x in shared}) == 4 * count
    for module, count in counts.items():
        owned = sorted(x['name'] for x in declarations if x['module'] == module)
        aliases = sorted(x['name'] for x in shared if x['module'] == module)
        inv = inventories[module]
        assert count['count'] == len(owned) and owned == sorted(inv['environment'])
        assert count['shared_count'] == len(aliases) and aliases == sorted(inv['shared'])
        assert count['serialized_count'] == len(owned) + len(aliases) == 292
        assert len(owned) == 288 and set(aliases) == EQUATIONS
    validate(context)
    assert pin(path) == context_pin
    for key in ['incoming_modules', 'replay_source', 'audit_source', 'verifier_source']:
        assert pin(Path(state[key]['path'])) == state[key]
    (out / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    (out / 'shared-declarations.json').write_text(json.dumps(shared, indent=2) + '\n')
    external_path = ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py'
    external_pin = pin(external_path)
    assert external_pin == context['external_verifier_source']
    spec = importlib.util.spec_from_file_location('finite_join_external', external_path)
    external = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(external)
    external.OUT = out / 'FINAL_EXTERNAL_READBACK.json'
    external.main()
    report = json.loads(external.OUT.read_text())
    assert report['status'] == 'matched' and report['unique_physical_files_hashed'] == 54309
    assert report['problems'] == [] and report['plan'] == context['external_plan']
    assert pin(external_path) == external_pin
    validate(context)
    assert pin(path) == context_pin
    for key in ['incoming_modules', 'replay_source', 'audit_source', 'verifier_source']:
        assert pin(Path(state[key]['path'])) == state[key]
    state['final_external_readback'] = pin(external.OUT)
    state['external_verifier_source'] = external_pin
    state.update(status='succeeded', formal_acceptance=True, owned_modules=len(modules),
        owned_declarations=len(declarations), shared_serialized_occurrences=len(shared),
        different_shared_bodies_rechecked=sum(not x['identical_body'] for x in shared),
        owned_counts={m: c['count'] for m, c in counts.items()}, allowed_axioms=sorted(ALLOWED))
    save()
    successor = {'formal_acceptance': True, 'P2_6_complete': False, 'original_full_snapshot_verified': False,
        'scope': f'Accepted current1341 plus{len(modules)} exact finite row owners; no all-row original floor or cell integral endpoint.',
        'accepted_parent': context['accepted_parent'], 'qualification_parent': pin(target),
        'project_closure': context['project_closure'], 'native_artifacts': context['native_artifacts'],
        'runtime': context['runtime'], 'lean_path': context['lean_path']}
    (stage / 'CURRENT_ACCEPTED_CONTEXT.json').write_text(json.dumps(successor, indent=2) + '\n')
    print(json.dumps({k: state[k] for k in ['status', 'owned_modules', 'owned_declarations',
        'shared_serialized_occurrences', 'P2_6_complete']}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', required=True, type=Path)
    parser.add_argument('--rows', nargs='+', type=int, default=list(range(1, 144)))
    args = parser.parse_args()
    main(args.stage, args.rows)
