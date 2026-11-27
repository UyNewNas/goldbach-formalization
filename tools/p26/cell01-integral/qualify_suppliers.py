"""Kernel replay and complete serialized inventory audit of recovered Cell01."""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

import psutil

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
STAGE = Path('/workspace/p26-cell01-next-20261128')
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
PREFIX = 'P26_CELL01_SUPPLIER_AUDIT'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def validate(context):
    entries = [context['accepted_parent'], context['transport_archive'],
               context['transport_manifest'], context['old_row000_recovery'],
               context['restorer_source']]
    entries += context['native_artifacts'] + list(context['runtime'].values())
    for info in context['project_closure'].values():
        entries.extend([info['source'], info['selected_object']])
    for item in entries:
        assert pin(Path(item['path'])) == item, item['path']


def main():
    path = STAGE / 'RECOVERED_BASE_CONTEXT.json'
    context_pin, context = pin(path), json.loads(path.read_text())
    validate(context)
    modules_path = STAGE / 'INCOMING_BASE_MODULES.json'
    modules = json.loads(modules_path.read_text())
    assert modules == context['incoming_modules'] and len(modules) == len(set(modules)) == 407
    out = STAGE / 'qualification'
    out.mkdir(exist_ok=True)
    target = out / 'RUN.json'
    assert not target.exists(), 'Keep prior attempts immutable; do not repeat a passed kernel replay.'
    replay, audit = HERE / 'ReplayJoin.lean', HERE / 'OwnedSuppliersAudit.lean'
    state = {'schema': 'p26_cell01_current_supplier_qualification_v1', 'status': 'running',
             'formal_acceptance': False, 'P2_6_complete': False,
             'original_full_snapshot_verified': False,
             'scope': '407 recovered exact Cell01 supplier modules joined to accepted current930; no Cell01 integral endpoint.',
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
        if line.startswith('P26_CELL01_JOIN_COMPLETE '): complete.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL01_JOIN_PROGRESS '): progress.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL01_ORIGINAL_BYTES '): originals.append(json.loads(line.split(' ', 1)[1]))
    assert len(complete) == 1 and complete[0]['kernel_replay_succeeded']
    assert complete[0]['project_modules'] == 407 and complete[0]['new_external_modules'] == []
    assert len(progress) == 407 and {x['module'] for x in progress} == set(modules)
    assert [x['completed_modules'] for x in progress] == list(range(1, 408))
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
    assert len(shared) == len({(x['module'], x['name']) for x in shared})
    for module, count in counts.items():
        owned = sorted(x['name'] for x in declarations if x['module'] == module)
        aliases = sorted(x['name'] for x in shared if x['module'] == module)
        inv = inventories[module]
        assert count['count'] == len(owned) and owned == sorted(inv['environment'])
        assert count['shared_count'] == len(aliases) and aliases == sorted(inv['shared'])
        assert count['serialized_count'] == len(owned) + len(aliases)
    validate(context)
    assert pin(path) == context_pin
    for key in ['incoming_modules', 'replay_source', 'audit_source', 'verifier_source']:
        assert pin(Path(state[key]['path'])) == state[key]
    (out / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    (out / 'shared-declarations.json').write_text(json.dumps(shared, indent=2) + '\n')
    state.update(status='succeeded', formal_acceptance=True, owned_modules=407,
        owned_declarations=len(declarations), shared_serialized_occurrences=len(shared),
        different_shared_bodies_rechecked=sum(not x['identical_body'] for x in shared),
        owned_counts={m: c['count'] for m, c in counts.items()}, allowed_axioms=sorted(ALLOWED))
    save()
    print(json.dumps({k: state[k] for k in ['status', 'owned_modules', 'owned_declarations',
        'shared_serialized_occurrences', 'P2_6_complete']}), flush=True)


if __name__ == '__main__':
    main()
