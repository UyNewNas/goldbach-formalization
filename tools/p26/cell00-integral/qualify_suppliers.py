"""Qualify the recovered Cell00 objects in the current accepted context.

Only the unavailable aggregate is rebuilt. Existing finite normal receipts
are preserved; replay and inventory here qualify a different import join.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

import psutil

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell00-next-20261128')
SYSROOT = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
AGGREGATE = 'ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic'
PREFIX = 'P26_CELL00_SUPPLIER_AUDIT'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def validate(context):
    assert pin(Path(context['parent']['path'])) == context['parent']
    assert pin(Path(context['parent_base']['path'])) == context['parent_base']
    for info in context['project_closure'].values():
        for key in ['source', 'selected_object']:
            expected = info[key]
            assert pin(Path(expected['path'])) == expected
    for expected in context['native_artifacts']:
        assert pin(Path(expected['path'])) == expected
    for expected in context['runtime'].values():
        assert pin(Path(expected['path'])) == expected


def main():
    context_path = STAGE / 'RECOVERED_CONTEXT.json'
    context_pin = pin(context_path)
    context = json.loads(context_path.read_text())
    validate(context)
    modules_path = STAGE / 'INCOMING_MODULES.json'
    modules = json.loads(modules_path.read_text())
    assert len(modules) == len(set(modules)) == 468
    out = STAGE / 'qualification'
    out.mkdir(exist_ok=True)
    previous = out / 'RUN.json'
    if previous.exists():
        number = 1
        while (out / f'RUN-attempt-{number:03d}.json').exists():
            number += 1
        previous.rename(out / f'RUN-attempt-{number:03d}.json')
        for name in ['kernel-join.log', 'owned.log']:
            path = out / name
            if path.exists():
                path.rename(out / f'{path.stem}-attempt-{number:03d}{path.suffix}')
    env = os.environ.copy()
    env['PATH'] = str(SYSROOT / 'bin') + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = context['lean_path']
    env['LEAN_NUM_THREADS'] = '1'
    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    replay = ROOT / 'tools/p26/cell00-integral/ReplayJoin.lean'
    audit = ROOT / 'tools/p26/cell00-integral/OwnedSuppliersAudit.lean'
    state = {'schema': 'p26_cell00_current_supplier_join_qualification_v1',
             'status': 'running', 'formal_acceptance': False, 'P2_6_complete': False,
             'original_full_snapshot_verified': False,
             'scope': 'Exact original Cell00 finite suppliers and original floor bridge joined to the accepted current analytic context; no new cell integral endpoint.',
             'recovered_context': context_pin, 'incoming_modules': pin(modules_path),
             'runtime': context['runtime'], 'lean_path': env['LEAN_PATH'],
             'replay_source': pin(replay), 'audit_source': pin(audit),
             'verifier_source': pin(Path(__file__)), 'commands': []}

    def save():
        previous.write_text(json.dumps(state, indent=2) + '\n')

    def run(label, argv, timeout):
        log = out / (label + '.log')
        record = {'label': label, 'argv': list(map(str, argv)), 'cwd': str(ROOT),
                  'started_at': time.time()}
        state['commands'].append(record)
        save()
        started = time.monotonic()
        peak, cpu, reason = 0, 0.0, None
        with log.open('wb') as stream:
            process = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            root = psutil.Process(process.pid)
            while process.poll() is None:
                rss, usage = 0, 0.0
                try:
                    processes = [root] + root.children(recursive=True)
                except psutil.Error:
                    processes = []
                for child in processes:
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
        text = log.read_text()
        if code or reason or 'sorryAx' in text:
            state['status'] = 'failed'
            save()
            print(text[-8000:], flush=True)
            raise SystemExit(1)
        return record

    source = ROOT / (AGGREGATE.replace('.', '/') + '.lean')
    obj = STAGE / 'objects' / (AGGREGATE.replace('.', '/') + '.olean')
    receipt = STAGE / 'AGGREGATE_BUILD.json'
    expected = {'source': pin(source), 'runtime': context['runtime']['lean'],
                'lean_path': env['LEAN_PATH'], 'flags': flags}
    if receipt.exists():
        old = json.loads(receipt.read_text())
        assert all(old[k] == value for k, value in expected.items())
        assert old['command']['exit_code'] == 0 and pin(obj) == old['object']
        state['reused_current_aggregate_build'] = pin(receipt)
    else:
        record = run('aggregate-normal', [SYSROOT / 'bin/lean', *flags,
            '-o', obj, source.relative_to(ROOT)], timeout=600)
        assert pin(source) == expected['source']
        receipt.write_text(json.dumps({**expected, 'object': pin(obj), 'command': record,
            'reason': 'Original aggregate object not located in bounded P1/P2 workspace scans; original 56 suppliers retained.'}, indent=2) + '\n')
    catalog = dict(context['project_closure'])
    catalog[AGGREGATE] = {'source': pin(source), 'selected_object': pin(obj),
                          'origin': 'current-rebuilt-missing-aggregate'}
    assert len(catalog) == 907
    state['project_closure'] = catalog
    state['aggregate_build'] = pin(receipt)
    save()
    run('kernel-join', [SYSROOT / 'bin/lean', *flags, '--run', replay, modules_path], timeout=2700)
    completed = []
    original_bytes = []
    for line in (out / 'kernel-join.log').read_text().splitlines():
        if line.startswith('P26_CELL00_JOIN_COMPLETE '):
            completed.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL00_ORIGINAL_BYTES '):
            original_bytes.append(json.loads(line.split(' ', 1)[1]))
    assert len(completed) == len(original_bytes) == 1
    assert completed[0]['project_modules'] == 468 and completed[0]['kernel_replay_succeeded']
    assert original_bytes[0] == {'geometry_bytes': 195134, 'moment_bytes': 28999,
                                 'embedded_original_bytes_match': True}
    state.update(kernel_join=completed[0], original_input_readback=original_bytes[0])
    save()
    run('owned', [SYSROOT / 'bin/lean', *flags, audit], timeout=900)
    declarations, counts, inventories = [], {}, {}
    with (out / 'owned.log').open() as stream:
        for line in stream:
            if not line.startswith(PREFIX + '_'):
                continue
            tag, raw = line.split(' ', 1)
            item = json.loads(raw)
            if tag.endswith('_INVENTORY'):
                assert item['module'] not in inventories
                assert sorted(item['serialized']) == sorted(item['environment'])
                inventories[item['module']] = item
            elif tag.endswith('_DECL'):
                assert not (item['unsafe'] or item['partial'] or item['axiom'])
                assert set(item['axioms']) <= ALLOWED and '⋯' not in item['type']
                declarations.append(item)
            elif tag.endswith('_COMPLETE'):
                assert item['module'] not in counts
                counts[item['module']] = item['count']
    assert set(counts) == set(inventories) == set(modules)
    assert len({x['name'] for x in declarations}) == len(declarations)
    for module, count in counts.items():
        names = sorted(x['name'] for x in declarations if x['module'] == module)
        assert count == len(names) and names == sorted(inventories[module]['serialized'])
    (out / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    validate(context)
    for info in catalog.values():
        for key in ['source', 'selected_object']:
            item = info[key]
            assert pin(Path(item['path'])) == item
    assert pin(context_path) == context_pin
    assert pin(replay) == state['replay_source'] and pin(audit) == state['audit_source']
    state.update(status='succeeded', formal_acceptance=True,
                 owned_modules=len(counts), owned_declarations=len(declarations),
                 owned_counts=counts, allowed_axioms=sorted(ALLOWED))
    save()
    print(json.dumps({'status': 'succeeded', 'owned_modules': len(counts),
                      'owned_declarations': len(declarations), 'P2_6_complete': False}), flush=True)


if __name__ == '__main__':
    main()
