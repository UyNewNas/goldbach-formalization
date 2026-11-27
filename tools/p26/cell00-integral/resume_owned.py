"""Resume full inventory checks using an unchanged, successful kernel replay."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import qualify_suppliers as qualifier

ROOT = Path(__file__).resolve().parents[3]
STAGE = qualifier.STAGE
PREFIX = qualifier.PREFIX
ALLOWED = qualifier.ALLOWED
PARENT_SHA = '1b0053ec50d6d186ee301ede5645e64fe1da12cc300deeb26ce55e524ed164b9'
pin = qualifier.pin


def validate_catalog(catalog):
    for info in catalog.values():
        for key in ['source', 'selected_object']:
            item = info[key]
            assert pin(Path(item['path'])) == item


def main():
    folder = STAGE / 'qualification'
    parent_path = folder / 'RUN-kernel-passed-owned-failed.json'
    parent_pin = pin(parent_path)
    assert parent_pin['sha256'] == PARENT_SHA
    parent = json.loads(parent_path.read_text())
    context_path = Path(parent['recovered_context']['path'])
    assert pin(context_path) == parent['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    catalog = parent['project_closure']
    assert len(catalog) == 907
    validate_catalog(catalog)
    for key in ['replay_source', 'verifier_source', 'incoming_modules', 'aggregate_build']:
        assert pin(Path(parent[key]['path'])) == parent[key]
    assert parent['runtime'] == context['runtime'] and parent['lean_path'] == context['lean_path']
    modules = json.loads(Path(parent['incoming_modules']['path']).read_text())
    assert len(modules) == len(set(modules)) == 468
    kernel, = [c for c in parent['commands'] if c['label'] == 'kernel-join']
    assert kernel['exit_code'] == 0 and kernel['stop_reason'] is None
    assert pin(Path(kernel['log']['path'])) == kernel['log']
    complete, progress, originals = [], [], []
    for line in Path(kernel['log']['path']).read_text().splitlines():
        if line.startswith('P26_CELL00_JOIN_COMPLETE '): complete.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL00_JOIN_PROGRESS '): progress.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL00_ORIGINAL_BYTES '): originals.append(json.loads(line.split(' ', 1)[1]))
    assert complete == [parent['kernel_join']]
    assert complete[0] == {'P2_6_complete': False, 'checked_declarations': 28059,
                           'kernel_replay_succeeded': True, 'new_external_modules': [], 'project_modules': 468}
    assert len(progress) == 468 and {p['module'] for p in progress} == set(modules)
    assert [p['completed_modules'] for p in progress] == list(range(1, 469))
    assert progress[-1]['checked_declarations'] == 28059
    assert originals == [parent['original_input_readback']]
    ledger = json.loads((ROOT / 'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json').read_text())
    raw_inputs = []
    for item in ledger['all_inputs']:
        if item['cell'] == 0:
            actual = pin(Path(item['resolved_actual_path']))
            assert all(actual[k] == item[k] for k in ['bytes', 'sha256'])
            raw_inputs.append(actual)
    assert len(raw_inputs) == 2
    number = 1
    while (folder / f'owned-retry-{number:03d}').exists(): number += 1
    retry = folder / f'owned-retry-{number:03d}'
    retry.mkdir()
    audit = ROOT / 'tools/p26/cell00-integral/OwnedSuppliersAudit.lean'
    state = dict(parent)
    state.update(status='running', formal_acceptance=False, commands=[kernel],
                 audit_source=pin(audit), verifier_source=pin(Path(__file__)),
                 kernel_verifier_source=parent['verifier_source'],
                 kernel_replay_reused=True, passed_kernel_parent=parent_pin,
                 previous_failed_owned_log=parent['commands'][-1]['log'],
                 raw_original_inputs_rechecked=raw_inputs)
    target = folder / 'RUN.json'

    def save(): target.write_text(json.dumps(state, indent=2) + '\n')

    flags = ['--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
             '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    expected_kernel = [str(qualifier.SYSROOT / 'bin/lean'), *flags, '--run',
                       parent['replay_source']['path'], parent['incoming_modules']['path']]
    assert kernel['argv'] == expected_kernel
    env = os.environ.copy()
    env['PATH'] = str(qualifier.SYSROOT / 'bin') + ':' + env.get('PATH', '')
    env['LEAN_PATH'] = parent['lean_path']
    env['LEAN_NUM_THREADS'] = '1'
    argv = [str(qualifier.SYSROOT / 'bin/lean'), *flags, str(audit)]
    log = retry / 'owned.log'
    record = {'label': 'owned', 'argv': argv, 'cwd': str(ROOT), 'started_at': time.time()}
    state['commands'].append(record)
    save()
    started = time.monotonic()
    with log.open('wb') as stream:
        result = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=1500)
    record.update(exit_code=result.returncode, seconds=time.monotonic() - started, log=pin(log))
    save()
    if result.returncode or 'sorryAx' in log.read_text():
        state['status'] = 'failed'
        save()
        print(log.read_text()[-7000:], flush=True)
        raise SystemExit(1)
    declarations, shared, inventories, counts = [], [], {}, {}
    for line in log.read_text().splitlines():
        if not line.startswith(PREFIX + '_'): continue
        tag, value = line.split(' ', 1)
        item = json.loads(value)
        if tag.endswith('_DECL') or tag.endswith('_SHARED'):
            assert not (item['unsafe'] or item['partial'] or item['axiom'])
            assert set(item['axioms']) <= ALLOWED and '⋯' not in item['type']
            if tag.endswith('_SHARED'):
                assert item['identical_metadata'] and item['proof_body_kernel_checked']
                assert item['canonical_module'] in catalog and item['canonical_module'] != item['module']
                shared.append(item)
            else: declarations.append(item)
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
    assert len(declarations) == len({x['name'] for x in declarations}) == 28059
    assert len(shared) == len({(x['module'], x['name']) for x in shared}) == 229
    assert sum(not x['identical_body'] for x in shared) == 1
    for module, count in counts.items():
        owned = sorted(x['name'] for x in declarations if x['module'] == module)
        aliases = sorted(x['name'] for x in shared if x['module'] == module)
        inv = inventories[module]
        assert count['count'] == len(owned) and owned == sorted(inv['environment'])
        assert count['shared_count'] == len(aliases) and aliases == sorted(inv['shared'])
        assert count['serialized_count'] == len(owned) + len(aliases)
    qualifier.validate(context)
    validate_catalog(catalog)
    assert pin(parent_path) == parent_pin and pin(audit) == state['audit_source']
    for key in ['replay_source', 'kernel_verifier_source', 'incoming_modules', 'aggregate_build']:
        assert pin(Path(state[key]['path'])) == state[key]
    assert pin(Path(kernel['log']['path'])) == kernel['log']
    for item in raw_inputs: assert pin(Path(item['path'])) == item
    (folder / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    (folder / 'shared-declarations.json').write_text(json.dumps(shared, indent=2) + '\n')
    state.update(status='succeeded', formal_acceptance=True, owned_modules=len(counts),
                 owned_declarations=len(declarations), shared_serialized_occurrences=len(shared),
                 different_shared_bodies_rechecked=1,
                 owned_counts={m: c['count'] for m, c in counts.items()}, allowed_axioms=sorted(ALLOWED))
    save()
    print(json.dumps({'status': 'succeeded', 'owned_modules': 468, 'owned_declarations': 28059,
                      'shared_bodies_kernel_checked': 229, 'kernel_replay_reused': True,
                      'P2_6_complete': False}), flush=True)


if __name__ == '__main__': main()
