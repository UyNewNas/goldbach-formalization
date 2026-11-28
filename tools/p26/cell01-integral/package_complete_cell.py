"""Package Cell01 only after the entire checked original chain succeeds."""
import io
import json
from pathlib import Path
import shutil
import tarfile

import prepare_finite_join as preparer
import qualify_finite_join as qualifier
import verify_after_finite as phases

ROOT = Path(__file__).resolve().parents[3]
JOIN = phases.JOIN
OUT = ROOT / 'docs/verification/20261128-p26-cell01-integral'


def load_run(path):
    run = json.loads(path.read_text())
    assert run['status'] == 'succeeded' and run['formal_acceptance']
    for command in run['commands']:
        assert command['exit_code'] == 0
        preparer.check(command['log'])
    for key in ['verifier_source', 'wrapper_source', 'audit_source', 'replay_source',
                'incoming_modules', 'external_verifier_source', 'final_external_readback']:
        if key in run: preparer.check(run[key])
    if 'final_external_readback' in run:
        report = json.loads(Path(run['final_external_readback']['path']).read_text())
        assert report['status'] == 'matched' and report['problems'] == []
        assert report['unique_physical_files_hashed'] == 54309
        preparer.check(report['plan'])
    return run


def main():
    assert not (OUT / 'CAPSULE.json').exists(), 'Preserve an existing completed package.'
    for path in [JOIN / 'qualification/RUN.json', *[
            JOIN / ('verification-' + phase) / 'RUN.json' for phase in phases.ORDER]]:
        status = json.loads(path.read_text())
        assert status['status'] == 'succeeded' and status['formal_acceptance'], str(path)
    context_path = JOIN / 'JOIN_INPUTS.json'
    context_pin = preparer.pin(context_path)
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    join_path = JOIN / 'qualification/RUN.json'
    join_pin, joined = preparer.pin(join_path), load_run(join_path)
    assert joined['recovered_context'] == preparer.pin(context_path)
    assert joined['owned_modules'] == 143 and joined['owned_declarations'] == 41184
    assert joined['shared_serialized_occurrences'] == 572
    assert joined['project_closure'] == context['project_closure']
    expected = dict(context['project_closure'])
    assert len(expected) == 1484
    members = {'JOIN_INPUTS.json': context_path,
               'INCOMING_MODULES.json': JOIN / 'INCOMING_MODULES.json',
               'programs/ReplayJoin.lean': JOIN / 'ReplayJoin.lean',
               'programs/OwnedAudit.lean': JOIN / 'OwnedAudit.lean'}
    failed_folder = JOIN / 'attempts/physical-001'
    failed_manifest_path = failed_folder / 'PRESERVED_FAILED_ATTEMPT.json'
    failed_manifest = json.loads(failed_manifest_path.read_text())
    assert failed_manifest['status'] == 'preserved_failed_normal_attempt'
    assert not failed_manifest['formal_acceptance']
    assert failed_manifest['no_successful_compile_step_repeated']
    for item in failed_manifest['preserved']:
        preparer.check(item['preserved'])
        if 'original' in item:
            assert all(item['original'][key] == item['preserved'][key]
                       for key in ['bytes', 'sha256'])
    failed_run_path = failed_folder / 'verification-physical/RUN.json'
    failed_run = json.loads(failed_run_path.read_text())
    assert failed_run['status'] == 'failed' and len(failed_run['commands']) == 1
    assert failed_run['commands'][0]['exit_code'] == 1
    assert failed_run['commands'][0]['label'].endswith('-normal')
    for command in failed_run['commands']:
        log = failed_run_path.parent / Path(command['log']['path']).name
        assert all(preparer.pin(log)[key] == command['log'][key]
                   for key in ['bytes', 'sha256'])
    for path in failed_folder.rglob('*'):
        if path.is_file():
            members['attempts/physical-001/' + str(path.relative_to(failed_folder))] = path
    objects, sources, receipts = {}, {}, {'finite_join': join_pin}
    incoming = context['incoming_modules']
    for module in incoming:
        info = expected[module]
        relative = module.replace('.', '/')
        sources['sources/' + relative + '.lean'] = Path(info['source']['path'])
        objects['objects/' + relative + '.olean'] = Path(info['selected_object']['path'])
    folders = [('finite-join', JOIN / 'qualification')]
    for key in ['audit_source', 'replay_source', 'verifier_source', 'external_verifier_source']:
        item = joined[key]
        members['programs/finite-join/' + Path(item['path']).name] = Path(item['path'])
    previous_context = JOIN / 'CURRENT_ACCEPTED_CONTEXT.json'
    for phase in phases.ORDER:
        parent = json.loads(previous_context.read_text())
        assert parent['formal_acceptance'] and parent['project_closure'] == expected
        for key in ['native_artifacts', 'runtime', 'lean_path']: assert parent[key] == context[key]
        run_path = JOIN / ('verification-' + phase) / 'RUN.json'
        run = load_run(run_path)
        assert run['finite_join_parent'] == join_pin
        assert run['accepted_parent'] == preparer.pin(previous_context)
        phase_modules = ['ImbalancedChen.' + name for name in phases.PHASES[phase]]
        assert set(run['project_closure']) <= set(expected) | set(phase_modules)
        for module, info in run['project_closure'].items():
            if module not in phase_modules:
                assert info['source'] == expected[module]['source']
                assert info['reused_object'] == expected[module]['selected_object']
        for module in phase_modules:
            assert module not in expected
            info = run['project_closure'][module]
            expected[module] = {'source': info['source'], 'selected_object': info['new_object'],
                                'origin': 'accepted-cell01-' + phase}
            relative = module.replace('.', '/')
            sources['sources/' + relative + '.lean'] = Path(info['source']['path'])
            objects['objects/' + relative + '.olean'] = Path(info['new_object']['path'])
        phases.check_catalog(run['project_closure'])
        receipts[phase] = preparer.pin(run_path)
        for key in ['audit_source', 'verifier_source', 'wrapper_source']:
            item = run[key]
            members['programs/' + phase + '/' + Path(item['path']).name] = Path(item['path'])
        folders.append((phase, run_path.parent))
        previous_context = run_path.parent / 'CURRENT_ACCEPTED_CONTEXT.json'
        successor = json.loads(previous_context.read_text())
        assert successor['formal_acceptance'] and not successor['P2_6_complete']
        assert successor['phase_parent'] == preparer.pin(run_path)
        assert successor['project_closure'] == expected
        for key in ['native_artifacts', 'runtime', 'lean_path']: assert successor[key] == context[key]
    assert len(expected) == 1499 and len(objects) == len(sources) == 158
    phases.check_catalog(expected)
    final_context_pin = preparer.pin(previous_context)
    members['CURRENT_ACCEPTED_CONTEXT.json'] = previous_context
    for label, folder in folders:
        for path in folder.iterdir():
            if path.is_file() and path.suffix in {'.json', '.log'}:
                members[label + '/' + path.name] = path
    members.update(sources)
    members.update(objects)
    for name in ['prepare_finite_join.py', 'qualify_finite_join.py',
                 'verify_after_finite.py', 'package_complete_cell.py']:
        members['programs/' + name] = Path(__file__).resolve().parent / name
    OUT.mkdir(parents=True, exist_ok=True)
    pins = {name: preparer.pin(path) for name, path in members.items()}
    manifest = {'schema': 'p26_cell01_complete_original_integral_materials_v1',
        'members': pins, 'P2_6_complete': False, 'original_full_snapshot_verified': False}
    archive = OUT / 'evidence.tar.xz'
    manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode()
    with tarfile.open(archive, 'w:xz') as tar:
        for name, path in sorted(members.items()):
            raw = path.read_bytes()
            assert len(raw) == pins[name]['bytes']
            entry = tarfile.TarInfo(name)
            entry.size, entry.mode = len(raw), 0o644
            tar.addfile(entry, io.BytesIO(raw))
        raw = manifest_bytes
        entry = tarfile.TarInfo('MANIFEST.json')
        entry.size, entry.mode = len(raw), 0o644
        tar.addfile(entry, io.BytesIO(raw))
    with tarfile.open(archive) as tar:
        assert len(tar.getmembers()) == len(members) + 1
        for entry in tar:
            raw = tar.extractfile(entry).read()
            if entry.name == 'MANIFEST.json': assert raw == manifest_bytes
            else: assert raw == members[entry.name].read_bytes()
    assert archive.stat().st_size < 90 * 1024**2, 'Split a large archive before Git publication.'
    for name, item in pins.items(): assert preparer.pin(members[name]) == item
    qualifier.validate(context)
    assert preparer.pin(context_path) == context_pin
    assert preparer.pin(previous_context) == final_context_pin
    for item in receipts.values(): preparer.check(item)
    for label, folder in folders:
        target = OUT / label
        target.mkdir(exist_ok=True)
        shutil.copyfile(folder / 'RUN.json', target / 'RUN.json')
    shutil.copyfile(previous_context, OUT / 'CURRENT_ACCEPTED_CONTEXT.json')
    capsule = {'schema': 'p26_cell01_complete_original_integral_capsule_v1',
        'Cell01_integral_complete': True, 'P2_6_complete': False,
        'original_full_snapshot_verified': False,
        'target': {'cell': 1, 'numerator': '282451447802500037895', 'denominator': '2^96',
                   'premises': [], 'kernel_checked_exact_target_example': True},
        'original_rows': 144, 'original_vertices': 40, 'original_gates': 97,
        'degree': 6, 'saved_max_old_new_retained': True,
        'finite_new_canonical': 41184, 'finite_shared_bodies_checked': 572,
        'new_object_modules': 158, 'accepted_project_union': 1499,
        'receipts': receipts, 'current_accepted_context': final_context_pin,
        'failed_normal_attempt_preserved': preparer.pin(failed_manifest_path),
        'archive': preparer.pin(archive), 'archive_readback_members': len(members) + 1,
        'packager_source': preparer.pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(capsule, indent=2) + '\n')
    print(json.dumps(capsule), flush=True)


if __name__ == '__main__':
    main()
