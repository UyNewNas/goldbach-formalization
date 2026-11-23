#!/usr/bin/env python3
"""Final read-only stock check and exact identities for completed P6 roots."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess
import time

ROOT = Path('/workspace/blue-p6-controller')
PROJECT = Path('/workspace/blue-p6-build')


def digest(path):
    return {'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    lock = (ROOT / 'controller.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    directory = ROOT / 'final-four-roots'
    directory.mkdir(exist_ok=True)
    assert not any(directory.iterdir()), "Final receipt directory must be empty before the one stock run"
    selection_path = Path('/workspace/blue-p6-selection.json')
    selection = json.loads(selection_path.read_text())
    targets = ['ImbalancedChen.P6OriginalSeventhMeshPrice', 'ImbalancedChen.P6OriginalEighthMeshPrice',
               'ImbalancedChen.P6OriginalNinthMeshPrice', 'ImbalancedChen.P6OriginalZeroMarkedIntegralCost']
    records = {}
    for phase, module in zip(['seventh', 'eighth', 'ninth', 'zero'], targets):
        path = ROOT / phase / 'validation/VALIDATION_RESULTS.json'
        record = json.loads(path.read_text())
        assert record['kernel']['exit_code'] == record['types_and_axioms']['exit_code'] == 0
        assert module in record['modules']
        assert record['sources_and_outputs_unchanged']
        build = json.loads((ROOT / phase / 'BUILD_PROCESS.json').read_text())
        assert build['exit_code'] == 0 and build['target'] == module
        records[phase] = {'root': module, 'normal_build': build,
                          'validation_results': str(path), 'validation_results_sha256': digest(path)['sha256'],
                          'declared_audit_scope': record['modules'],
                          'owned_declaration_counts': record['declaration_counts'],
                          'owned_declaration_total': sum(record['declaration_counts'].values()),
                          'observed_axioms': record['observed_axioms']}

    snapshots = {}
    auxiliary_gaps = []
    changed = []
    for module, selected in selection['project_sources'].items():
        source = PROJECT / selected['install_path']
        source_record = digest(source)
        if source_record['sha256'] != selected['sha256']:
            changed.append(module)
        stem = module.replace('.', '/')
        facets = {}
        for name, relative in [('olean', '.lake/build/lib/lean/' + stem + '.olean'),
                               ('ilean', '.lake/build/lib/lean/' + stem + '.ilean'),
                               ('c', '.lake/build/ir/' + stem + '.c'),
                               ('trace', '.lake/build/lib/lean/' + stem + '.trace'),
                               ('setup', '.lake/build/ir/' + stem + '.setup.json')]:
            path = PROJECT / relative
            if path.is_file():
                facets[name] = {'path': str(path), **digest(path)}
            else:
                assert name == 'setup' and module == 'ImbalancedChen.ChenLogLevelGeometry'
                auxiliary_gaps.append({'module': module, 'facet': name, 'path': str(path),
                                       'reason': 'Qualified Member project13 reuse deliberately installed only seven portable facets; producer setup input was not adopted. Actual normal root builds replay this module successfully.'})
        snapshots[module] = {'source': {'path': str(source), **source_record},
                             'selected_source_sha256': selected['sha256'], 'facets': facets}
    assert len(snapshots) == 208 and len(changed) == 34
    for module, selected in selection['native_sources'].items():
        assert digest(PROJECT / '.lake/packages/goldbach' / selected['install_path'])['sha256'] == selected['sha256'], module
    save(directory / 'ALL_SELECTED_PROJECT_SOURCE_AND_FACETS_BEFORE.json', snapshots)

    guard_log = Path('/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl')
    command = ['python3', '/workspace/blue-build-tools/run_guarded.py', 'lake', '--no-build',
               'build', *['+' + target + ':olean' for target in targets]]
    process = {'command': command, 'cwd': str(PROJECT),
               'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'guard_log_start_bytes': guard_log.stat().st_size}
    save(directory / 'STOCK_PROCESS.json', process)
    started = time.monotonic()
    with (directory / 'stock.log').open('wb') as output:
        result = subprocess.run(command, cwd=PROJECT, stdout=output, stderr=subprocess.STDOUT)
    raw = guard_log.read_bytes()[process['guard_log_start_bytes']:]
    commands = [json.loads(line) for line in raw.splitlines()]
    source_commands = [r for r in commands if r['tool'] == 'lean' and
                       ('--stdin' in r['input_args'] or any(a.endswith('.lean') for a in r['input_args']))]
    process.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - started,
                   finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   guard_log_end_bytes=guard_log.stat().st_size,
                   source_compiler_calls=len(source_commands), log_sha256=digest(directory / 'stock.log')['sha256'])
    save(directory / 'STOCK_PROCESS.json', process)
    (directory / 'STOCK_GUARD_COMMANDS.jsonl').write_bytes(raw)
    assert result.returncode == 0 and not source_commands
    for record in snapshots.values():
        assert digest(Path(record['source']['path'])) == {k: record['source'][k] for k in ['bytes', 'sha256']}
        for facet in record['facets'].values():
            assert digest(Path(facet['path'])) == {k: facet[k] for k in ['bytes', 'sha256']}
    save(directory / 'ALL_SELECTED_PROJECT_SOURCE_AND_FACETS_AFTER.json', snapshots)
    receipt = {'schema': 'p6_four_exact_original_price_roots_acceptance_v1',
               'result': 'PASS_FOUR_NORMAL_ROOT_BUILDS_EXACT_NAMED_KERNEL_FULL_OWNED_AUDITS_AND_FINAL_ZERO_SOURCE_STOCK',
               'project': str(PROJECT), 'source_selection': str(selection_path),
               'source_selection_sha256': digest(selection_path)['sha256'],
               'source_selection_project_count': 208, 'source_selection_native_count': 810,
               'all_native_sources_exact_selection': True,
               'project_proof_compatibility_postimage_count': len(changed),
               'project_postimage_modules': changed, 'phases': records,
               'final_stock': process,
               'all_selected_project_sources_have_olean_ilean_generated_c_and_trace': True,
               'project_auxiliary_setup_inputs_present': 208 - len(auxiliary_gaps),
               'project_auxiliary_setup_input_exceptions': auxiliary_gaps,
               'final_stock_source_and_facet_snapshots_unchanged': True,
               'source_and_five_outputs_unchanged_for_each_newly_audited_module': True,
               'native_or_project_cache_reuse_is_new_proof_work': False,
               'data_inputs': selection['data_inputs'],
               'scope_limitations': ['Kernel replay covers the exact named phase audit modules relative to their recorded imports; no claim of fresh replay of all 208+810 modules.',
                                     'The 34 postimages preserve public statements/definitions/constants/assumptions except six explicitly recorded finite-carrier coercion annotations restoring old ill-typed syntax.',
                                     'UniformTaylorTail includes a repaired false internal arithmetic equality using existing conservative slack; public 672/125 bound is unchanged.',
                                     'No frozen source/numerical archive was modified.']}
    save(directory / 'FOUR_ROOT_ACCEPTANCE.json', receipt)
    state_path = ROOT / 'STATE.json'
    state = json.loads(state_path.read_text())
    zero_validation = ROOT / 'zero/validation/VALIDATION_RESULTS.json'
    zero = json.loads(zero_validation.read_text())
    state.setdefault('verified_phases', {})['zero'] = {
        'build_process': 'zero/BUILD_PROCESS.attempt1.json',
        'validation_results': 'zero/validation/VALIDATION_RESULTS.json',
        'validation_results_sha256': digest(zero_validation)['sha256'],
        'declaration_counts': zero['declaration_counts'], 'source_and_outputs_unchanged': True}
    state.update(status='ALL_FOUR_ROOTS_NORMAL_KERNEL_FULL_OWNED_AND_FINAL_STOCK_PASS',
                 final_acceptance=str(directory / 'FOUR_ROOT_ACCEPTANCE.json'))
    save(state_path, state)
    print(json.dumps({'receipt': str(directory / 'FOUR_ROOT_ACCEPTANCE.json'),
                      'receipt_sha256': digest(directory / 'FOUR_ROOT_ACCEPTANCE.json')['sha256'],
                      'stock': process}))


if __name__ == '__main__':
    main()
