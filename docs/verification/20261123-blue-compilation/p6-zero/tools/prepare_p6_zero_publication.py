#!/usr/bin/env python3
"""Package completed Zero and final four-root evidence; no builds or edits."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/workspace/blue-p6-controller')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    phase = ROOT / 'zero'
    validation = json.loads((phase / 'validation/VALIDATION_RESULTS.json').read_text())
    normal = json.loads((phase / 'BUILD_PROCESS.attempt1.json').read_text())
    final = ROOT / 'final-four-roots'
    stock = json.loads((final / 'STOCK_PROCESS.json').read_text())
    assert normal['exit_code'] == validation['kernel']['exit_code'] == validation['types_and_axioms']['exit_code'] == stock['exit_code'] == 0
    raw = Path('/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl').read_bytes()[normal['guard_log_start_bytes']:stock['guard_log_start_bytes']]
    commands = [json.loads(line) for line in raw.splitlines()]
    sources = [r for r in commands if r['tool'] == 'lean' and
               ('--stdin' in r['input_args'] or any(a.endswith('.lean') for a in r['input_args']))]
    assert all(all(flag in r['command'] for flag in ['-t0', '-j2', '-M12288']) for r in sources)
    (phase / 'GUARDED_COMPILER_COMMANDS.jsonl').write_bytes(raw)
    summary = {
        'schema': 'p6_zero_root_and_marked_integral_prices_verified_v1',
        'result': 'PASS_NORMAL_AGGREGATE_EXACT_MODULE_KERNEL_FULL_OWNED_TYPES_AND_STANDARD_AXIOMS',
        'root': 'ImbalancedChen.P6OriginalZeroMarkedIntegralCost',
        'normal_build': normal, 'audited_modules': validation['modules'],
        'defining_module_declaration_counts': validation['declaration_counts'],
        'total_owned_declarations': sum(validation['declaration_counts'].values()),
        'observed_axioms': validation['observed_axioms'],
        'source_and_five_outputs_per_module_unchanged': True,
        'both_sources_entirely_byte_identical_to_exact_R02_selection': True,
        'source_preservation': 'SOURCE_PRESERVATION.json',
        'new_proof_repairs': [],
        'all_recorded_source_commands_have_trust0_threads2_memory12288': True,
        'guard_source_command_count': len(sources),
        'kernel_checker_environment_threads': 2,
        'kernel_checker_memory_flag': 'not a source compiler; no -M flag claimed',
        'validation_results_sha256': sha(phase / 'validation/VALIDATION_RESULTS.json'),
        'final_four_root_stock': {'exit_code': stock['exit_code'], 'source_calls': stock['source_compiler_calls'],
                                 'receipt': 'p6-four-roots/FOUR_ROOT_ACCEPTANCE.json',
                                 'receipt_sha256': sha(final / 'FOUR_ROOT_ACCEPTANCE.json')},
        'scope_limitations': ['Exact named-module kernel replay relative to current imports; no fresh all-import replay claim.',
                              '208 selected project sources have olean, ilean, generated C and trace; one qualified reused module lacks the auxiliary producer setup input, explicitly recorded in the four-root receipt.',
                              'No frozen source/numerical archive or original manuscript parameter was changed.']}
    save(phase / 'BATCH_SUMMARY.json', summary)
    files = []
    def add(path, destination):
        files.append({'source': str(path), 'destination': 'docs/verification/20261123-blue-compilation/' + destination,
                      'sha256': sha(path), 'bytes': path.stat().st_size})
    for path in sorted((phase / 'validation').glob('*')):
        if path.is_file():
            add(path, 'p6-zero/validation/' + path.name)
    for name in ['BATCH_SUMMARY.json', 'SOURCE_CONTEXT.json', 'SOURCE_PRESERVATION.json',
                 'GUARDED_COMPILER_COMMANDS.jsonl', 'ROOT_BASELINE.lean',
                 'BUILD_PROCESS.attempt1.json', 'build.attempt1.log']:
        add(phase / name, 'p6-zero/' + name)
    for path in sorted(final.iterdir()):
        if path.is_file():
            add(path, 'p6-four-roots/' + path.name)
    for name in ['run_p6_phase.py', 'validate_p6_modules_v3_cached_fold.py', 'record_p6_context.py',
                 'finalize_p6_four_roots.py', 'prepare_p6_zero_publication.py']:
        add(Path('/workspace/blue-build-tools') / name, 'p6-zero/tools/' + name)
    save(phase / 'PUBLISH_FILES.json', {'schema': 'reviewable_publish_files_v1',
                                      'source_root': str(phase),
                                      'destination_root': 'docs/verification/20261123-blue-compilation/p6-zero',
                                      'files': files})
    print(json.dumps({'publish_list': str(phase / 'PUBLISH_FILES.json'),
                      'publish_list_sha256': sha(phase / 'PUBLISH_FILES.json'),
                      'file_count': len(files), 'bytes': sum(x['bytes'] for x in files),
                      'total_owned_declarations': summary['total_owned_declarations'],
                      'validation_results_sha256': summary['validation_results_sha256']}))


if __name__ == '__main__':
    main()
