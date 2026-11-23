#!/usr/bin/env python3
"""Package existing P6 Ninth verification evidence; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path('/workspace/blue-p6-controller')
PHASE = ROOT / 'ninth'
REPO = Path('/workspace/goldbach-formalization')
STAGE = Path('/workspace/blue-p6-build')
DEST = 'docs/verification/20261123-blue-compilation/p6-ninth'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    validation = json.loads((PHASE / 'validation/VALIDATION_RESULTS.json').read_text())
    assert validation['result'].startswith('PASS_')
    modules = validation['modules']
    diagnoses = {
        'P2U9DirectedRationalCover': 'Explicit rational coefficient casts and pinned addition orientation; expose unchanged interval aliases and normalize rational endpoint/log-density casts.',
        'CurrentChenP5U9OriginalIntegralGap': 'Reuse exact existing remote 86d2a123 proof postimage: specify (μ := volume) for the interval-integrability hint.',
        'CurrentP5CausalCellEventualAssembly': 'Reuse existing six Finset-to-Set carrier annotations. Old expressions were ill-typed; explicit coercion preserves the existing full finite carrier and all assumptions, conclusions and proof bodies.',
        'P5zPositiveFamilyBudget': 'Type the original prime/size conjunction before if_pos; explicitly supply the existing N parameter to the prime/coprimality helper.',
        'P5OriginalKFeedbackBudget': 'Normalize multiplication/division association with simpa instead of a no-progress convert/ring sequence.',
        'P5OriginalFixedDensitySupplierAssembly': 'Use pinned add_le_add_left for the right-added fixed error term.',
        'P5zUpsilon9SwitchedMultiplicity': 'Use existing Finset membership equivalences explicitly, avoid reducible Sigma projection mismatch in q<N+1, and apply the pinned right-added cardinality inequality.',
        'P5zUpsilon9SmallPrimeBudget': 'Beta-normalize the receiver-map injectivity hypothesis before omega.',
        'P5zUpsilon9SourceMass': 'Normalize only the existing multiplication/division association when transporting the scaled logarithmic-integral mass bound.',
        'CurrentChenP5U9CoprimeCorrection': 'Split the existing coprimality condition and close the signed Fubini coefficient identity by ring; retain arbitrary signed rho and the original domains.',
        'P5zUpsilon9OriginalSlot': 'Use pinned add_le_add_left for right-added delta; retain every independent analytic input.',
        'CurrentChenP5U9DirectedLowerCertificate': 'Normalize the unchanged a,b,d,logDensity rational casts explicitly.',
        'CurrentChenP5U9UniformTaylorTail': 'The old internal equality is false: 32*(59/250-19/125)=336/125. Keep the original public 672/125 upper bound and use the nonnegative geometric tail to prove the internal weak inequality.',
        'P5zUpsilon9OriginalRoute': 'Use abs_add_le for the two triangle inequalities and add_le_add_left for their right-added third term.',
    }
    selection_path = Path('/workspace/blue-p6-selection.json')
    selection = json.loads(selection_path.read_text())
    repairs = {}
    for module in modules:
        short = module.split('.')[-1]
        if short not in diagnoses:
            continue
        directory = ROOT / 'repairs' / short
        if short != 'CurrentP5CausalCellEventualAssembly':
            subprocess.run(['python3', '/workspace/blue-build-tools/record_p6_repair.py', short,
                            '--status', 'PASS_NORMAL_AGGREGATE_BUILD_EXACT_MODULE_KERNEL_AND_FULL_OWNED_TYPES_AXIOMS'], check=True)
        record_path = directory / 'SOURCE_SELECTION.json'
        record = json.loads(record_path.read_text())
        original = selection['project_sources'][module]
        assert record['preimage_sha256'] == original['sha256'], short
        assert sha(directory / 'before.lean') == record['preimage_sha256']
        assert sha(directory / 'postimage.lean') == record['postimage_sha256']
        assert sha(STAGE / original['install_path']) == record['postimage_sha256']
        assert sha(REPO / original['install_path']) == record['postimage_sha256']
        record.update(original_exact_selection=original, diagnosis=diagnoses[short],
                      validation_status='PASS_NORMAL_AGGREGATE_BUILD_EXACT_MODULE_KERNEL_AND_FULL_OWNED_TYPES_AXIOMS',
                      validation_results='validation/VALIDATION_RESULTS.json',
                      defining_module_owned_declarations=validation['declaration_counts'][module],
                      neutral_historical_status_comment_pointer='docs/verification/20261123-blue-compilation',
                      constants_and_assumptions_unchanged=True,
                      substantive_manuscript_gap_identified=False)
        if short == 'CurrentChenP5U9OriginalIntegralGap':
            record['existing_exact_source_fix_commit'] = '86d2a123d08befe29c69454637fa9aa1d2614441'
            record['exact_existing_remote_postimage'] = True
        if short == 'CurrentChenP5U9UniformTaylorTail':
            record['classification'] = 'repairable_proof_internal_arithmetic_error_and_conservative_slack'
            record['internal_arithmetic_review'] = 'TAYLOR_INTERNAL_SLACK_REVIEW.json'
        save(record_path, record)
        repairs[short] = {key: record[key] for key in [
            'preimage_sha256', 'postimage_sha256', 'source_command_count',
            'all_theorem_headers_preserved', 'all_definitions_structures_instances_preserved',
            'diagnosis', 'validation_status']}
        if short == 'CurrentP5CausalCellEventualAssembly':
            repairs[short]['header_coercion_syntax_exception'] = record['header_coercion_syntax_exception']
        if short == 'CurrentChenP5U9UniformTaylorTail':
            repairs[short]['classification'] = record['classification']
    assert len(repairs) == 14

    attempts = []
    for number in range(1, 14):
        path = PHASE / f'build.attempt{number}.log'
        lines = path.read_text().splitlines()
        errors = []
        for index, line in enumerate(lines):
            if line.startswith('error: ImbalancedChen/'):
                end = index + 1
                while end < len(lines) and not lines[end].startswith(('error:', 'warning:', '✖', '✔', '⚠', 'ℹ', 'Some required builds', 'error: build')):
                    end += 1
                errors.append({'line': index + 1, 'text': '\n'.join(lines[index:end]).rstrip()})
        attempts.append({'attempt': number, 'log': path.name, 'sha256': sha(path),
                         'process': json.loads((PHASE / f'BUILD_PROCESS.attempt{number}.json').read_text()),
                         'errors': errors})
    assert attempts[-1]['process']['exit_code'] == 0 and not attempts[-1]['errors']
    save(PHASE / 'FAILURE_DIAGNOSES.json', {
        'scope': 'Actual canonical normal build attempts1 through12 and final successful attempt13; all failing raw logs retained, including unsuccessful proof-API variants and a removed trace_state diagnostic.',
        'classification': 'Pinned API, elaboration/coercion and local omitted proof detail, plus the separately recorded repairable internal Taylor arithmetic equality error. No substantive manuscript gap identified.',
        'module_diagnoses': diagnoses, 'attempts': attempts})

    guard_path = Path('/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl')
    start = attempts[0]['process']['guard_log_start_bytes']
    end = json.loads((ROOT / 'zero/BUILD_PROCESS.attempt1.json').read_text())['guard_log_start_bytes']
    raw = guard_path.read_bytes()[start:end]
    records = [json.loads(line) for line in raw.splitlines()]
    assert all(r['cwd'] == str(STAGE) for r in records)
    source_records = [r for r in records if r['tool'] == 'lean' and
                      ('--stdin' in r['input_args'] or any(x.endswith('.lean') for x in r['input_args']))]
    assert all(all(x in r['command'] for x in ['-t0', '-j2', '-M12288']) for r in source_records)
    (PHASE / 'GUARDED_COMPILER_COMMANDS.jsonl').write_bytes(raw)

    root_module = 'ImbalancedChen.P6OriginalNinthMeshPrice'
    root_source = selection['project_sources'][root_module]
    assert sha(STAGE / root_source['install_path']) == root_source['sha256']
    summary = {
        'schema': 'p6_ninth_root_and_support_repairs_verified_v1',
        'result': 'PASS_NORMAL_AGGREGATE_EXACT_MODULE_KERNEL_FULL_OWNED_TYPES_AND_STANDARD_AXIOMS',
        'root': root_module, 'normal_build': attempts[-1]['process'],
        'audited_modules': modules, 'defining_module_declaration_counts': validation['declaration_counts'],
        'total_owned_declarations': sum(validation['declaration_counts'].values()),
        'observed_axioms': validation['observed_axioms'],
        'source_and_five_outputs_per_module_unchanged': True,
        'root_source_changed': False, 'root_source_sha256': root_source['sha256'],
        'main_canonical_root_exists': (REPO / root_source['install_path']).exists(),
        'proof_only_and_explicit_coercion_compatibility_repairs': repairs,
        'repaired_source_command_count': sum(x['source_command_count'] for x in repairs.values()),
        'header_scope': 'Literal theorem-header invariance holds for thirteen repaired modules; CurrentP5CausalCellEventualAssembly has six owner-authorized explicit finite-carrier coercion annotations, restoring ill-typed original syntax. Its proof bodies are identical.',
        'arithmetic_scope': json.loads((PHASE / 'TAYLOR_INTERNAL_SLACK_REVIEW.json').read_text()),
        'guard_source_command_count_including_failed_tooling_audits': len(source_records),
        'all_recorded_source_commands_have_trust0_threads2_memory12288': True,
        'kernel_checker_environment_threads': 2,
        'kernel_checker_memory_flag': 'not a source compiler; no -M flag claimed',
        'validation_results_sha256': sha(PHASE / 'validation/VALIDATION_RESULTS.json'),
        'audit_inventory': validation['inventory_method'],
        'audit_tooling_failures': [
            {'path': 'validation/audit-tooling-attempt1', 'reason': 'Mutable variable shadowing in prepared audit tooling; no project source failure.'},
            {'path': 'validation/audit-tooling-attempt2', 'reason': 'Attempted ModuleData index/owner crosscheck did not align; used authorized cached-header original full fold fallback. No ModuleData equality claim.'}],
        'successful_audit_reuses_same_passed_kernel': True,
        'project_cache_reuse_reference': json.loads((PHASE / 'PROJECT13_REUSE_REFERENCE.json').read_text()),
        'scope_limitations': ['Exact named-module kernel replay relative to current imports; no fresh all-import replay claim.',
                              'Imported cache adoption is not new project theorem work.',
                              'No frozen archive, manuscript object, public bound, numerical definition or assumption was changed.']}
    save(PHASE / 'BATCH_SUMMARY.json', summary)

    files = []
    def add(source, destination):
        files.append({'source': str(source), 'destination': DEST + '/' + destination,
                      'sha256': sha(source), 'bytes': source.stat().st_size})
    for path in sorted((PHASE / 'validation').rglob('*')):
        if path.is_file():
            add(path, str(path.relative_to(PHASE)))
    for name in ['BATCH_SUMMARY.json', 'SOURCE_CONTEXT.json', 'FAILURE_DIAGNOSES.json',
                 'GUARDED_COMPILER_COMMANDS.jsonl', 'ROOT_BASELINE.lean',
                 'PROJECT13_REUSE_REFERENCE.json', 'TAYLOR_INTERNAL_SLACK_REVIEW.json']:
        add(PHASE / name, name)
    for number in range(1, 14):
        for name in [f'build.attempt{number}.log', f'BUILD_PROCESS.attempt{number}.json']:
            add(PHASE / name, name)
    for short in repairs:
        directory = ROOT / 'repairs' / short
        for name in ['before.lean', 'postimage.lean', 'candidate.patch', 'SOURCE_SELECTION.json']:
            add(directory / name, 'repairs/' + short + '/' + name)
        for path in sorted(directory.glob('remote-*.lean')):
            add(path, 'repairs/' + short + '/' + path.name)
        if (directory / 'NORMAL_MODULE_BUILD_RECEIPT.json').exists():
            add(directory / 'NORMAL_MODULE_BUILD_RECEIPT.json', 'repairs/' + short + '/NORMAL_MODULE_BUILD_RECEIPT.json')
    for path in [Path('/workspace/blue-build-tools') / name for name in [
            'run_p6_phase.py', 'validate_p6_modules_v3_cached_fold.py', 'record_p6_repair.py',
            'record_p6_context.py', 'prepare_p6_ninth_publication.py']]:
        add(path, 'tools/' + path.name)
    if (PHASE / 'INDEPENDENT_REVIEW.json').exists():
        add(PHASE / 'INDEPENDENT_REVIEW.json', 'INDEPENDENT_REVIEW.json')
    assert len({x['destination'] for x in files}) == len(files)
    save(PHASE / 'PUBLISH_FILES.json', {'schema': 'reviewable_publish_files_v1',
                                     'source_root': str(PHASE), 'destination_root': DEST,
                                     'files': files})
    print(json.dumps({'publish_list': str(PHASE / 'PUBLISH_FILES.json'),
                      'publish_list_sha256': sha(PHASE / 'PUBLISH_FILES.json'),
                      'file_count': len(files), 'bytes': sum(x['bytes'] for x in files),
                      'total_owned_declarations': summary['total_owned_declarations'],
                      'repaired_source_command_count': summary['repaired_source_command_count']}))


if __name__ == '__main__':
    main()
