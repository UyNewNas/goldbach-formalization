"""Assemble existing Policy receipts byte-for-byte; execute no acceptance code."""
from pathlib import Path
import base64
import hashlib
import json
import zlib

ROOT = Path('/workspace/scratch/b70e634c1342')
HERE = ROOT / 'p15-next-medium/next-policy/acceptance-publication'
BASE = HERE.parent / 'formal-publication'
RAW = BASE / 'exact-acceptance-evidence'
COMMIT = 'a00f220200df77b9ca62f93ad2a870567277d767'
TARGET = 'ImbalancedChen.P1SignedExitPolicyComparison'
SOURCE_SHA = 'c60992855b519d9767e66f31c9007dd18f2292e326e28539fc2a39d1d831b57f'
ADAPTER_SHA = '30c7e65f409bf3eaece9f32cbfe10fcc0a21b0c8ed2682bb9592212579fe46d4'
PACKET = 'docs/p1/20261127/p15-policy-comparison-acceptance'
SOURCE_PACKET = 'docs/p1/20261127/p15-signed-exit-policy-comparison/'
OUT = HERE / 'publication' / PACKET


def raw(path):
    assert path.is_file() and not path.is_symlink(), str(path)
    return path.read_bytes()


def fp(value):
    return {'bytes': len(value), 'sha256': hashlib.sha256(value).hexdigest()}


def doc(path):
    return json.loads(raw(path))


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert raw(path) == value, 'existing assembly copy differs: ' + str(path)
    else:
        path.write_bytes(value)


def put_json(path, value):
    put(path, (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode())


def main():
    # Check the existing compressed provider output against every downloaded raw.
    envelope = doc(BASE / 'policy-acceptance-export-raw.json')
    assert envelope['encoding'] == 'zlib+base64'
    compressed = base64.b64decode(envelope['data_base64'], validate=True)
    assert len(compressed) == envelope['compressed_bytes']
    expanded = zlib.decompress(compressed)
    assert fp(expanded) == {k: envelope[k] for k in ('bytes', 'sha256')}
    export = json.loads(expanded)
    assert export['schema'] == 'p15_policy_exact_acceptance_export_v1' and export['read_only']
    entries = doc(BASE / 'EXACT_ACCEPTANCE_FILES.json')
    actual = {(e['group'], e['path']): e for e in entries}
    expected = {(g, p): e for g, files in export['groups'].items() for p, e in files.items()}
    assert len(actual) == len(entries) == envelope['files'] and set(actual) == set(expected)
    assert len(actual) == 58
    for key, entry in actual.items():
        value = raw(RAW / key[0] / key[1])
        original = expected[key]
        assert value == base64.b64decode(original['base64'], validate=True)
        assert fp(value) == {k: original[k] for k in ('bytes', 'sha256')} == {k: entry[k] for k in ('bytes', 'sha256')}
        assert entry['remote_path'] == original['remote_path']
        assert Path(entry['local']) == RAW / key[0] / key[1]
    assert sum(e['bytes'] for e in entries) == 4563570
    op = RAW / 'policy-operation'
    owner = RAW / 'policy-owner'
    audits = list(owner.glob('audits/*/lane-0/OWNED_EXPORTS.json'))
    assert len(audits) == 1
    lane = audits[0].parent
    owned = doc(audits[0])
    assert {row['module'] for row in owned} == {TARGET}
    assert len({row['name'] for row in owned}) == len(owned)
    counts = {'owned': len(owned), 'public': sum(not row['is_private'] for row in owned)}
    axioms = sorted({axiom for row in owned for axiom in row['axioms']})
    assert axioms == ['Classical.choice', 'Quot.sound', 'propext']
    measured = {**counts, 'axioms': axioms}
    passed, worker = doc(op / 'PASS.json'), doc(op / 'WORKER_PASS.json')
    readonly = doc(RAW / 'policy-readonly/READONLY_RESULT.json')
    identity = readonly['identity']
    assert passed['identity'] == worker['identity'] == identity
    assert identity['commit'] == COMMIT and identity['module'] == TARGET
    assert identity['source'] == {'bytes': 17805, 'sha256': SOURCE_SHA}
    assert identity['adapter_sha256'] == ADAPTER_SHA
    assert readonly['status'] == envelope['status'] == 'REVALIDATED'
    assert readonly['normal_or_kernel_commands_executed'] == 0 and not readonly['whole_P1_5_complete']
    assert readonly['owner'] == envelope['owner'] == measured
    assert {k: worker['owner'][k] for k in measured} == measured
    assert passed['worker'] == fp(raw(op / 'WORKER_PASS.json')) and passed['command']['exit_code'] == 0
    command = doc(RAW / 'policy-readonly/READONLY_COMMAND.json')
    assert command['exit_code'] == 0 and command['normal_or_kernel_commands_executed'] == 0
    assert command['stdout_sha256'] == fp(raw(RAW / 'policy-readonly/READONLY_RESULT.json'))['sha256']
    assert command['stderr_sha256'] == fp(raw(RAW / 'policy-readonly/readonly.stderr.log'))['sha256']
    assert not raw(RAW / 'policy-readonly/readonly.stderr.log')
    for stem in ('PRESERVED', 'GIT'):
        assert raw(op / (stem + '_BEFORE.json')) == raw(op / (stem + '_AFTER.json'))
    assert passed['preserved'] == fp(raw(op / 'PRESERVED_BEFORE.json'))
    assert fp(raw(op / 'original-published.lean')) == identity['source']
    assert fp(raw(op / 'executed.py'))['sha256'] == ADAPTER_SHA
    normal_dir = owner / 'normal' / TARGET
    normal = doc(normal_dir / 'NORMAL_PASS.json')
    normal_command = doc(normal_dir / 'attempt-00000/normal-command.json')
    validation = doc(lane / 'VALIDATION_RESULTS.json')
    assert normal['source_commit'] == COMMIT and normal['module'] == TARGET
    assert normal_command['exit_code'] == 0 and normal_command['actual_built_modules'] == [TARGET]
    assert not normal_command['actual_failed_modules'] and normal_command['project_error_count'] == 0
    assert normal_command['log_sha256'] == fp(raw(normal_dir / 'attempt-00000/normal.log'))['sha256']
    assert validation['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
    assert validation['modules'] == {TARGET: SOURCE_SHA}
    assert validation['total_owned_exports'] == counts['owned'] and validation['total_public_exports'] == counts['public']
    for flag in ('full_owned_including_private_generated', 'only_standard_axioms', 'pp_all_true_no_elisions', 'source_plus_five_outputs_unchanged_across_kernel_and_audit', 'successful_normal_not_repeated'):
        assert validation[flag] is True
    for command in (validation['kernel_commands'][TARGET], validation['audit_command']):
        assert command['exit_code'] == 0 and command['log_sha256'] == fp(raw(lane / command['log']))['sha256']
    assert worker['native_stock']['exit_code'] == 0 and not worker['native_stock']['actual_built_modules']
    # Compare the recorded reused inputs, without invoking any old reader.
    prior = identity['partition_original_acceptance']
    assert prior['status'] == 'REVALIDATED' and prior['normal_or_kernel_commands_executed'] == 0
    assert prior['identity']['commit'] == '7296a9659fbf34773ec03f437860c14073b3a638'
    assert prior['identity']['dictionary_original_reference']['source_acceptance_commit'] == '040d46058821746c69c5183b3f6c22792287c4ba'
    assert prior['identity']['variation_original_acceptance']['identity']['commit'] == 'f7e9219f4860a819758d52752c5a9309dd14a8c7'
    old = doc(ROOT / 'p15-next-medium-probe/DEPENDENCY_REUSE_SPEC.json')
    context = doc(normal_dir / 'attempt-00000/CONTEXT_BEFORE.json')
    assert normal['dependency_context'] == context and context['source_commit'] == COMMIT
    partition = 'ImbalancedChen.P1SignedExitPartition'
    assert set(context['project_sources']) == set(old['graph']) | {partition, TARGET}
    assert len(context['dependency_objects_and_traces']) == 82
    for module, row in old['dependencies'].items():
        assert context['project_sources'][module] == row['source']['sha256']
        for path, pin in row['normal_objects_and_traces'].items():
            assert context['dependency_objects_and_traces'][path] == pin
    assert context['project_sources'][partition] == prior['identity']['new_source_sha256']
    assert identity['actual_project_dependencies'] == 41 and identity['formal_graph_sources'] == 42
    # The original provider records and stdout are retained, not regenerated.
    provider_files = {}
    for label, job in [('FORMAL', 'job_af3e2532c0e347169c13e97e1f3433b5'), ('READONLY', 'job_4d66fb043c0249d7beef3301d11947df')]:
        path = ROOT / 'p15-next-acceptance-metadata' / ('POLICY_' + label + '_PROVIDER_TASK.json')
        task = doc(path)
        assert task['job_id'] == job and task['status'] == 'succeeded' and task['exit_code'] == 0
        provider_files[label] = {'job_id': job, **fp(raw(path))}
        put(OUT / 'provider' / path.name, raw(path))
    formal_result = doc(BASE / 'formal-task-result.json')
    formal_stdout = [json.loads(line) for line in raw(BASE / 'formal-task-output.log').decode().splitlines() if line.startswith('{')]
    assert formal_result == formal_stdout[-1] == readonly
    for key in actual:
        put(OUT / 'raw' / key[0] / key[1], raw(RAW / key[0] / key[1]))
    for name in ('policy-acceptance-export-raw.json', 'EXACT_ACCEPTANCE_FILES.json', 'EXACT_ACCEPTANCE_SUMMARY.json', 'formal-task-output.log', 'formal-task-result.json', 'stage_run_policy.py', 'export_policy_acceptance.py', 'ROOT_BINDING_VERIFICATION.json'):
        put(OUT / 'transport' / name, raw(BASE / name))
    # Reference the already published and reviewed source packet at a00f.
    selected = ['P1SignedExitPolicyComparison.lean', 'run_policy.py', 'INPUTS.json', 'PARTITION_BINDING.json', 'POLICY_ORIGINAL_INTERFACE.json', 'POLICY_PUBLICATION_SCOPE_PINS.json', 'README.md', 'BINDING_ONLY.diff', 'BINDING_SUMMARY.json', 'reviewed-unbound/run_policy.py', 'reviewed-unbound/INDEPENDENT_REVIEW.json', 'reviewed-unbound/LOCAL_CHECKS.json', 'support/probe_policy_v1.py']
    indexed = {row['path']: row for row in doc(BASE / 'FILE_INDEX.json')}
    refs = []
    for path in ['ImbalancedChen/P1SignedExitPolicyComparison.lean'] + [SOURCE_PACKET + name for name in selected]:
        row = indexed[path]
        assert fp(raw(Path(row['local']))) == {k: row[k] for k in ('bytes', 'sha256')}
        refs.append({'commit': COMMIT, 'path': path, **fp(raw(Path(row['local'])))})
    put_json(OUT / 'SOURCE_AND_REVIEW_REFERENCES.json', {'schema': 'p15_policy_accepted_source_references_v1', 'source_acceptance_commit': COMMIT, 'source_publication_parent': identity['publication_parent'], 'references': refs})
    for path, name in [(ROOT / 'p15-next-medium/BOUNDARY_DEPENDENCY_REUSE.json', 'BOUNDARY_DEPENDENCY_REUSE.json'), (ROOT / 'p15-next-medium/boundary-dependency-analysis/SOURCE_MANIFEST.json', 'SOURCE_MANIFEST.json'), (ROOT / 'p15-next-medium/boundary-dependency-analysis/SOURCE_FETCHES.json', 'SOURCE_FETCHES.json')]:
        put(OUT / 'future-inputs' / name, raw(path))
    put(OUT / 'README.md', raw(HERE / 'README.md'))
    put(OUT / 'assemble_policy_acceptance.py', raw(Path(__file__)))
    summary = {'schema': 'p15_policy_acceptance_evidence_assembly_v1', 'publication_parent': COMMIT, 'source_acceptance_commit': COMMIT, 'module': TARGET, 'source': identity['source'], 'raw_files': len(entries), 'raw_bytes': sum(e['bytes'] for e in entries), 'compressed_original_stdout': fp(raw(BASE / 'policy-acceptance-export-raw.json')), 'formal_pass': fp(raw(op / 'PASS.json')), 'independent_readonly': fp(raw(RAW / 'policy-readonly/READONLY_RESULT.json')), 'owned_census': {**measured, 'private': counts['owned'] - counts['public'], 'derived_from': audits[0].relative_to(RAW).as_posix(), 'raw_binding': fp(raw(audits[0]))}, 'provider_tasks': provider_files, 'original_dependency_identities': {'Dictionary': '040d46058821746c69c5183b3f6c22792287c4ba', 'Partition': '7296a9659fbf34773ec03f437860c14073b3a638', 'Variation': 'f7e9219f4860a819758d52752c5a9309dd14a8c7'}, 'project_dependencies': 41, 'project_graph_including_target': 42, 'recorded_preservation_bytes_equal': True, 'original_fixed_registry': {'accepted': 18, 'registered': 21}, 'policy_is_additional_owner': True, 'future_inputs_grant_new_acceptance': False, 'whole_P1_5_complete': False, 'assembly_execution': {'cloud_commands': 0, 'git_commands': 0, 'normal_or_kernel_commands': 0, 'old_tests_replayed': 0, 'acceptance_readers_invoked': 0}}
    put_json(OUT / 'ASSEMBLY_SUMMARY.json', summary)
    review = HERE / 'INDEPENDENT_REVIEW.json'
    if review.exists():
        put(OUT / 'INDEPENDENT_REVIEW.json', raw(review))
    index = [{'local': str(path), 'path': path.relative_to(HERE / 'publication').as_posix(), **fp(raw(path))} for path in sorted(OUT.rglob('*')) if path.is_file()]
    assert all(row['path'].startswith(PACKET + '/') for row in index)
    (HERE / 'FILE_INDEX.json').write_text(json.dumps(index, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'files': len(index), 'bytes': sum(row['bytes'] for row in index), 'index': str(HERE / 'FILE_INDEX.json'), 'index_binding': fp(raw(HERE / 'FILE_INDEX.json')), 'assembly_summary': fp(raw(OUT / 'ASSEMBLY_SUMMARY.json')), 'independent_review_included': review.exists(), 'owned_census': summary['owned_census']}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
