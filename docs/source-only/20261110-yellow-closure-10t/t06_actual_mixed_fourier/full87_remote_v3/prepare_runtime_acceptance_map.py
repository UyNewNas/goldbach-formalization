"""Static source/import/data acceptance mapping; no runtime or proof execution."""
from __future__ import annotations
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[5]
NATIVE = WORKSPACE / 'goldbach-variable-envelope/.lake/ntfs-source-backups-20261011/goldbach'


def read(path):
    return Path('\\\\?\\' + str(path.resolve())).read_bytes()


def desc(payload):
    return {'bytes': len(payload), 'sha256': hashlib.sha256(payload).hexdigest(),
            'raw_git_blob_sha1': hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()}


def save(name, obj):
    (HERE / name).write_bytes((json.dumps(obj, indent=2, ensure_ascii=False) + '\n').encode())


def main():
    m = json.loads(read(HERE / 'EXACT_INSTALL_MANIFEST.json'))
    active = set(m['targets'][0]['closure_modules'])
    candidates = set(m['potential_v3_source_matches_only_not_accepted_objects'])
    forbidden = set(m['semantic_forbidden_old_object_modules'])
    rows = {r['module']: r for r in m['files']}
    data = {r['install_path']: r for r in m['data_inputs']}
    direct_inputs = {}
    for r in m['data_inputs']:
        consumers = r.get('consumed_by', [])
        for key in ['consuming_module', 'consumer_module']:
            if key in r:
                consumers = consumers + [r[key]]
        for module in consumers:
            direct_inputs.setdefault(module, []).append(r['install_path'])
    per_module = []
    for name in sorted(active):
        r = rows[name]
        per_module.append({'module': name, 'source': {k: r[k] for k in ['install_path', 'bytes', 'sha256', 'git_blob_sha1', 'origin']},
            'expected_direct_imports': r['imports'],
            'project_predecessors': [n for n in r['imports'] if n.startswith('ImbalancedChen.')],
            'external_direct_imports': [n for n in r['imports'] if not n.startswith('ImbalancedChen.')],
            'declared_direct_compile_time_input_paths': sorted(set(direct_inputs.get(name, []))),
            'old_semantic_object_restore_forbidden': name in forbidden,
            'producer_source_match_only_not_object_acceptance': name in candidates,
            'required_build_class': ('conditional_real_artifact_per_module_rebind' if name in candidates else 'fresh_or_unmatched_source_build'),
            'actual_setup_import_read_receipt': None, 'accepted_object': None})
    plan = json.loads(read(HERE / 'NATIVE_RESEARCH_OVERLAY.json'))
    native = []
    for r in plan['files']:
        payload = subprocess.check_output(['git', '-C', str(NATIVE), 'show', plan['native_commit'] + ':' + r['path']])
        observed = desc(payload)
        if observed['bytes'] != r['bytes'] or observed['raw_git_blob_sha1'] != r['git_blob_sha1']:
            raise ValueError('Native original raw Git source differs')
        native.append({**r, 'source_sha256': observed['sha256'], 'original_commit': plan['native_commit'],
            'canonical_untracked_source_copy_required': True, 'actual_guarded_compile_required': True,
            'actual_pre_post_census_receipts': None, 'actual_setup_import_ABI_receipt': None,
            'fresh_kernel_replay_required': True})
    audit_inputs = [{**r, 'origin': {'kind': 'reviewed_driver_plan_file',
                     'relative_path': Path(r['install_path']).name,
                     'actual_driver_commit_bound_by_stage_provenance': True}}
                    for r in [m['legacy_audit_source'], m['audit_source']]]
    audit_inputs.append({**m['inherited_T01']['audit_source'], 'module': 'T01Audit',
        'install_path': 'T01Audit.lean', 'origin': {'kind': 'git',
            'commit': m['inherited_T01']['publication_commit'],
            'path': m['inherited_T01']['repository_directory'] + '/' + m['inherited_T01']['audit_source']['path']}})
    out = {'schema': 'full87-actual-paid-I87-runtime-setup-import-acceptance-map-v3',
        'status': 'STATIC_EXPECTED_INPUTS_ONLY_ACTUAL_RUNTIME_RECEIPTS_PENDING',
        'source_commit': m['frozen_source_parent'], 'source_identity_sha256': m['targets'][0]['source_identity_sha256'],
        'producer_commit': m['inherited_T01']['publication_commit'], 'producer_run_id': '42753193835',
        'producer_job_id': '129621380109', 'artifact_id': None, 'artifact_digest': None,
        'accepted_objects': [], 'compiled': False, 'kernel_verified': False,
        'declared_toolchain_and_configuration': {'toolchain': m['toolchain'], 'mathlib': m['mathlib_rev'],
            'native': m['native_rev'], 'configuration': m['configuration'],
            'lakefile': m['inherited_T01']['project_lakefile'],
            'source_flags': m['source_elaboration_resource_options']},
        'actual_runtime_ABI_identity': None,
        'actual_runtime_gate_requirements': [
            'Independently bind immutable producer artifact ID/digest and actual CHECKPOINT/RAW_FILES content-addressed payloads; no v2 log/object inference.',
            'Require actual producing successful output-bound guarded compile candidate, nonquarantine, complete source/config/data pins and runtime audit.',
            'Rebind exact compiler/toolchain/Lake binaries, platform/architecture, native/system ABI, toolchain shared libraries and all loaded plugins from producer and consumer; revision and declared flags alone do not prove equality.',
            'Bind each actual guarded command and output to canonical source bytes, exact setup file and all imported source/object facets (private/server/IR/native/plugin and package facets included). Compare actual flags/trust/recursion/heartbeat options.',
            'Every actual IO read must map to an exact allowed source/data input or separately approved pinned package/runtime input. Declared direct data consumers below are not substituted for actual read observations.',
            'Resolve actual full transitive external imports from compiler setup/runtime, including ordinary mathlib reacquisition and exact facet hash equality; the static direct import list is not a runtime read trace.',
            'Reject contradictory Lake descriptor/sidecar hashes; absent sidecar needs verified cryptographic rebind, never receipt synthesis. Actual changed imported facet recursively invalidates all dependants.',
            'Require observed project pre/post source receipts and native43 installation/postcompile receipts bound by independent hashes and same run/commit/environment; post verification never repairs sources.',
            'Build unmatched/invalidated actual active modules only after real artifact evaluation; inventory-only sources are not force-compiled. Fresh kernel set and all full type/axiom gates remain mandatory even for reused objects.'],
        'project_module_inputs': per_module, 'compile_time_data_inputs': list(data.values()),
        'original_94_npz_receipts': m['release_npz_container_receipts'],
        'official_release_asset': m['release_asset'], 'native43_source_inputs': native,
        'audit_source_inputs': audit_inputs, 'type_targets': desc(read(HERE / 'PRINT_TARGETS.json')),
        'actual_kernel_module_set': m['fresh_kernel_modules'],
        'kernel_module_set_sha256': m['fresh_kernel_module_set_sha256'],
        'mandatory_legacy_kernel_module_set_sha256': m['mandatory_legacy_kernel_module_set_sha256'],
        'counts': {'project_modules': len(per_module), 'native_original_sources': len(native),
                   'data_inputs': len(data), 'potential_source_matches_only': len(candidates),
                   'fresh_or_unmatched_source_modules': len(active - candidates), 'fresh_kernel': len(m['fresh_kernel_modules'])}}
    save('RUNTIME_SETUP_IMPORT_ACCEPTANCE_MAP.json', out)
    authority = json.loads(read(WORKSPACE / 'output/t-batch-20261110/READY_FULL87_PUBLICATION.json'))
    same, changed = [], []
    for r in authority['actual_import_closure']['modules']:
        selected = rows[r['module']]
        if selected['sha256'] == r['sha256']:
            same.append(r['module'])
        else:
            changed.append({'module': r['module'], 'authority_sha256': r['sha256'],
                            'selected_sha256': selected['sha256'], 'selected_origin': selected['origin'],
                            'transform': selected.get('transform', []), 'semantic_group': selected.get('semantic_group')})
    if len(same) != 1021 or len(changed) != 25:
        raise ValueError('Original1046 byte comparison changed')
    save('CORE_SELECTION_BYTE_COMPARISON.json', {'schema': 'full87-fixed1046-byte-comparison-v3',
        'authority_sha256': m['authority']['sha256'], 'original_selection_names_retained': 1046,
        'same_bytes': same, 'changed_bytes': changed, 'same_count': 1021, 'changed_count': 25,
        'interpretation': 'The1046 names remain fixed. The21 inherited approved repairs/compatibility edits and four R17 semantic replacements change25 original source bytes. No claim that all1046 are byte-identical.'})
    print(json.dumps(out['counts']))


if __name__ == '__main__':
    main()
