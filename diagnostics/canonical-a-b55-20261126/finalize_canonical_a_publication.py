from pathlib import Path
import hashlib
import json

ROOT = Path('/tmp/p24-integration-repairs-20261126')
BASE = ROOT / 'canonical-a-publication-draft02'
OUT = ROOT / 'canonical-a-publication-final'
PREFIX = 'docs/source-only/20261125-p24-original-compact/canonical-a-b55'
MANIFEST_PATH = 'docs/source-only/20261125-p24-original-compact/p24-canonical-a-b55-publication-files-20261126.json'
STATE_PATH = 'docs/source-only/20261125-p24-original-compact/p24-canonical-a-b55-checkpoint-20261126.json'
BASE_TREE_SHA256 = '31ca52963d7804dee5f517b346289571e4363ade3422fde455d1a384676b8cfd'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()

tree_bytes = (BASE / 'tree.json').read_bytes()
assert sha(tree_bytes) == BASE_TREE_SHA256
tree = json.loads(tree_bytes)
manifest = json.loads((BASE / 'publication-files.json').read_bytes())
state = json.loads((BASE / 'state.json').read_bytes())
assert manifest['parent_sha'] == '12eefd99552b6a8540600a6334383d9724ec3c17'
assert manifest['base_tree_sha'] == 'f1f520791707ef604a94b2b7e6ef2620875a5f23'
assert manifest['production_files_changed'] == []
assert len(tree) == 312
entries = {r['path']: r for r in tree}
records = {r['path']: r for r in manifest['files']}
assert len(entries) == 312 and len(records) == 311
assert set(entries) == set(records) | {MANIFEST_PATH}

for name, r in records.items():
    e = entries[name]
    b = Path(r['origin']).read_bytes()
    assert len(b) == r['bytes'] and sha(b) == r['sha256'], name
    assert e['mode'] == '100644' and e['type'] == 'blob'
    if 'content' in e:
        assert e['content'].encode() == b, name
    else:
        assert e['sha'] == r['git_blob_sha']
        assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == e['sha']

OUT.mkdir(exist_ok=False)
added = []

def add(origin, target, role):
    p = Path(origin)
    b = p.read_bytes()
    assert target not in entries and target not in records, target
    entries[target] = {'path': target, 'mode': '100644', 'type': 'blob', 'content': b.decode('utf-8')}
    records[target] = {'path': target, 'bytes': len(b), 'sha256': sha(b), 'origin': str(p), 'role': role}
    added.append(target)

inputs = [
    (BASE / 'local-publication-review.json', PREFIX + '/reviews/local-publication-review.json', 'Completed local verification of frozen draft02; no new proof credit'),
    (BASE / 'original-to-draft02.patch', 'diagnostics/canonical-a-b55-20261126/original-to-draft02.patch', 'Exact publication-builder change history'),
    (ROOT / 'canonical-a-publication-draft02-independent-review-scope.json', PREFIX + '/reviews/independent-publication-review-scope.json', 'Independent read-only review of frozen draft02'),
    (Path('/tmp/p24-global-duplicate-repairs-b55-20261126/review-six-isolated-wrappers-design-01.json'), PREFIX + '/reviews/six-isolated-wrappers-design-review.json', 'Independent static review; six wrappers remain unexecuted'),
    (Path('/tmp/p24-global-duplicate-repairs-b55-20261126/review-lower-b55/design-two-candidates-review.json'), PREFIX + '/reviews/two-proof-candidates-design-review.json', 'Independent static review only; not Lean execution'),
    (Path('/tmp/p24-native-recovery-readonly-20261126/exact-native-restoration-design-v02.md'), PREFIX + '/native-restoration-prepared/exact-native-restoration-design-v02.md', 'Prepared restoration design; existing authorization clarified; network still blocked'),
    (Path('/tmp/p24-native-recovery-readonly-20261126/prepared-only-verification-v02.json'), PREFIX + '/native-restoration-prepared/prepared-only-verification-v02.json', 'Prepared-only v02 evidence bindings; no restoration performed'),
    (Path('/tmp/p24-native-recovery-readonly-20261126/exact-native-restoration-design-v01-to-v02.patch'), PREFIX + '/native-restoration-prepared/exact-native-restoration-design-v01-to-v02.patch', 'One-sentence authorization clarification; v01 retained'),
]
for origin, target, role in inputs:
    add(origin, target, role)
for suffix in ['.sh', '.log', '-task.json', '-summary.json']:
    name = 'final-environment-observation-01' + suffix
    add(Path('/tmp/p24-b-rfl-diagnostic-20261126') / name,
        PREFIX + '/native-input-incident/' + name,
        'Final read-only observation; same frozen source/registry/snapshot and missing Mathlib directory')

observation = json.loads(Path('/tmp/p24-b-rfl-diagnostic-20261126/final-environment-observation-01-summary.json').read_text())
assert observation['source_pin'] == state['source_pin']
assert observation['registry_sha256'] == '3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445'
assert observation['snapshot_sha256'] == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
assert observation['tracked_status'] == ''
assert observation['Mathlib_ir_exists'] is False and observation['mathlib_build_lib_exists'] is False
assert observation['files_written'] == 0 and observation['qualification_repeated'] is False
state['final_readonly_environment_observation'] = observation
old_design = state['exact_native_restoration_design'].copy()
new_verification = Path('/tmp/p24-native-recovery-readonly-20261126/prepared-only-verification-v02.json')
state['exact_native_restoration_design'].update({
    'verification_path': str(new_verification),
    'verification_sha256': sha(new_verification.read_bytes()),
    'design_repo_path': PREFIX + '/native-restoration-prepared/exact-native-restoration-design-v02.md',
    'prior_v01_binding_retained': old_design,
    'existing_continue_authorization_requires_no_reconfirmation': True,
    'network_access_restrictions_unchanged': True,
})
state['independent_publication_review_paths'] = [
    PREFIX + '/reviews/local-publication-review.json',
    PREFIX + '/reviews/independent-publication-review-scope.json',
]
for flag in ['canonical_B_compile_complete', 'canonical_W_compile_complete',
             'full324_canonical_owned_audit_complete', 'final_original_export_complete',
             'P2_4_complete', 'P2_complete', 'main_theorem_complete', 'claim_6_809']:
    assert state[flag] is False, flag
assert state['current_acceptance_readiness'] == 'blocked_native_physical_inputs_missing'
state_bytes = encoded(state)
(OUT / 'state.json').write_bytes(state_bytes)
entries[STATE_PATH]['content'] = state_bytes.decode()
records[STATE_PATH].update(bytes=len(state_bytes), sha256=sha(state_bytes), origin=str(OUT / 'state.json'))
add(Path(__file__), 'diagnostics/canonical-a-b55-20261126/finalize_canonical_a_publication.py',
    'Local deterministic final overlay; no remote jobs or Git writes')

assert all(p.startswith(('docs/', 'diagnostics/')) for p in entries)
assert all(e.get('mode') == '100644' and e.get('type') == 'blob' for e in entries.values())
assert all(('content' in e) != ('sha' in e) for e in entries.values())
assert len([e for e in entries.values() if 'sha' in e]) == 4
for name, r in records.items():
    b = Path(r['origin']).read_bytes()
    assert len(b) == r['bytes'] and sha(b) == r['sha256'], name
    if 'content' in entries[name]:
        assert entries[name]['content'].encode() == b, name

review = {
    'status': 'PASS',
    'base_tree_json_sha256': BASE_TREE_SHA256,
    'parent_sha': manifest['parent_sha'],
    'base_tree_sha': manifest['base_tree_sha'],
    'all_base_311_origins_rechecked_against_tree_content_or_binary_blob': True,
    'all_added_origins_rechecked': True,
    'all_four_binary_blob_ids_independently_recomputed': True,
    'two_independent_base_publication_reviews_passed': True,
    'production_paths_changed': [],
    'candidate_sources_and_wrappers_remain_unexecuted_and_unpromoted': True,
    'v02_restoration_change_is_authorization_wording_only': True,
    'current_native_environment_still_blocked_at_final_readonly_observation': True,
    'original_source_registry_and_snapshot_sha256_unchanged_at_final_observation': True,
    'final_observed_at_utc': observation['observed_at_utc'],
    'previously_reviewed_evidence_and_diagnostic_entries_unchanged_except_state_and_manifest': True,
    'new_proof_or_qualification_credit': False,
    'P2_4_complete': False,
    'added_before_this_review': added,
}
review_path = OUT / 'root-final-review.json'
review_path.write_bytes(encoded(review))
add(review_path, PREFIX + '/reviews/root-final-publication-review.json',
    'Root final overlay integrity verification; no new proof credit')
manifest['files'] = list(records.values())
manifest['files_count_without_manifest_itself'] = len(records)
manifest['final_overlay'] = {
    'base_draft02_tree_json_sha256': BASE_TREE_SHA256,
    'base_draft02_manifest_sha256': sha((BASE / 'publication-files.json').read_bytes()),
    'added_paths': added,
    'updated_existing_paths': [STATE_PATH, MANIFEST_PATH],
    'unchanged_production_sources': True,
    'latest_environment_observation_utc': observation['observed_at_utc'],
    'current_acceptance_readiness': state['current_acceptance_readiness'],
}
manifest_bytes = encoded(manifest)
(OUT / 'publication-files.json').write_bytes(manifest_bytes)
entries[MANIFEST_PATH]['content'] = manifest_bytes.decode()
final_tree = list(entries.values())
assert len(final_tree) == len(records) + 1
final_bytes = encoded(final_tree)
(OUT / 'tree.json').write_bytes(final_bytes)
for name in ['p24-memory-and-audit-checkpoint-20261126.md', 'p24-source-node-blocks-promotion-20261126.md']:
    (OUT / name).write_bytes((BASE / name).read_bytes())
descriptor = {
    'tree_entries': len(final_tree), 'tree_json_bytes': len(final_bytes),
    'tree_json_characters': len(final_bytes.decode()),
    'tree_json_sha256': sha(final_bytes), 'manifest_sha256': sha(manifest_bytes),
    'state_sha256': sha(state_bytes), 'production_files_changed': [],
    'parent_sha': manifest['parent_sha'], 'base_tree_sha': manifest['base_tree_sha'],
    'binary_blobs': 4, 'text_entries': len(final_tree) - 4,
    'current_acceptance_readiness': state['current_acceptance_readiness'],
}
(OUT / 'descriptor.json').write_bytes(encoded(descriptor))
print(json.dumps(descriptor, sort_keys=True))
