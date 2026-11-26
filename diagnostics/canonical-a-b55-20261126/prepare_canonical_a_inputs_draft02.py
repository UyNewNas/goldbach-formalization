"""Freeze only local evidence inputs for a publication draft; no remote or Git writes."""
from pathlib import Path
import base64
import gzip
import hashlib
import json

ROOT = Path('/tmp/p24-integration-repairs-20261126')
RAW_B = Path('/tmp/p24-b-rfl-diagnostic-20261126')
SHAPE = Path('/tmp/p24-canonical-A-shape-evidence-20261126')
RET = Path('/tmp/p24-diagnostic-metadata-retention-20261126')
SER = Path('/tmp/p24-current322-serialized-names-b55-20261126')
LOGPOINT = Path('/tmp/p24-receipt-duplicates-b55-20261126/logpoint-candidate-01')
SIX = Path('/tmp/p24-global-duplicate-repairs-b55-20261126')
PREPARED = ROOT / 'canonical-a-draft02-prepared-inputs'
PREFIX = 'docs/source-only/20261125-p24-original-compact/canonical-a-b55'
DIAG = 'diagnostics/canonical-a-b55-20261126'
SOURCE = 'b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
PARENT = '12eefd99552b6a8540600a6334383d9724ec3c17'
TREE = 'f1f520791707ef604a94b2b7e6ef2620875a5f23'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_bytes())


def write_new_json(path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()
    with Path(path).open('xb') as stream:
        stream.write(raw)
    return {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


root_observation_path = ROOT / 'canonical-a-publication-observed-tasks.json'
root_observation_raw = root_observation_path.read_bytes()
observed = json.loads(root_observation_raw)
assert observed['source_pin'] == SOURCE and observed['publication_parent'] == PARENT
assert observed['current_native_environment']['acceptance_readiness'] == 'blocked'
observed['as_of_utc'] = observed['observed_at_utc']
observed['root_observation_original'] = {'path': str(root_observation_path),
    'bytes': len(root_observation_raw), 'sha256': sha(root_observation_raw)}
observed['adaptation'] = 'Add as_of_utc alias required by the existing builder; preserve all original observation fields.'
write_new_json(ROOT / 'canonical-a-publication-observed-tasks-draft02.json', observed)

native_raw_gz = (RAW_B / 'native-missing-complete-inventory.json.gz').read_bytes()
assert len(native_raw_gz) == 2034654 and sha(native_raw_gz) == '371180d13bcfc651df35e9712dba3b1ce6a1bc1aa5ad1020f33e18fd0b836a57'
native_raw = gzip.decompress(native_raw_gz)
assert len(native_raw) == 14064089 and sha(native_raw) == '297f3c77f8494ac78ba5694872bf214b464bea3c601404fa2a0bf61f3251f505'
inventory = json.loads(native_raw)
assert inventory['counts'] == {'missing': 41505, 'present_same_size': 28878}
assert inventory['source_pin'] == SOURCE
assert sum(row['expected']['bytes'] for row in inventory['mismatches']) == 5712781792
native_observation = {
    'schema': 1, 'as_of_utc': observed['as_of_utc'], 'source_pin': SOURCE,
    'current_acceptance_readiness': 'blocked_native_physical_inputs_missing',
    'qualified_snapshot_bytes': 20904189,
    'qualified_snapshot_sha256': inventory['snapshot_sha256'],
    'registry_sha256_at_inventory': inventory['registry_sha256'],
    'expected_physical_files': 70383, 'missing_physical_files': 41505,
    'missing_expected_bytes': 5712781792,
    'all_missing_under': '/workspace/compile-deps/mathlib/',
    'present_at_expected_size_not_rehashed': 28878,
    'whnf_task_id': '2ed7d836789347e1be94c3a543745489',
    'whnf_lean_executed': False,
    'whnf_failed_gate': 'original ExternalSnapshot.verify',
    'inventory_task_id': '9206f22b0b8741b8b41e91e334fc9eca',
    'official_cache_probe_task_id': 'd61bbe8cdf374c8eb298fe462cd6381a',
    'official_cache_probe_result': 'network tunnel 403 for both GET requests',
    'official_cache_absence_or_http_404_inferred': False,
    'access_restriction_bypass_attempted': False,
    'replacement_qualification_performed': False,
    'environment_restoration_performed': False,
    'cause_attributed': False,
    'directory_timestamp_is_not_deletion_time_or_attribution': True,
    'released_by_reviewed_metadata_workflow': False,
    'original_files_released_by_metadata_workflow': 0,
    'reported_new_free_bytes_credited_as_safe_capacity': False,
    'historical_pass_receipts_preserved_at_original_execution_times': True,
    'evidence_paths': [str(RAW_B / name) for name in [
        'whnf-b55-draft01-precheck-failure.log', 'whnf-b55-draft01-precheck-failure-task.json',
        'native-input-missing-inventory-01.log', 'native-input-missing-inventory-01-task.json',
        'native-input-missing-inventory-01-summary.json', 'native-missing-complete-inventory.json.gz',
        'native-missing-complete-inventory-blob.json', 'native-official-cache-index-probe-01.log',
        'native-official-cache-index-probe-01-task.json']],
}
write_new_json(ROOT / 'native-environment-block-observation-draft02.json', native_observation)

# Represent the six redundant native transport files exactly, without embedding base64 twice.
native_transport_rows = []
for index in range(3):
    basename = f'native-missing-transport-part-{index:03d}'
    raw_log = (RAW_B / (basename + '.log')).read_bytes()
    first, second = raw_log.splitlines(keepends=True)
    marker = b'P24_NATIVE_MISSING_CHUNK '
    assert first.startswith(marker)
    item = json.loads(first[len(marker):])
    chunk = native_raw_gz[item['offset']:item['offset'] + item['bytes']]
    assert len(chunk) == item['bytes'] and sha(chunk) == item['sha256']
    encoded = base64.b64encode(chunk) + b'\n'
    assert (RAW_B / (basename + '.base64')).read_bytes() == encoded
    assert second == b'P24_CHUNK_BASE64 ' + encoded
    native_transport_rows.append({
        'chunk': item, 'header_line_utf8_exact': first.decode(),
        'base64_file': {'path': str(RAW_B / (basename + '.base64')), 'bytes': len(encoded), 'sha256': sha(encoded)},
        'stdout_file': {'path': str(RAW_B / (basename + '.log')), 'bytes': len(raw_log), 'sha256': sha(raw_log)},
        'formula': 'header_line_utf8_exact.encode() + b"P24_CHUNK_BASE64 " + base64.b64encode(whole_gzip[offset:offset+bytes]) + b"\\n"',
    })
write_new_json(PREPARED / 'native-missing-transport-reconstruction.json', {
    'schema': 1, 'whole_gzip_bytes': len(native_raw_gz), 'whole_gzip_sha256': sha(native_raw_gz),
    'git_blob_sha': '0b555e12f6ec71d0f4f842f857d4ea64d04049df',
    'parts': native_transport_rows, 'all_six_original_transport_files_compared_byte_for_byte': True,
    'originals_deleted_or_modified': False, 'original_page_offsets_and_statuses_retained_separately': True,
})

items = []
seen_origins, seen_targets = set(), set()


def add(path, target, role):
    path = Path(path)
    assert path.is_file(), path
    assert str(path) not in seen_origins, path
    assert target not in seen_targets, target
    raw = path.read_bytes()
    assert raw.decode('utf-8').encode('utf-8') == raw
    seen_origins.add(str(path))
    seen_targets.add(target)
    items.append({'origin': str(path), 'target': target, 'bytes': len(raw), 'sha256': sha(raw), 'role': role})


def named(directory, names, prefix, role):
    for name in names:
        add(Path(directory) / name, prefix + '/' + name, role)


# Freeze known top-level evidence once. The builder only reads the resulting explicit list.
excluded = {'strict321-transfer-0.txt', 'strict321-transfer-1.txt',
            'canonical-a-publication-draft02-inputs.json'}
allowed_extensions = {'.json', '.log', '.py', '.sh', '.md', '.patch', '.lean'}
for path in sorted(ROOT.iterdir()):
    if path.is_file() and path.name not in excluded and path.suffix in allowed_extensions:
        prefix = DIAG if path.suffix in {'.py', '.sh', '.patch', '.lean'} else PREFIX
        add(path, prefix + '/' + path.name, 'historical actual evidence or explicitly labelled prepared workflow')

for folder in ['a-capacity-diagnostic', 'storage-readonly', 'a-canonical-owned', 'a-block-shape']:
    directory = ROOT / folder
    if not directory.exists():
        continue
    for path in sorted(directory.rglob('*')):
        if path.is_file() and path.suffix in allowed_extensions:
            add(path, PREFIX + '/' + folder + '/' + path.relative_to(directory).as_posix(),
                'frozen actual diagnostic evidence or unexecuted original-gate workflow; status determined only by receipts')

named(SHAPE, [
    'InspectBlocks.lean', 'blocks-stdout-blob.json', 'github-create-blob-response.json',
    'evidence-files-manifest.json', 'local-validation-attempt-001.json',
    'metadata-command.sh', 'metadata-submission.json', 'metadata-task-status.json',
    'original-shape-task-status.json', 'original-shape-task.log', 'read-api-invalid-argument-history.json',
    'remote-files-descriptor.json', 'retrieval-verification.json', 'shape-diagnostic.json', 'verify_retrieved_evidence.py',
], PREFIX + '/shape', 'actual complete shape evidence and byte-verified retrieval history; no full-owned/replay credit')
for index in range(8):
    for suffix in ['command.sh', 'submission.json', 'task-status.json', 'metadata.json']:
        filename = f'chunk-{index:02d}-{suffix}'
        add(SHAPE / 'chunks' / filename, PREFIX + '/shape/chunks/' + filename,
            'actual bounded read-only retrieval; stdout/binary/page duplicates are represented reversibly')
for path in sorted(PREPARED.iterdir()):
    if path.is_file():
        add(path, PREFIX + '/transport-maps/' + path.name,
            'exact reversible transport representation; all original bytes retained and independently compared')

named(RET, ['conditional-metadata-consumer-analysis.md', 'final-export-tmpfs-retention-design.md',
    'original-migrate-winner9-private-snapshot.py', 'original-run-winner9-private-checks.py',
    'original-winner9-external-snapshot.py', 'draft01-code-freeze.json', 'local-validation.json', 'plan.md'],
    PREFIX + '/metadata-retention', 'read-only consumer analysis or frozen preparation; three conditional metadata files remain excluded')
for path in sorted((RET / 'draft02').iterdir()):
    if path.is_file() and path.suffix in allowed_extensions:
        add(path, PREFIX + '/metadata-retention/draft02/' + path.name,
            'stage1 and verification-only actual evidence; release code is prepared and automatic approval blocked, no release task')

named(RAW_B, [
    'P24CachedEndpointRawDefEqDiagnostic.lean', 'p2-B-raw-defeq-b55-draft01.py',
    'p2-B-raw-defeq-b55-draft01.sh', 'raw-defeq-wrapper-draft01-manifest.json',
    'raw-defeq-execution-tail-draft01.py', 'build-raw-defeq-wrapper-draft01.py',
    'raw-defeq-b55-submission.json', 'raw-defeq-b55-final.log',
    'raw-defeq-b55-final-task.json', 'raw-defeq-b55-final-summary.json',
    'pinned-evidence-index.json', 'readonly-analysis-draft01.md', 'static-verification-draft01.json',
    'P24CachedEndpointWhnfDiagnostic.lean', 'p2-B-whnf-b55-draft01.py', 'p2-B-whnf-b55-draft01.sh',
    'build-whnf-wrapper-draft01.py', 'raw-false-to-whnf-handoff.json',
    'raw-to-whnf-wrapper-draft01-review.patch', 'whnf-wrapper-draft01-manifest.json',
    'whnf-b55-submission.json', 'whnf-b55-draft01-precheck-failure.log',
    'whnf-b55-draft01-precheck-failure-task.json', 'whnf-draft01-preflight-failure-state.json',
    'mathlib-input-incident-readonly-01.sh', 'mathlib-input-incident-readonly-01.log',
    'mathlib-input-incident-readonly-01-task.json',
    'native-input-missing-inventory-01.sh', 'native-input-missing-inventory-01.log',
    'native-input-missing-inventory-01-task.json', 'native-input-missing-inventory-01-summary.json',
    'native-missing-complete-inventory-blob.json', 'native-missing-transport-descriptors.json',
    'native-missing-transport-local-verification.json', 'native-missing-transport-submissions.json',
    'native-missing-transport-tasks.json', 'native-recovery-cache-probe-01.sh',
    'native-recovery-cache-probe-01.log', 'native-recovery-cache-probe-01-task.json',
    'native-official-cache-index-probe-01.sh', 'native-official-cache-index-probe-01.log',
    'native-official-cache-index-probe-01-task.json',
], PREFIX + '/B-and-native-incident',
    'actual raw-B observation / WHNF preflight rejection / read-only native incident evidence; no B result or new qualification')

named(LOGPOINT, [
    'P2HistoricLogPointInterpreter-contains-change-01.lean', 'P2HistoricLogPointInterpreter-original-b55.lean',
    'build-diagnostic.py', 'contains-change-01.patch', 'exact-proof-replacement.json',
    'isolated-diagnostic-manifest.json', 'isolated-submission.json',
    'logpoint-candidate-b55-final-summaries.json', 'logpoint-candidate-b55-final-summary.json',
    'logpoint-candidate-b55-final-task.json', 'logpoint-candidate-b55-final.log',
    'p2-logpoint-contains-change-01.py', 'p2-logpoint-contains-change-01.sh',
    'publication-files.json', 'scope-natrec-to-contains-wrapper.patch', 'selected-evidence-and-source-rationale.json',
], PREFIX + '/isolated-logpoint', 'actual isolated proof-only candidate PASS; no production promotion or canonical gate credit')
named(SER, [
    'SerializedNames.template.lean', 'build-draft01.py', 'draft01-independent-review.json',
    'draft01-manifest.json', 'p2-current322-serialized-names-b55-draft01.py',
    'p2-current322-serialized-names-b55-draft01.sh', 'scanner-tail-draft01.py',
    'serialized322-b55-final-summaries.json', 'serialized322-b55-final-task.json',
    'serialized322-b55-final.log', 'serialized322-b55-submission.json',
    'three-diagnostic-evidence-blob.json', 'three-diagnostic-transport-01.sh',
    'three-diagnostic-transport-descriptor.json', 'three-diagnostic-transport-final-task.json',
    'three-diagnostic-transport-local-verification.json',
], PREFIX + '/serialized322', 'actual serialized duplicate scan and complete three-diagnostic transport; no original-owned acceptance')

six = read_json(SIX / 'candidates-01/six-proof-candidates-manifest.json')
named(SIX, ['minimum-repair-set-and-source-dependencies.json'], PREFIX + '/prepared-six-proof-candidates',
      'read-only minimal candidate/dependency plan, not executed or promoted')
named(SIX / 'candidates-01', ['six-proof-candidates-manifest.json', 'root-static-review.json'],
      PREFIX + '/prepared-six-proof-candidates', 'static review of six prepared candidates; no compile credit')
for row in six['candidates']:
    for key, group in [('original_path', 'originals'), ('candidate_path', 'candidates'), ('patch_path', 'patches')]:
        path = Path(row[key])
        add(path, DIAG + '/prepared-six-proof-candidates/' + group + '/' + path.name,
            'diagnostic source copy only; original public statements unchanged, prepared candidate not compiled/promoted')

original = ROOT / 'build_canonical_a_publication.py'
plan = {'schema': 1, 'source_pin': SOURCE, 'parent_sha': PARENT, 'base_tree_sha': TREE,
    'original_builder': {'path': str(original), 'bytes': original.stat().st_size, 'sha256': sha(original.read_bytes())},
    'as_of_utc': observed['as_of_utc'], 'text_inputs': items,
    'reversible_transport_views': [
        {'map': PREFIX + '/transport-maps/' + name,
         'local_origin': str(PREPARED / name), 'sha256': sha((PREPARED / name).read_bytes())}
        for name in ['shape-transport-reconstruction.json', 'three-diagnostic-transport-reconstruction.json',
                     'native-missing-transport-reconstruction.json']],
    'no_future_files_auto_discovered_by_builder': True,
    'originals_deleted_or_modified': False, 'remote_jobs_or_git_mutations_performed': False,
    'current_native_environment': 'blocked; historical PASS receipts do not requalify current physical inputs',
}
result = write_new_json(ROOT / 'canonical-a-publication-draft02-inputs.json', plan)
print(json.dumps({'text_input_count': len(items), 'raw_input_bytes': sum(x['bytes'] for x in items),
                  'input_plan': result, 'no_remote_or_git_operations': True}, sort_keys=True))
