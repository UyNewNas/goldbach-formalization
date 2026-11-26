from pathlib import Path
import gzip
import hashlib
import io
import json
import tarfile

ROOT = Path('/tmp/p24-integration-repairs-20261126')
OUT = ROOT / 'joint321-publication'
OUT.mkdir(exist_ok=True)
PREFIX = 'docs/source-only/20261125-p24-original-compact'
EVIDENCE = PREFIX + '/joint321-b55'
DIAGNOSTICS = 'diagnostics/joint321-b55-20261126'
PIN = 'b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
BASE_TREE = '8a7c8bb637a31199a80f585733d3c1265a602f73'
rows = []
elements = []
seen = set()

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def add_bytes(path, raw, origin, role):
    assert path not in seen, path
    seen.add(path)
    content = raw.decode('utf-8')
    assert content.encode('utf-8') == raw
    elements.append({'path': path, 'mode': '100644', 'type': 'blob', 'content': content})
    rows.append({'path': path, 'bytes': len(raw), 'sha256': sha(raw), 'origin': origin, 'role': role})

def add_file(path, source, role):
    source = Path(source)
    add_bytes(path, source.read_bytes(), str(source), role)

archives = []
for label, expected_count in [('1087', 20), ('b55', 23)]:
    archive = ROOT / ('evidence-' + label + '.tar.gz')
    raw = archive.read_bytes()
    blob = json.loads((ROOT / ('evidence-' + label + '-blob.json')).read_bytes())
    descriptor = json.loads((ROOT / ('evidence-' + label + '-descriptor.json')).read_bytes())
    local = json.loads((ROOT / ('evidence-' + label + '-local-integrity.json')).read_bytes())
    git_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert len(raw) == blob['bytes'] == descriptor['gzip_bytes']
    assert sha(raw) == blob['sha256'] == descriptor['gzip_sha256'] == local['archive_sha256']
    assert git_blob == blob['sha'] == local['archive_git_blob']
    unpacked = gzip.decompress(raw)
    assert len(unpacked) == descriptor['tar_bytes'] and sha(unpacked) == descriptor['tar_sha256']
    actual = {}
    member_bytes = {}
    with tarfile.open(fileobj=io.BytesIO(unpacked), mode='r:') as tar:
        for member in tar:
            assert member.isfile() and member.name not in actual
            data = tar.extractfile(member).read()
            actual[member.name] = {'bytes': len(data), 'sha256': sha(data)}
            member_bytes[member.name] = data
    assert len(actual) == expected_count and actual == descriptor['members']
    assert json.loads(member_bytes['FILES.json']) == {n: v for n, v in actual.items() if n != 'FILES.json'}
    receipt = json.loads(member_bytes['promotion/receipt.json'])
    assert receipt['wrapper_exit_code'] == (1 if label == '1087' else 0)
    assert receipt['original_summary']['successful_closure'] == (317 if label == '1087' else 321)
    assert receipt['postchecks'] and all(receipt['postchecks'].values()) and not receipt['postcheck_errors']
    path = EVIDENCE + '/evidence-' + label + '.tar.gz'
    assert path not in seen
    seen.add(path)
    elements.append({'path': path, 'mode': '100644', 'type': 'blob', 'sha': git_blob})
    rows.append({'path': path, 'bytes': len(raw), 'sha256': sha(raw), 'git_blob_sha': git_blob,
                 'origin': str(archive), 'role': 'complete lossless original gate evidence'})
    archives.append({'label': label, 'path': path, 'bytes': len(raw), 'sha256': sha(raw),
                     'git_blob_sha': git_blob, 'members': len(actual), 'tar_bytes': len(unpacked),
                     'tar_sha256': sha(unpacked), 'all_members_independently_verified': True})

excluded = {'strict321-transfer-0.txt', 'strict321-transfer-1.txt'}
for source in sorted(ROOT.iterdir()):
    if not source.is_file() or source.name in excluded or source.name.endswith(('.gz', '.xz', '.bin', '.b64')):
        continue
    target = (DIAGNOSTICS if source.suffix in {'.sh', '.py'} else EVIDENCE) + '/' + source.name
    add_file(target, source, 'original task evidence or explicitly labelled prepared workflow')

for label in ['1087', 'b55']:
    folder = ROOT / ('evidence-' + label + '-chunks')
    for source in sorted(folder.iterdir()):
        if source.suffix not in {'.sh', '.json'}:
            continue
        add_file(EVIDENCE + '/' + folder.name + '/' + source.name, source,
                 'bounded transport command or complete task-index metadata; archive bytes retained separately')

storage = ROOT / 'storage-readonly'
for source in sorted(storage.rglob('*')):
    if source.is_file():
        add_file(EVIDENCE + '/storage-readonly/' + source.relative_to(storage).as_posix(), source,
                 'read-only storage probe; no cleanup or capability write test')

for name, folder in [('p3-b-feasibility', Path('/tmp/p24-p3-b-feasibility-20261126')),
                     ('b-prefix-readonly-review', Path('/tmp/p24-b-prefix-readonly-review-20261126'))]:
    for source in sorted(folder.iterdir()):
        if source.is_file() and source.suffix in {'.json', '.sh', '.md', '.log', '.lean'}:
            add_file(EVIDENCE + '/' + name + '/' + source.name, source,
                     'read-only feasibility or existing uncompiled generic-prefix review; no canonical B credit')

add_file(EVIDENCE + '/proof-source-publication-refetch.json', ROOT / 'publication/published-and-refetched.json',
         'exact b55 source and manifest refetch')
summary = json.loads((ROOT / 'strict321-b55-summary.json').read_bytes())
task = json.loads((ROOT / 'strict321-b55-task.json').read_bytes())
a_progress = json.loads((ROOT / 'finite-a-b55-progress.json').read_bytes())
assert task['exit_code'] == 0 and summary['strict321_compile_passed'] is True
assert summary['original_summary']['total'] == summary['original_summary']['successful_closure'] == 321
assert summary['original_summary']['reused'] == 317
assert a_progress['task']['status'] == 'running' and a_progress['complete_task_log'] is False
state = {
    'as_of': a_progress['as_of'], 'publication_parent': PIN, 'source_pin': PIN,
    'actual_P2_pin': PIN, 'source_changes_in_this_publication': [],
    'original_full324_ordered_fingerprint': 'c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f',
    'original_strict321': {'task': task, 'final_summary_and_postchecks': summary,
        'full_stdout_bytes': 4145, 'full_stdout_sha256': sha((ROOT / 'strict321-b55.log').read_bytes()),
        'fresh_module_count': 4, 'accepted_compilation_count': 321},
    'archives': archives,
    'canonical_A': {'task_id': 'b969b7262ac5492587102cbd5b969e38', 'progress_snapshot': a_progress,
        'zero_budget321_all_reused': True, 'zero_budget321_postchecks_passed': True,
        'compile_complete_at_this_checkpoint': False, 'independent_replay_complete': False, 'owned_audit_complete': False},
    'canonical_B_compile_complete': False, 'canonical_W_compile_complete': False,
    'eleven_changed_module_canonical_owned_audit_complete': False,
    'full324_owned_audit_complete': False, 'final_original_export_complete': False,
    'P2_4_complete': False, 'P2_complete': False, 'main_theorem_complete': False, 'claim_6_809': False,
    'storage': {'latest_readonly_probe_task': 'c6de65f940764b889e845ede03c4c454',
        'probe_free_bytes': 379904000, 'required_reserve_bytes': 33554432,
        'measured_P3_full2048_original_three_file_serialization_bytes': 510596115,
        'canonical_A_actual_size_still_requires_measurement': True,
        'probe_free_vs_anchor_plus_reserve_deficit_bytes': 164246547,
        'cleanup_executed': False, 'filesystem_capability_write_tests_executed': False,
        'native_sources_objects_actual_audit_logs_preserved': True},
}
state_raw = (json.dumps(state, ensure_ascii=False, indent=2) + '\n').encode()
(OUT / 'state.json').write_bytes(state_raw)
add_bytes(PREFIX + '/p24-joint321-b55-checkpoint-20261126.json', state_raw, str(OUT / 'state.json'), 'current bounded acceptance state')

block = f'''# Current checkpoint: original strict321 PASS at b55

As of **{a_progress['as_of']}**, the canonical P2 worktree is pinned to `{PIN}`.
This checkpoint adds evidence only; it does not change production Lean sources.

The original 321-module gate, task `caeb84c54d744748a036826b55c6126c`, finished with **exit 0**:
321/321 successful, 317 reused and four freshly compiled modules. The four fresh modules are
Reachability (22.938 s), CompleteSoundness (6.898 s), CachedRun (9.337 s), and FixedBindings
(17.067 s). The original driver reported 125.554 s; the outer task took 251.054163 s.
All seven normal postchecks passed, including original `verify_compilation`, the complete
324-source/order binding, unchanged toolchain/native inputs, and unchanged unselected
A/B/W objects and records. The current compile registry SHA-256 is
`1c192905bcca6461d0d4aca1433498f7d1ec0bcb9a1a55dbcbe230e3f57badbc`.

Both the previous 1087 failure and the b55 success have complete lossless archives under
`joint321-b55/`, with 20 and 23 members respectively. Every member and the FILES index
were independently checked after bounded retrieval. The earlier clipped 2 MiB transport
prefix remains explicitly marked truncated; it is not a substitute for either complete archive.

Canonical A revalidation is **running**, task `b969b7262ac5492587102cbd5b969e38`.
Its original zero-budget 321 prerequisite gate passed with all 321 reused and all postchecks;
the original A102/3000-second gate has started, but no final A result is claimed here.
Prepared B and eleven-module owned-audit wrappers retain the original resource envelopes,
full scope, runtime/native bindings, complete owned/type output, and failure postchecks.
They have not been executed at this checkpoint.

Storage remains an unresolved execution constraint for the full audit. The latest read-only
probe measured 379,904,000 free bytes. The actual P3 full2048 output serialized by the original
audit format occupies 510,596,115 bytes across audit.log, declarations.json, and types.txt;
canonical A still needs its own measurement. Against that measured anchor plus the existing
32 MiB reserve, the deficit is 164,246,547 bytes, before other audits or final archive retention.
No cleanup, filesystem capability write test, source/object/native removal, or actual audit-log
removal was performed. Other projects' files are outside the cleanup scope.

**P2.4 is not complete:** canonical A replay/full-owned, B, W, final full324 owned selection,
and the unchanged original complete export remain outstanding. This checkpoint provides
no full P2, main-theorem, or 6.809 claim.

The earlier checkpoints below are historical records; their pending/failed states describe
their own timestamps and must not be read as the current strict321 state.

---

'''
for name in ['p24-memory-and-audit-checkpoint-20261126.md', 'p24-source-node-blocks-promotion-20261126.md']:
    source = ROOT / 'publication' / name
    raw = block.encode() + source.read_bytes()
    (OUT / name).write_bytes(raw)
    add_bytes(PREFIX + '/' + name, raw, str(OUT / name), 'main checkpoint with bounded current results and retained history')

assert all(e['path'].startswith(('docs/', 'diagnostics/')) for e in elements)
manifest = {'parent_sha': PIN, 'base_tree_sha': BASE_TREE, 'production_files_changed': [],
            'files': rows, 'files_count_without_manifest_itself': len(rows),
            'complete_gate_evidence_archives_independently_verified': True,
            'A_progress_is_not_completion_credit': True, 'full_P2_4_complete': False}
raw = (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode()
(OUT / 'publication-files.json').write_bytes(raw)
add_bytes(PREFIX + '/p24-joint321-b55-publication-files-20261126.json', raw,
          str(OUT / 'publication-files.json'), 'publication manifest; excludes itself to avoid recursion')
(OUT / 'tree.json').write_text(json.dumps(elements, ensure_ascii=False, separators=(',', ':')) + '\n')
print(json.dumps({'tree_entries': len(elements), 'tree_bytes': (OUT / 'tree.json').stat().st_size,
                  'manifest_sha256': sha(raw), 'state_sha256': sha(state_raw),
                  'binary_archive_count': len(archives), 'production_files_changed': []}))
