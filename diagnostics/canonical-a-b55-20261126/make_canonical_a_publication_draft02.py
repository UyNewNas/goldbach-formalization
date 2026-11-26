"""Prepare a new local-only publication builder; never execute Git or remote work."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT = Path('/tmp/p24-integration-repairs-20261126')
ORIGINAL = ROOT / 'build_canonical_a_publication.py'
TARGET = ROOT / 'build_canonical_a_publication_draft02.py'
EXTRA = ROOT / 'canonical_a_draft02_extra_validation.py'


def replace_once(text, old, new):
    assert text.count(old) == 1, old[:100]
    return text.replace(old, new, 1)


text = ORIGINAL.read_text()
original_sha = hashlib.sha256(ORIGINAL.read_bytes()).hexdigest()
text = replace_once(text, 'import json\n', 'import json\nimport base64\nimport gzip\nimport io\nimport lzma\nimport tarfile\n')
text = replace_once(text, "OUT = ROOT / 'canonical-a-publication'", "OUT = ROOT / 'canonical-a-publication-draft02'")
text = replace_once(text, 'OUT.mkdir(exist_ok=True)', 'OUT.mkdir(exist_ok=False)')
start = text.index("previous = json.loads((ROOT / 'joint321-publication/publication-files.json').read_bytes())")
end = text.index("for name in ['independent-publication-review.json', 'published-and-refetched.json']:")
text = text[:start] + '''input_plan_path = ROOT / 'canonical-a-publication-draft02-inputs.json'
input_plan = json.loads(input_plan_path.read_bytes())
assert sha((ROOT / 'build_canonical_a_publication.py').read_bytes()) == input_plan['original_builder']['sha256']
assert input_plan['source_pin'] == SOURCE and input_plan['parent_sha'] == PARENT and input_plan['base_tree_sha'] == BASE_TREE
previous = json.loads((ROOT / 'joint321-publication/publication-files.json').read_bytes())
previous_by_origin = {r['origin']: r for r in previous['files']}
previous_references = []
for item in input_plan['text_inputs']:
    source = Path(item['origin'])
    raw = source.read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], source
    if str(source) in previous_by_origin:
        old = previous_by_origin[str(source)]
        assert old['bytes'] == len(raw) and old['sha256'] == sha(raw)
        previous_references.append({'origin': str(source), 'published_path': old['path'], 'sha256': sha(raw)})
        continue
    add(item['target'], raw, source, item['role'])
add_file(DIAGNOSTICS + '/publication-input-plan-draft02.json', input_plan_path,
         'explicit frozen input allowlist; later files are not discovered automatically')

''' + text[end:]
anchor = "latest_path = ROOT / 'canonical-a-publication-observed-tasks.json'"
text = replace_once(text, anchor, EXTRA.read_text() + "\n\nlatest_path = ROOT / 'canonical-a-publication-observed-tasks-draft02.json'")
text = replace_once(text, "'canonical_shape_check_complete': False", "'canonical_shape_check_complete': True")
text = replace_once(text, "'original_322_prerequisites_remain_valid': True", "'original_322_prerequisites_valid_at_B_completion': True")
text = replace_once(text, "'native_sources_objects_actual_audit_logs_preserved': True,",
    "'no_reviewed_task_deleted_native_sources_objects_or_actual_audit_logs': True,\n"
    "    'current_native_physical_integrity': 'failed_missing_required_Mathlib_artifacts',")
text = replace_once(text, "state_raw = (json.dumps(state, ensure_ascii=False, indent=2) + '\\n').encode()",
    "state.update(extra_state)\nstate['source_pin_of_historical_receipts'] = SOURCE\n"
    "state['prior_passes_do_not_requalify_the_current_environment'] = True\n"
    "state_raw = (json.dumps(state, ensure_ascii=False, indent=2) + '\\n').encode()")
text = replace_once(text, "# Current checkpoint: canonical A compile PASS at b55",
    "# Current checkpoint: historical A/shape PASS; current native environment blocked")
text = replace_once(text, "result remains 321/321 successful with all seven postchecks passed.",
    "receipt records 321/321 successful with all seven postchecks passed at its execution time.\n"
    "Current acceptance readiness is **blocked**: the later unchanged qualified native snapshot\n"
    "expects 70,383 physical files, of which 41,505 Mathlib build artifacts are now missing\n"
    "(5,712,781,792 expected bytes). The 28,878 files found at the expected size were not\n"
    "rehash-verified by that inventory. The next B WHNF diagnostic stopped in native preflight\n"
    "before Lean ran. The missing-file cause is unknown; no reviewed metadata-release task ran.\n"
    "Newly observed free disk space is not treated as safely available A audit capacity, and no\n"
    "replacement qualification is inferred. Two exact-commit official cache index GET requests\n"
    "returned `Tunnel connection failed: 403 Forbidden` at the network layer; this does not\n"
    "establish cache absence or HTTP 404. No access restriction was bypassed. Environment-side\n"
    "restoration of the frozen physical inputs is required. All PASS claims below remain\n"
    "timestamped historical receipts.")
text = replace_once(text, "credit; independent replay, canonical complete-owned audit and canonical block-shape\ninspection remain separate gates.",
    "credit at that time. Independent replay and canonical complete-owned audit remain separate\n"
    "pending gates. Canonical block-shape inspection subsequently passed as described below.")
old_end = """**P2.4 remains incomplete:** B, W, canonical A replay/full-owned/shape, current complete324
owned acceptance and the unchanged original full export still require their actual outcomes.
No native inputs, Lean sources, objects or actual audit logs have been removed. Diagnostic
metadata preservation has been submitted separately; no duplicate release has occurred at
this checkpoint. No full-P2, main-theorem
or 6.809 claim is made. Earlier checkpoints below retain their own historical timestamps.
"""
new_end = """Canonical A shape task `af141e9e53ef4fd591f2e320debedb5e` passed separately:
2,048 private balanced blocks, each with 64 facts, cover all 131,072 indices from 32,769 to
163,840. Its complete 32,377,535-byte stdout is retained by the exact 7,577,341-byte gzip
blob `a0d5c412533cd98ca31babfe996d8b9fc48730ce`. All five requested artifacts and transport
pages were recovered without truncation. The two small original gzips are preserved as
explicit base64 text; the exact original bytes are verified. Redundant chunk/stdout/page
views are represented by byte-checked reversible maps, while all original copies remain
locally retained. This is shape evidence, not canonical full-owned audit or replay credit.

The raw B diagnostic returned `Meta.isDefEq = false` normally, with no exception and all
preservation checks passing. This does **not** prove that the Boolean endpoint evaluates to
false. The LogPoint `contains_iff` proof candidate separately passed isolated compile,
independent replay and the original full-owned template: 125 declarations, with the named
`I80.Contains.eq_1` absent. It has not been promoted to production. The independent current322
serialized-name scan reported 12,030 occurrences, 12,016 distinct names and 14 duplicate names;
the full duplicate set and all diagnostic postchecks are retained. The original duplicate guard
and all gates remain unchanged. These three diagnostics have a complete 26-member XZ archive
with blob `763a8ffb73bd88e77402e053c735fb909290855f`; one isolated object is excluded explicitly
and remains bound by its original diagnostic receipt.

Six additional proof-only candidates are preserved as diagnostic source copies and exact
patches: six modules, fourteen existing proof blocks, and 109 unchanged theorem headers.
Their inverse byte comparisons restore the frozen originals. They remain **prepared only**:
no compile, replay, original-owned acceptance or production promotion is claimed. The
LogPoint isolated PASS above is separate. Six isolated wrapper scripts are also frozen as
prepared-only workflows with the unchanged native preflight and original resource limits;
none has run. Their presence in this checkpoint grants no acceptance credit.

Diagnostic-metadata preservation task `f4ea526437424a519930753257d6e725` passed with a
569,276-byte solid XZ. The proposed release action was blocked by automatic approval review:
no release task was created, and the full rejection reason was not recovered. The materially
safer verification-only task `09da25ebebca4f20a9e2b83deb106ee2` then passed. It reconstructed
all 13 files from the preserved bundle and compared every byte with the originals; all
canonical/recipe/original-file checks passed, zero original files were deleted or written,
and zero reconstruction markers were created. No storage reclamation is credited.

The three additionally considered metadata files remain excluded and non-releasable. The
old export manifest is already preserved exactly, but historical helpers still read its loose
path; a future restore-before-read contract would be required. Coverage and current physical
consumers of the two migration JSONs are not yet fully established. Detailed read-only consumer
analysis and the original-CLI tmpfs export/retention design are included, without execution.
The separate exact-native-restoration design includes its locked cache-source analysis.
No download or restoration has run, official index existence remains unknown, and the
existing full 70,383-input verification is still required before the blocked state can clear.

**P2.4 remains incomplete:** current native inputs must first be restored and verified against
the existing frozen snapshot; B, W, canonical A replay/full-owned, complete324 owned acceptance
and the unchanged original full export still need their actual outcomes. No full-P2,
main-theorem or 6.809 claim is made. Earlier checkpoints retain their historical timestamps.
"""
text = replace_once(text, old_end, new_end)
text = replace_once(text, "'source_pin': SOURCE, 'production_files_changed': [], 'files': rows,",
    "'source_pin': SOURCE, 'production_files_changed': [], 'files': rows,\n"
    "    'previous_publication_references': previous_references,\n"
    "    'reversible_transport_views': input_plan['reversible_transport_views'],\n"
    "    'current_acceptance_readiness': 'blocked_native_physical_inputs_missing',")
TARGET.write_text(text)
assert hashlib.sha256(ORIGINAL.read_bytes()).hexdigest() == original_sha
print(json.dumps({'draft': str(TARGET), 'bytes': TARGET.stat().st_size,
                  'sha256': hashlib.sha256(TARGET.read_bytes()).hexdigest(),
                  'original_builder_sha256_unchanged': original_sha,
                  'remote_or_git_calls': False}, sort_keys=True))
