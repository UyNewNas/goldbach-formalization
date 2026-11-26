from pathlib import Path
import datetime
import hashlib
import json
import re

OUT = Path('/tmp/p24-nine-source-promotion-20261126')
ROOT = Path('/tmp/p24-recursion-repairs-20261126')
DOC = 'docs/source-only/20261125-p24-original-compact'
PIN = '6e616f4e0372555f7a78bcdba3e198d0e277eec8'
PARENT = '7e87d9a1116d68abf8dfd35788e1db1d79a1b826'
files = {}

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def add(path, local, expected=None, binary=False):
    local = Path(local)
    raw = local.read_bytes()
    if expected:
        assert digest(raw) == expected, str(local)
    if not binary:
        raw.decode('utf-8')
    row = {'path': path, 'read_source': str(local), 'bytes': len(raw),
           'sha256': digest(raw), 'binary': binary, 'mode': '100644', 'type': 'blob'}
    if path in files:
        assert files[path]['sha256'] == row['sha256'], path
    files[path] = row
    return row

def standard_manifest(path, destination):
    path = Path(path)
    data = json.loads(path.read_text())
    for row in data['files']:
        add(row['path'], row['read_source'], row['sha256'], row.get('binary', False))
    add(destination, path)
    return data

old_two = json.loads(Path('/tmp/p24-owned-source-repairs-20261126/tree-elements.json').read_text())
for row in old_two[:2]:
    add(row['path'], row['read_source'], row['sha256'])

scope = standard_manifest(ROOT/'scope-candidates/encloser-array-natrec-publication-files.json',
                          DOC+'/recursion-repairs/encloser-array/publication-manifest.json')
for row in scope['source_candidates_for_root_review']:
    add(row['canonical_path'], row['read_source'], row['sha256'])
standard_manifest(ROOT/'concrete-loop/attempt-001/publication-manifest.json',
                  DOC+'/recursion-repairs/concrete-loop/publication-manifest.json')
standard_manifest(ROOT/'adaptive-forest/publication-manifest.json',
                  DOC+'/recursion-repairs/adaptive-forest/publication-manifest.json')
standard_manifest(ROOT/'cached-run/publication-manifest.json',
                  DOC+'/recursion-repairs/cached-run/publication-manifest.json')
concrete = standard_manifest(ROOT/'concrete-run/publication-manifest.json',
                             DOC+'/recursion-repairs/concrete-run/publication-manifest.json')

ledger_path = ROOT/'ledger/publication-manifest.json'
ledger = json.loads(ledger_path.read_text())
for row in ledger['files']:
    relative = row['relative_path']
    if relative.startswith('candidate/'):
        path = 'ImbalancedChen/P2OriginalPriorityForestLedger.lean'
    elif relative == 'repair-note.md':
        path = DOC+'/recursion-repairs/ledger/repair-note.md'
    else:
        path = DOC+'/recursion-repairs/'+relative
    add(path, row['local_path'], row['sha256'])
add(DOC+'/recursion-repairs/ledger/publication-manifest.json', ledger_path)

retention = Path('/tmp/p24-export-retention-recovery-20261126')
retention_manifest = retention/'storage-xz-publication-files.json'
for row in json.loads(retention_manifest.read_text())['files']:
    add(row['repository_path'], row['local_absolute_path'], row['sha256'])
add(DOC+'/export-retention-recovery-20261126/storage-xz-publication-files.json', retention_manifest)
for name in ['stage2-submit.sh','stage2-root-review.json']:
    add('diagnostics/export-retention-recovery-20261126/'+name, retention/name)
for path in sorted((retention/'stage2-actual').iterdir()):
    if path.is_file():
        add(DOC+'/export-retention-recovery-20261126/stage2-actual/'+path.name, path)

# Independent reviews are evidence, never substituted for the original gates.
for path in sorted((ROOT/'cached-run').glob('independent-*.json')):
    add(DOC+'/recursion-repairs/cached-run/'+path.name, path)
for path in sorted((ROOT/'cached-run').glob('independent-*.md')):
    add(DOC+'/recursion-repairs/cached-run/'+path.name, path)
for path in sorted((ROOT/'cached-run/full-002/independent-review').iterdir()):
    if path.is_file():
        add(DOC+'/recursion-repairs/cached-run/full-002/independent-review/'+path.name, path)

production = sorted((row for path,row in files.items() if path.startswith('ImbalancedChen/')), key=lambda x:x['path'])
assert len(production) == 9, [r['path'] for r in production]
original_two = {row['path']:row for row in old_two[:2]}
static = []
for row in production:
    raw = Path(row['read_source']).read_bytes()
    text = raw.decode()
    assert 'import TreeFoldCandidate' not in text and 'SourceTree.rec' not in text
    assert not re.search(r'^\s*(?:(?:private|protected)\s+)?(?:axiom|unsafe\s+def|partial\s+def)\b', text, re.M)
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b', text)
    if row['path'] in original_two:
        original_sha = original_two[row['path']]['base_sha256']
        row['base_sha256'] = original_sha
        static.append({'path':row['path'],'original_sha256':original_sha,
                       'candidate_sha256':row['sha256'],'previous_independent_review_preserved':True})
        continue
    original = (ROOT/'originals'/Path(row['path']).name).read_bytes()
    orig_text = original.decode()
    row['base_sha256'] = digest(original)
    heads = lambda s: re.findall(r'(?ms)^(?:private )?theorem\s+.*?(?=\s*:=)',s)
    orig_heads = heads(orig_text)
    new_heads = heads(text)
    assert all(h in new_heads for h in orig_heads), row['path']
    imports = lambda s: re.findall(r'^import .+$',s,re.M)
    options = lambda s: re.findall(r'^\s*(?:set_option|local\s+set_option) .+$',s,re.M)
    assert imports(orig_text) == imports(text), row['path']
    assert options(orig_text) == options(text), row['path']
    static.append({'path':row['path'],'original_sha256':digest(original),
                   'candidate_sha256':row['sha256'],'original_theorem_headers_preserved':len(orig_heads),
                   'imports_unchanged':True,'source_option_scope_unchanged':True})

expected_sources = {
 'ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean':'048eda0f169f5842cf3a969e0c05eb1192222ac920e71153b4cecd5e564990a6',
 'ImbalancedChen/ActualThirdOriginalP4AOrdinaryFiniteSelector.lean':'bc50bc05f214ff8c9716000558c170fb8a92334ff7bd32465616507107f81547',
 'ImbalancedChen/P2OriginalCompactQ80Encloser.lean':'139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058',
 'ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean':'b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d',
 'ImbalancedChen/P2OriginalAdaptiveForestSourceIdentity.lean':'e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6',
 'ImbalancedChen/P2OriginalCompactConcreteLoop.lean':'04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0',
 'ImbalancedChen/P2OriginalPriorityForestLedger.lean':'11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c',
 'ImbalancedChen/P2OriginalCompactConcreteRun.lean':'18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2',
 'ImbalancedChen/P2OriginalCompactCachedRun.lean':'80aab3eb9bda4146fa09ab0245a5bf93114dbf3f788175fb5ed868bfa8a330d4',
}
assert {r['path']:r['sha256'] for r in production} == expected_sources
isolated = [
 ('DataCore','b9065e2fa34c495d8b6691e4c26474c4',58),
 ('FiniteSelector','f2ffa9d3726247abb92bbef7c85d9ada',89),
 ('Q80Encloser','8d56c275c9174285b46c320201d11d33',193),
 ('Q80ArrayTable','8d56c275c9174285b46c320201d11d33',19),
 ('AdaptiveForestSourceIdentity','5bf981f9bbd5432f8765bb099af95cd7',42),
 ('PriorityForestLedger','4164a39fc61e485ebabec90f4761301a',201),
 ('ConcreteLoop','df72bc1bd44d4eb3aabca7cd80785131',106),
 ('ConcreteRun','dd367ab8f2b643d5804840e840928551',None),
 ('CachedRun','af16794dc5d34e17b425b4556fca60ca',99),
]
# Actual last task and receipt must already be saved by its owner.
concrete_receipt = json.loads((ROOT/'concrete-run/attempt-006/receipt.json').read_text())
assert concrete_receipt['all_three_stages_passed'] is True and concrete_receipt['wrapper_exit_code'] == 0
assert all(concrete_receipt['postchecks'].values()) and not concrete_receipt['postcheck_errors']
isolated[7] = (*isolated[7][:2],concrete_receipt['audit_summary']['owned_count'])

now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')
state = {
 'schema':'p24-nine-source-promotion-v1','as_of':now,'source_base_pin':PIN,
 'publication_parent':PARENT,'remote_canonical_source_pin_before_integration':PIN,
 'changed_production_files':production,'static_source_review':static,
 'isolated_passes':[{'module':n,'task_id':t,'compiler_environment':('P3' if n=='DataCore' else 'P2'),'owned_count':c,'compile_replay_full_owned_passed':True} for n,t,c in isolated],
 'shared_tree_fold':{'task_id':'e046315a0a574746859728913b59e07b','owned_count':19,
   'source_sha256':'8a46d925da6ccc0f469d21449e24eeb7dd3d2921abba9b4cec757d9ecfc08778',
   'bound':'sum of the three original nonnegative integer coordinate widths plus one',
   'uses_sizeOf':False,'source_split_width_guard_unchanged':True},
 'historical_source6e':{'original_compiled_count':322,'original_owned_accepted_receipts_before_reselection':87,
   'canonical_A_compiler_passed':True,'canonical_A_replay_and_owned_passed':False,
   'B_cancelled_before_start':True,'W_run':False},
 'new_source_original_321_passed':False,'new_source_A_passed':False,
 'new_source_B_passed':False,'new_source_W_passed':False,'new_source_final_324_selected':False,
 'full_P2_4_complete':False,'full_P2_complete':False,'main_theorem_complete':False,'6_809_claim':False,
 'original_321_324_roots_and_resource_envelopes_unchanged':True,
 'storage':{'stage1_task':'1107b856458b46deadc06036604e39a7','stage2_task':'602f0f63825a48a295d3b799dd9df0b4',
   'exact_original_gzip_reconstructed':True,'original_sha256':'3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463',
   'original_member_count':13856,'original_member_payload_bytes':4302650543,
   'redundant_original_gzip_released_bytes':581735403,'retained_xz_bytes':28798608,
   'retained_xz_sha256':'059f665f7dd471a5f19a8ec7fcce4302deb3ab0ba170b2a34bd1db214e94ad49',
   'all_mutable_original_members_preserved':True,'shared_qualified_native_members':1752,'no_new_gate_credit':True},
}
(OUT/'nine-source-promotion-state.json').write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n')
add(DOC+'/p24-nine-source-promotion-20261126.json', OUT/'nine-source-promotion-state.json')

rows='\n'.join(f'| {name} | `{task}` | {count} |' for name,task,count in isolated)
section=f'''## Nine-module recursion repair: pre-integration checkpoint

Recorded {now}. This source promotion contains exactly nine production module
changes. Every candidate has separately passed compilation, independent
leanchecker replay, and the unchanged original complete owned/type audit.
The active P2 checkout at this checkpoint is still `{PIN}`. The new combined
source has not yet passed the original 321/A/B/W or final full324 gates.
Historical 322 compiler passes and 87 accepted original receipts remain tied to
their old source/object bindings; they are not copied as new-source acceptance.

| Candidate | Successful isolated task | Complete owned declarations |
|---|---|---:|
{rows}

DataCore adds only `import Lean.Elab.Command`, allowing the unchanged original
audit command to elaborate. The other eight modules replace the 25 observed
partial structural recursion implementations with explicit safe recursors.
Existing public theorem statements, branches, queue/root/leaf order, serial
progression, zero-fuel behavior, original Q80 arithmetic and numerical targets
are retained. Proof edits normalize only the corresponding recursion equations.
The [exact source and status manifest](p24-nine-source-promotion-20261126.json)
and complete failed/successful diagnostics bind each candidate to its bytes.

The shared tree fold is computable and has a proved sufficient bound derived
from the original split geometry: sum of three nonnegative integer coordinate
widths plus one. A legal split strictly decreases the selected width and leaves
the other two unchanged. Its leaf/split equations were checked, and task
`e046315a0a574746859728913b59e07b` passed all three stages with 19 owned
declarations. The earlier direct `SourceTree.rec` code-generation failure and
the `sizeOf` missing-LCNF failure are preserved as failed attempts. The accepted
helper uses neither. No speed or whole-run endpoint claim follows from this
small helper test.

Downstream isolated candidates import only this SHA-bound helper alongside the
old lower modules. The original 321 compiler must therefore check all nine
changes together. Static review identifies proof normalization as a remaining
integration risk, especially when both sides change from generated pattern
equations to explicit List.rec. No isolated result substitutes for that gate.

Storage retention also completed its separate verification. Stage1 task
`1107b856458b46deadc06036604e39a7` preserved every potentially mutable original
archive member in a 28,798,608-byte xz and verified 1,752 shared, immutable native
members. Independent stage2 task `602f0f63825a48a295d3b799dd9df0b4` reconstructed
the exact original 581,735,403-byte gzip, SHA `3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463`,
and rechecked all 13,856 members / 4,302,650,543 payload bytes. Only after this
pass was that redundant gzip removed, freeing 581,735,403 bytes. The original
manifest, qualified native files, source, objects, audit logs and registry were
not removed. The retained xz, reconstruction recipe, exact native bindings and
release receipt remain persistent. The old gzip path is now explicitly marked
as requiring reconstruction, not presented as a downloadable archive.

Full P2.4, full P2, the main theorem and a 6.809 bound remain uncompleted.

'''
for name in ['p24-memory-and-audit-checkpoint-20261126.md','p24-source-node-blocks-promotion-20261126.md']:
    old=(Path('/tmp/p24-recursion-risk-publication-20261126')/name).read_text()
    title,rest=old.split('\n',1)
    # Keep prior evidence as explicitly dated history, and replace the stale
    # pending-sizeOf description with the actual failed and passed stages.
    rest=rest.replace('through the original address list/seed index, and a computable tree fold with a\nproved sufficient structural bound is being prepared for full traversals.\nThe sizeOf bound includes Nat serial values and is not claimed to equal node count;\nits practical cost remains subject to the unchanged original gates.',
                      'through the original address list/seed index. The later accepted tree fold uses\na bound proved from the original three coordinate widths. The intermediate\nsizeOf candidate failed code generation and is not the accepted implementation.\nThe current original-gate integration status is recorded at the top of this file.')
    updated=title+'\n\n'+section+'## Preserved source6e checkpoint and historical evidence\n'+rest
    (OUT/name).write_text(updated)
    add(DOC+'/'+name,OUT/name)

add('diagnostics/p24_select_original_audit_receipts.py', Path('/tmp/p24_select_original_audit_receipts.py'),
    '0b2798884008c0de0827c8668e828c2bcf236f2e81ec5a2a1eadce9e1769d6be')
for name in ['selector-before-history-freeze.py','selector-history-freeze.patch','selector-history-freeze-review.json']:
    add('diagnostics/recursion-repairs-20261126/'+name, OUT/name)
for path in sorted(OUT.glob('selector-independent-review.*')):
    add(DOC+'/recursion-repairs/'+path.name, path)
add('diagnostics/recursion-repairs-20261126/build-nine-source-publication.py', Path(__file__))
manifest={'schema':'p24-nine-source-publication-files-v1','parent':PARENT,'source_base_pin':PIN,
          'file_count':len(files),'files':list(files.values()),'all_isolated_passes_preserved':True,
          'joint_original_gates_pending':True}
(OUT/'publication-files.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
add(DOC+'/p24-nine-source-publication-files-20261126.json',OUT/'publication-files.json')

tree=[]
for row in files.values():
    entry={'path':row['path'],'mode':'100644','type':'blob'}
    if row['binary']:
        assert row['sha256']=='7e5a5463577e5904aa88ebecb81d31a1b301c104a88897e8490acfc556d45f3f'
        entry['sha']='56bc4f96699ce6b9b08b2a9b3d3e0c86c358415b'
    else:
        entry['content']=Path(row['read_source']).read_bytes().decode()
    tree.append(entry)
(OUT/'tree-elements-with-content.json').write_text(json.dumps(tree,ensure_ascii=False,separators=(',',':')))
print(json.dumps({'files':len(files),'production_files':len(production),
                  'tree_json_bytes':(OUT/'tree-elements-with-content.json').stat().st_size,
                  'state_sha256':digest((OUT/'nine-source-promotion-state.json').read_bytes()),
                  'manifest_sha256':digest((OUT/'publication-files.json').read_bytes())}))
