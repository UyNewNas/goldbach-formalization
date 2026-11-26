import hashlib,json,re
from datetime import datetime, timezone
from pathlib import Path
P=Path(__file__).resolve().parent
repo=P.parent.parent
dest=P/'stage-evidence'
prefix=Path('docs/verification/20261126-p2-1')
def sha(b):return hashlib.sha256(b).hexdigest()
files={}
def add(source,target):
    source=Path(source)
    raw=source.read_bytes()
    assert source.is_file() and not source.is_symlink()
    assert str(target) not in files
    files[str(target)]=(source,raw)
historical={
 'CURRENT_ACCEPTED_SOURCE_CHECK.json':'10c168a2728bf20c77061085217e42fd10792145ff3535bfa11b3044c6e02970',
 'DIRECT_GIT_PREPARATION_RESULT.json':'37baee431c392a49d30371c6b2b810aa112d3b37e2c4c2ce9996213281dd3751',
 'FULL_AUXILIARY_EVIDENCE_REVIEW.json':'c5689412123ba718b0f39e48701d7c62654f328b991cb824693d01151027329f',
 'INTERNAL_AUXILIARY_READBACK_VERIFICATION.json':'fe35150844946af34e8aee439fa333d3e42f2f19ac77927bf779ce0f4f682716',
 'PREPARED_EVIDENCE_REPORT.json':'aaf23fc49c3e287b95ee8db08529fa4fbb83a31010fd32506985b9811b106efd',
 'PUBLICATION_BLOCK.json':'071117ffb210f69a8ce2ea09e31f38c7f38814d578c23aae3f5d2916e774f724',
 'ROOT_AUXILIARY_BYTE_CHECK.json':'14b9ddd4b2ca257f73e6dce29d0387695119e0be7d9aeb738205dad8e5311c89'}
for name,digest in historical.items():
    source=repo/prefix/name
    assert sha(source.read_bytes())==digest,name
    add(source,prefix/name)
for name in ['USER_PUBLICATION_AUTHORIZATION.json','PUSH_RESULT.json','PUSH_READBACK_VERIFICATION.json',
 'GIT_RETRIEVAL_RESULT.json','LOCAL_ARCHIVE_VERIFICATION.json','LOCAL_ARCHIVE_EXECUTION.json',
 'AUTHORIZATION_AND_PUSH.tar.xz','AUTHORIZATION_AND_PUSH_MANIFEST.json',
 'LOCAL_TRANSPORT_AND_VERIFICATION.tar.xz','LOCAL_TRANSPORT_AND_VERIFICATION_MANIFEST.json',
 'RESTORATION_TEST_RESULT.json']:
    add(P/name,prefix/name)
for name in ['PREPARATION_FRESH_READBACK.json','RETAINED_REVIEW_AND_SOURCE_BINDINGS.json',
 'FRESH_RECOVERY_CAPSULE.json','FRESH_PREPARATION_READBACK_AND_SOURCE_CHECKS.tar.xz']:
    add(P/'recovered-history'/name,prefix/name)
add(P/'recovered-history/retriever-review/RESTORED_RETRIEVER_INDEPENDENT_REVIEW.json',prefix/'RESTORED_RETRIEVER_INDEPENDENT_REVIEW.json')
for name in ['PUSH_INDEPENDENT_REVIEW.json','INITIAL_SOURCE_REFERENCE_CARDINALITY_DIAGNOSTIC.json']:
    add(P/'recovered-history/completion-review'/name,prefix/name)
add(repo/prefix/'LOCAL_COMPLETION_REVIEW.json',prefix/'LOCAL_COMPLETION_REVIEW.json')
for name in ['retrieve_git_archive_restored.py','test_retrieve_git_archive_restored.py']:
    add(P/name,Path('verification/part2')/name)
for name in ['STAGE_EVIDENCE.py','PREPARE_PUBLICATION_TREE.py']:
    add(P/name,prefix/'publication-tools'/name)
docs=[
 prefix/'P21_STATUS.md',prefix/'README.md',
 Path('docs/verification/20261125-p2-1/RUNS.json'),
 Path('docs/superpowers/plans/2026-11-25-p2-1-original-query-closure.md')]
for rel in docs:
    source=P/'drafts/evidence-commit'/rel
    b=source.read_bytes()
    assert re.search(rb'\{\{[A-Z_]+\}\}',b) is None and 'DRAFT —' not in b.decode('utf-8'),rel
    add(source,rel)
review=json.loads((repo/prefix/'LOCAL_COMPLETION_REVIEW.json').read_bytes())
assert len(review['checks'])==57 and all(x['passed'] is True for x in review['checks'])
assert not review['critical_findings'] and not review['important_findings']
assert review['payload_publication_complete'] and review['local_archive_verified'] and review['full_p2_complete'] is False
execution=json.loads((P/'LOCAL_ARCHIVE_EXECUTION.json').read_bytes())
verification=json.loads((P/'LOCAL_ARCHIVE_VERIFICATION.json').read_bytes())
assert execution['exit_code']==0 and execution['original_verifier_unchanged']
assert verification['verified_original_members']==28167 and verification['verified_source_references']==140
bounds_original=(P/'recovered-history/RECOVERY_BOUNDARIES.json').read_bytes()
assert sha(bounds_original)=='f3f0c5ba4d9b86aba70457cc7d183100e4b60c98b09fdaecdaeb441b4bb603c1'
bounds=json.loads(bounds_original)
bounds['publication_status'].update(
 state='PUBLISHED_PAYLOAD_AND_COMPLETE_LOCAL_ARCHIVE_VERIFICATION_PASSED',
 actual_publication_result_record=str(prefix/'PUSH_RESULT.json'),
 actual_remote_readback_record=str(prefix/'PUSH_READBACK_VERIFICATION.json'),
 local_complete_archive_verification_record=str(prefix/'LOCAL_ARCHIVE_VERIFICATION.json'),
 published_evidence_record_commit=None,
 evidence_record_commit_location='The Git commit containing this file; no circular self-hash or future remote readback is asserted.',
 actual_payload_commit='947a5dd8fb3c32c8a2688b767f559d7ab31d46d1',
 independent_completion_review=str(prefix/'LOCAL_COMPLETION_REVIEW.json'))
new_bounds=(json.dumps(bounds,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()
other=json.loads(new_bounds);original=json.loads(bounds_original)
other.pop('publication_status');original.pop('publication_status')
assert other==original
files[str(prefix/'RECOVERY_BOUNDARIES.json')]=(P/'recovered-history/RECOVERY_BOUNDARIES.json',new_bounds)
record={
 'schema':'p21-published-payload-and-local-verification/v1',
 'status':'PUBLISHED_PAYLOAD_AND_LOCAL_VERIFICATION_PASSED',
 'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'payload_publication_complete':True,'local_archive_verified':True,
 'payload':{'commit':'947a5dd8fb3c32c8a2688b767f559d7ab31d46d1','tree':'14b67d3e5a4435fb02046d7d541e0d5531aff719','parent':'48b343279639cb3a289628d35cc23b2710eedd05','branch':'evidence/p2-1-20261126-6c7864ad'},
 'source_snapshot_commit':'00af18335dcebcc5e24571e33be7791ff718fbff',
 'accepted_git_commit':'1de0453bee55bf1128be422787216937b8fda9c9',
 'accepted_git_tree':'af74f02d263c72b0bb8e003ce49d1134ac04c5d5',
 'archive':{'bytes':490564596,'sha256':'066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212','parts':409},
 'original_acceptance':{'finalizer_task':'048eb7ed9b5141e692483cef94c6cd9d','five_roots':5,'accepted_modules':140,'named_public_types':26,'owned_declarations':18581,'unique_owned_declarations':18581,'duplicate_owned_declarations':0},
 'current_publication_execution':{'push_task':'0e8e08b3c3254066a8cadd51cf95071e','push_exit_code':0,'remote_ref_commit_tree_parent_independently_verified':True,'retrieval_git_commands':29,'archive_parts_verified':409,'auxiliary_originals_verified':7,'auxiliary_original_plan_parts_verified':39},
 'current_original_verifier':{'exit_code':0,'elapsed_seconds':execution['elapsed_seconds'],'implementation_sha256':execution['original_verifier_sha256'],'verified_logical_original_members':verification['verified_original_members'],'verified_source_references':verification['verified_source_references'],'retained_owned_metadata':verification['owned_declaration_count']},
 'independent_completion_review':{'checks':57,'critical':0,'important':0,'path':str(prefix/'LOCAL_COMPLETION_REVIEW.json')},
 'new_lean_execution':False,'compile_credit':False,'kernel_credit':False,'new_owned_audit_credit':False,
 'full_p2_complete':False,
 'boundary':'Bounded five-root P2.1 query acceptance and preservation of the original evidence. Current transport/local verification does not establish the manuscript main theorem, historical serialized-array identity, adaptive integrals, saved floors/charges, all integral totals or final density constants.',
 'historical_missing_normal_compile_logs':['VariableEnvelope','VariableEnvelopeConsequences','VariableEnvelopeRegularity','VariableEnvelopeBoxes','VariableEnvelopeScaled','VariableEnvelopeCertificates','BufferedFirstCubeGeometry','VariableEnvelopeTailFloor'],
 'source_reference_alias_note':'140 canonical source references are retained. One additional historical same-byte repository path does not add a module or declaration.',
 'historical_recovery_boundaries':{'path':str(prefix/'RECOVERY_BOUNDARIES.json'),'previous_record_sha256':sha(bounds_original),'only_publication_status_updated':True},
 'evidence_record_commit_identity':'The Git commit containing this file; this record has no circular self-hash.',
 'reports':{Path(path).name:{'path':path,'bytes':len(raw),'sha256':sha(raw)} for path,(source,raw) in files.items() if path.startswith(str(prefix)+'/') and path.endswith('.json')}
}
files[str(prefix/'PUBLISHED_ACCEPTANCE.json')]=(None,(json.dumps(record,sort_keys=True,indent=2)+'\n').encode())
assert not dest.exists()
dest.mkdir()
inventory=[]
for path,(source,raw) in sorted(files.items()):
    target=dest/path;target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as f:f.write(raw)
    assert target.read_bytes()==raw
    inventory.append({'path':path,'source':None if source is None else str(source),'bytes':len(raw),'sha256':sha(raw),'git_blob_sha':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()})
manifest={'schema':'p21-local-evidence-publication-staging/v1','stage':str(dest),'files':inventory,'file_count':len(inventory),'file_bytes':sum(x['bytes'] for x in inventory),'source_changes':0,'full_p2_complete':False,'external_write_performed':False}
with (P/'EVIDENCE_STAGE_MANIFEST.json').open('x') as f:json.dump(manifest,f,sort_keys=True,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in manifest.items() if k!='files'},sort_keys=True))

