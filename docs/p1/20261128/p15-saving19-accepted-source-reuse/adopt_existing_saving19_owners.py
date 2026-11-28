from pathlib import Path
import json,hashlib,subprocess,shutil,zipfile,datetime
BASE=Path('/workspace/p1-complete-proof')
ROOT=BASE/'20261128-p15-saving19-accepted-source-reuse'
WORK=Path('/workspace/p15-continue-20261127')
BRANCH='work/p1-5-actual-means-20261125'
EXPECTED_HEAD='67c6f940d565e23fb42134999db5e2be50311b67'
INDEX=BASE/'20261128-p15-saving19-existing34-owner-reuse-precheck.json'
CLOSURE=BASE/'20261128-p15-saving19-split-actual-closure-precheck.json'
def git(*args,text=True):return subprocess.check_output(['git',*args],cwd=WORK,text=text)
def sha(data):return hashlib.sha256(data).hexdigest()
def fp(path):
 p=Path(path)
 return {'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest()}
def save(path,value):Path(path).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
assert not ROOT.exists()
assert not git('status','--porcelain') and git('rev-parse','HEAD').strip()==EXPECTED_HEAD
index=json.loads(INDEX.read_text());closure=json.loads(CLOSURE.read_text())
assert index['matching_accepted_original_owners']==34 and not index['missing_modules'] and not index['source_lookup_errors']
assert len(closure['modules'])==252
owners=index['owners'];selected={};source_rows=[];verified_logs=[]
for owner in owners:
 module=owner['module'];rel=module.replace('.','/')+'.lean'
 # These canonical source paths are absent: no other variant is overwritten.
 assert subprocess.run(['git','cat-file','-e','HEAD:'+rel],cwd=WORK,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0
 data=git('show',owner['source_commit']+':'+rel,text=False)
 assert sha(data)==owner['source_sha256']
 assert (Path('/workspace/blue-member-build')/rel).read_bytes()==data
 assert fp(owner['receipt'])['sha256']==owner['receipt_sha256']
 for path_rel,wanted in owner['source_and_five_outputs'].items():
  got=fp(Path('/workspace/blue-member-build')/path_rel)
  assert {k:got[k] for k in ['bytes','sha256']}==wanted
 for log in owner['logs_rehashed']:assert fp(log['path'])=={k:log[k] for k in ['path','bytes','sha256']}
 selected[module]=data
 source_rows.append({'module':module,'source_commit':owner['source_commit'],'canonical_path':rel,'previous_P15_source_absent':True,'bytes':len(data),'sha256':sha(data),'original_receipt':owner['receipt'],'source_and_five_outputs':owner['source_and_five_outputs']})
for module in closure['modules']:
 rel=module.replace('.','/')+'.lean';member=Path('/workspace/blue-member-build')/rel
 data=selected[module] if module in selected else git('show','HEAD:'+rel,text=False)
 assert data==member.read_bytes(),module
assert len(selected)==34 and sum(x['total_owned_exports'] for x in owners)==414
ROOT.mkdir()
shutil.copyfile(__file__,ROOT/'adopt_existing_saving19_owners.py')
for src in [INDEX,CLOSURE,BASE/'20261128-p15-saving19-existing-split-owner-fields.json',BASE/'20261128-p15-saving19-input-availability.json']:
 shutil.copyfile(src,ROOT/src.name)
# Persist the independent read-only review delivered after all old owners passed.
review={'conclusion':'No blocking findings for exact P15 source and historical evidence reuse; current26external JSON-to-historical-quoted-content binding is pending.','reviewer':'/root/p15_rough_owner_review','blocking_findings':[],'P15_base_commit':EXPECTED_HEAD,'matching_source_owners':34,'actual_source_closure':252,'already_matching_P15_Git_sources':218,'all34_original_Git_sources_and_receipts_rehashed':True,'normal_kernel_audit_logs_rehashed':102,'current_Member_original_source_and_five_outputs_checked':204,'raw_AUDIT_RECORD_count':414,'each_record_contains_type_type_expression_and_universe_parameters':True,'record_names_match_full_owned_lists':True,'axioms':['Classical.choice','Quot.sound','propext'],'selected_Core_source_sha256':'4f5fcde939aad232d55f846ba5b52ca44862085cdf3354a288d354b953138c03','selected_Core_owned':8,'excluded_v2_Core_sha256_prefix':'df9c1855','excluded_v2_Core_owned':224,'old_v2_all6_fields_mismatch':True,'current_external_input_files':26,'current_external_input_bytes':80189086,'historical_quoted_data_equal_current_external_files_NOT_yet_claimed':True,'open_scope':['concrete parse success eliminating getD fallback','CellShape','RowShape','concrete numerical inequalities','ownership','historical quote content binding to current26JSON'],'P14_not_in_this_adoption_scope':True,'new_proof_commands':0,'new_mathematical_credit':0,'whole_P1_4_complete':False,'whole_P1_5_complete':False}
save(ROOT/'INDEPENDENT_REVIEW.json',review)
for owner in owners:
 module=owner['module'];folder=ROOT/'historical-evidence'/module;folder.mkdir(parents=True)
 receipt=Path(owner['receipt']);shutil.copyfile(receipt,folder/'VALIDATION_RESULTS.json')
 for name in ['OWNED_EXPORTS.json','MODULES.json','PROJECT_SOURCE_BINDING.json','BEFORE_KERNEL.json','REUSED_NORMAL_EVIDENCE.json','PublicAudit.lean']:
  if (receipt.parent/name).is_file():shutil.copyfile(receipt.parent/name,folder/name)
 for log in owner['logs_rehashed']:shutil.copyfile(log['path'],folder/(log['stage']+'.log'))
 source=ROOT/'selected-source-postimages'/(module.replace('.','/')+'.lean');source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(selected[module])
source_bindings=[]
for module in closure['modules']:
 rel=module.replace('.','/')+'.lean';data=selected[module] if module in selected else git('show','HEAD:'+rel,text=False)
 source_bindings.append({'module':module,'bytes':len(data),'sha256':sha(data),'adopted_from_original_accepted_Git_source':module in selected})
record={'status':'PASS_EXISTING_ACCEPTED_SOURCE_AND_EVIDENCE_REUSE','checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'P15_base_commit':EXPECTED_HEAD,'original_accepted_owners':source_rows,'complete252_project_source_bindings':source_bindings,'historical_owned_declarations_reused':414,'new_owned_declarations':0,'new_proof_commands':0,'new_mathematical_credit':0,'ordinary_dependency_scopes_retained':True,'source_and_original_five_outputs_exact_current_Member':True,'old_v2_Core_excluded':True,'current_external_JSON_content_binding_pending':True,'concrete_parse_shape_numeric_ownership_not_claimed':True,'original_register':'18/21','three_ProperPower_HOLDs_unchanged':True,'whole_P1_4_complete':False,'whole_P1_5_complete':False}
save(ROOT/'SOURCE_REUSE.json',record)
(ROOT/'README.md').write_text('# Existing Saving19 input and parser owners\n\nReuse34 exact historical source/owner receipts (414 existing declarations), without any normal/kernel replay or new mathematical credit. Source plus five outputs match current Member for every owner. All252 actual Core/RowNumerics project sources are bound;218 were already exact in P15 and34 are added unchanged from their recorded original Git commits.\n\nThe selected Core has source4f5fcde9 and8owned. The old v2 Core df9c1855 and224owned is excluded. Complete original parser results are preserved by the existing parse-of-list bridges; getD fallback remains. Concrete parse success, CellShape, RowShape, numeric inequalities and ownership are not accepted here. Current26 external JSON fingerprints do not yet prove equality to historical quoted character content. No old data/schema/core proof command is repeated. P14 is outside this source adoption. P1.4/P1.5 remain open;18/21 and three ProperPower HOLDs unchanged.\n')
# Archive only sources and historical evidence; imported compiled payloads stay at pinned paths.
archive=ROOT/'p15-saving19-accepted-source-reuse-evidence.zip';members={str(p.relative_to(ROOT)):p.read_bytes() for p in ROOT.rglob('*') if p.is_file() and p!=archive}
index_members=[{'path':name,'bytes':len(data),'sha256':sha(data)} for name,data in sorted(members.items())];members['FILE_INDEX.json']=(json.dumps(index_members,indent=2)+'\n').encode()
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for name,data in sorted(members.items()):z.writestr(name,data)
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 for item in index_members:
  data=z.read(item['path']);assert len(data)==item['bytes'] and sha(data)==item['sha256']
save(ROOT/'ARCHIVE.json',{'archive':archive.name,'bytes':archive.stat().st_size,'sha256':fp(archive)['sha256'],'members':len(members),'all_member_CRCS_and_fingerprints_verified':True,'new_proof_commands':0,'new_mathematical_credit':0})
# All evidence is concrete and checked before any repository mutation.
for row in source_rows:
 target=WORK/row['canonical_path'];target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();target.write_bytes(selected[row['module']])
docs_rel='docs/p1/20261128/p15-saving19-accepted-source-reuse';docs=WORK/docs_rel;assert not docs.exists();docs.mkdir(parents=True)
for name in ['SOURCE_REUSE.json','INDEPENDENT_REVIEW.json','ARCHIVE.json','README.md',archive.name,'adopt_existing_saving19_owners.py']:
 shutil.copyfile(ROOT/name,docs/name)
for row in source_bindings:
 rel=row['module'].replace('.','/')+'.lean';data=(WORK/rel).read_bytes() if row['module'] in selected else git('show','HEAD:'+rel,text=False);assert len(data)==row['bytes'] and sha(data)==row['sha256']
subprocess.run(['git','add','--sparse',docs_rel,*[x['canonical_path'] for x in source_rows]],cwd=WORK,check=True)
subprocess.run(['git','-c','core.whitespace=cr-at-eol','diff','--cached','--check'],cwd=WORK,check=True)
body=Path('/tmp/p15-saving19-existing-source-reuse-commit.txt');body.write_text('Reuse34 accepted Saving19 input and parser owners\n\nAdopt exact recorded original Git sources and historical full-owned normal/kernel evidence. All204 source/output fingerprints and102 validation logs match;252 actual project-source closure bound. Reuse414 historical declarations with zero new proof commands or mathematical credit. Exclude old v2 Core224owned. Current external JSON-to-quoted-content binding, concrete parse success, shapes, numerics and ownership remain open. P1.4/P1.5 and18/21/three HOLDs unchanged.\n')
subprocess.run(['git','commit','-F',str(body)],cwd=WORK,check=True)
subprocess.run(['git','push','origin','HEAD:'+BRANCH],cwd=WORK,check=True)
head=git('rev-parse','HEAD').strip();assert git('ls-remote','origin','refs/heads/'+BRANCH).split()[0]==head
for row in source_bindings:
 data=git('show',head+':'+row['module'].replace('.','/')+'.lean',text=False);assert len(data)==row['bytes'] and sha(data)==row['sha256']
assert sha(git('show',head+':'+docs_rel+'/'+archive.name,text=False))==fp(archive)['sha256']
assert not git('status','--porcelain')
save(ROOT/'PUBLISHED.json',{'commit':head,'remote_branch':BRANCH,'all252Git_source_blobs_and_archive_verified':True,'remote_head_verified':True,'new_proof_commands':0,'new_mathematical_credit':0,'whole_P1_4_complete':False,'whole_P1_5_complete':False})
print('PUBLISHED_EXISTING34_SOURCE_REUSE',head,'archive_bytes',archive.stat().st_size)
