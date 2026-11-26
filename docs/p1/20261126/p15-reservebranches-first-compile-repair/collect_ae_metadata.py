from pathlib import Path
import hashlib,json,os
U='ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
BASE=Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')/U
PROJECT=Path('/workspace/blue-member-build')
def fp(p):
 assert p.is_file() and not p.is_symlink(),str(p)
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
out={'source_commit':U,'runs':{},'accepted_owners':{},'failures':{}}
records=[]
for n in ('attempt-00000','attempt-00001'):
 r=BASE/'runs'/n
 out['runs'][n]={f:fp(r/f) for f in ('RESULT.json','WORKER_RESULT.json','CONTEXT_BEFORE.json','CONTEXT_AFTER.json','GIT_BEFORE.json','GIT_AFTER.json')}
 records.append(json.loads((r/'RESULT.json').read_bytes()))
for i,r in enumerate(records):
 for m in r['accepted_owners']:
  if m in out['accepted_owners']:continue
  binding=r['acceptance_bindings'][m];ap=Path(binding['audits'][0]['result']['path']);a=json.loads(ap.read_bytes())
  out['accepted_owners'][m]={'first_accepting_run_index':i,'source':fp(PROJECT/(m.replace('.','/')+'.lean')),'normal':fp(Path(binding['normal_receipt']['path'])),'audit_plan':fp(Path(binding['audits'][0]['plan']['path'])),'audit_result':fp(ap),'owned_count':a['total_owned_exports'],'public_count':a['total_public_exports'],'audit_status':a['status'],'only_standard_axioms':a['only_standard_axioms'],'full_owned_including_private_generated':a['full_owned_including_private_generated'],'kernel_exit_codes':{k:v['exit_code'] for k,v in a['kernel_commands'].items()},'audit_exit_code':a['audit_command']['exit_code'],'stock_before_exit_code':a['stock_readiness_before']['exit_code'],'stock_after_exit_code':a['stock_readiness_after']['exit_code']}
 for m,reason in r['failures'].items():
  ir=PROJECT/'.lake/build/ir'/m.replace('.','/');lib=PROJECT/'.lake/build/lib/lean'/m.replace('.','/')
  slots=[str(ir)+ext for ext in ('.c','.c.hash','.setup.json','.bc','.bc.hash','.o','.o.hash','.o.export','.o.export.hash')]
  slots += [str(lib)+ext for ext in ('.olean','.olean.hash','.olean.private','.olean.private.hash','.olean.server','.olean.server.hash','.ilean','.ilean.hash','.trace','.ir','.ir.hash','.ir.sig')]
  normal=BASE/m/'normal'/m/'attempt-00000/normal-command.json'
  out['failures'][m]={'reason':reason,'source':fp(PROJECT/(m.replace('.','/')+'.lean')),'artifact_slots':{x:fp(Path(x)) if os.path.lexists(x) else None for x in slots},'normal_metadata':fp(normal),'normal_command':json.loads(normal.read_bytes())}
for m, row in out['failures'].items():
 log=Path(row['normal_command']['log']); observed=fp(log)
 assert observed['bytes']==row['normal_command']['log_bytes'] and observed['sha256']==row['normal_command']['log_sha256']
 text=log.read_text(); marker='error: '+m.replace('.','/')+'.lean:'; start=text.find(marker)
 row['full_project_error_context']=text[start:] if start >= 0 else text[-6000:]
 row['diagnostic_log_binding']=observed
install=Path('/workspace/p1-complete-proof/20261126-p15-lowertrim-api-repair-v1')/U/'runs/attempt-00000/SOURCE_REPAIR_RESULT.json'
out['lowertrim_install']=fp(install)
out['original_first_summary']={k:records[0].get(k) for k in ('source_commit','targets','accepted_owners','failures','reused_complete_selected_owners','worker_exit_code','all_selected_owners_accepted')}
out['original_later_summary']={k:records[1].get(k) for k in ('source_commit','targets','accepted_owners','failures','reused_complete_selected_owners','worker_exit_code','all_selected_owners_accepted')}
print(json.dumps(out))
