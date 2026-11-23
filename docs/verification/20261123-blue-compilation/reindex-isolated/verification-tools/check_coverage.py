#!/usr/bin/env python3
"""One canonical owner enumeration; compare names only, without repeating type/axiom checks."""
import datetime,hashlib,json,re,subprocess,time
from pathlib import Path
ROOT=Path('/workspace/blue-reindex-build-evidence');OUT=Path(__file__).parent;PROJECT=Path('/workspace/blue-reindex-build');STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def identity(p):p=Path(p);return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def set_sha(names):return hashlib.sha256(('\n'.join(sorted(names))+'\n').encode()).hexdigest()
exports=json.loads((ROOT/'PUBLIC_EXPORTS.json').read_text());modules=[x['module'] for x in exports['modules']];assert len(modules)==70
original={(x['name']):x['module'] for x in exports['declarations']};assert len(original)==len(exports['declarations'])==1742
immutable_names=['PUBLIC_EXPORTS.json','PUBLIC_AUDIT_RECEIPT.json','FINAL_TRIAL_RECEIPT.json','KERNEL_REPLAY_RECEIPT.json','PACKET_RECEIPT.json','verified-isolated-reindex-closure.zip','verified-isolated-closure/INSTALL_SELECTION.json']
immutable={n:identity(ROOT/n) for n in immutable_names};selection=json.loads((ROOT/'EXACT_SELECTION.json').read_text())
for key in ['project_sources','native_sources']:
 for name,row in selection[key].items():assert sha(row['installed_path'])==row['identity']['sha256'],name
project_objects={n:identity(PROJECT/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean')) for n in modules}
kernel=json.loads((ROOT/'KERNEL_REPLAY_RECEIPT.json').read_text())
for name,row in kernel['target_objects'].items():assert sha(row['path'])==row['sha256'],name
source='''import ImbalancedChen.P5OrderedFactorTupleRectangleReindex
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[\n    '''+',\n    '.join('`'+n for n in modules)+''']
  let moduleNames := env.header.moduleNames
  let selected := env.constants.fold (init := (#[] : Array (Name × Name))) (fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
      let owner := moduleNames[index.toNat]!
      if targets.contains owner && !isPrivateName name then acc.push (owner, name) else acc
    | none => acc)
  let entries := selected.qsort (fun a b => Name.lt a.2 b.2)
  for (owner, name) in entries do
    let record := Json.mkObj [("module", toJson owner.toString), ("name", toJson name.toString)]
    logInfo m!"CANONICAL_NAME {record.compress}"
  logInfo m!"CANONICAL_FINISHED {entries.size}"
'''
source_path=OUT/'CanonicalPublicOwnerNames.lean';source_path.write_text(source)
command=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE),'lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']
st=json.loads(STATE.read_text());guard_log=Path(st['log']);offset=guard_log.stat().st_size;log_path=OUT/'CANONICAL_ENUMERATION.log';receipt_path=OUT/'COVERAGE_ADDENDUM.json'
report={'schema':'isolated_reindex_canonical_owner_coverage_addendum_v1','status':'RUNNING_CANONICAL_NAMES_ONLY','reason':'Observed P6 counterexample shows ModuleData.constNames storage index need not equal getModuleIdxFor? owner; independently compare exact canonical environment ownership.','command':command,'cwd':str(PROJECT),'guard_state':identity(STATE),'stdin_source':identity(source_path),'driver':identity(__file__),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_immutable_inputs':immutable,'original_name_count':len(original),'original_name_set_sha256':set_sha(original),'set_digest_encoding':'Sorted unique declaration names joined by LF plus final LF; UTF-8 SHA256.','scope_module_count':len(modules),'original_type_axiom_audit_repeated':False,'native_kernel_replay_repeated':False,'Lean_proof_module_source_compilation_requested':False}
dump(receipt_path,report);started=time.monotonic()
with log_path.open('wb') as log:result=subprocess.run(command,cwd=PROJECT,input=source.encode(),stdout=log,stderr=subprocess.STDOUT)
rows=[];errors=[]
for line in log_path.read_text().splitlines():
 marker=line.find('CANONICAL_NAME ')
 if marker>=0:
  try:rows.append(json.loads(line[marker+len('CANONICAL_NAME '):]))
  except json.JSONDecodeError as e:errors.append(str(e))
fin=[int(x) for x in re.findall(r'CANONICAL_FINISHED (\d+)',log_path.read_text())];canonical={x['name']:x['module'] for x in rows};counts={n:sum(x['module']==n for x in rows) for n in modules};complete=(result.returncode==0 and not errors and fin==[len(rows)] and len(canonical)==len(rows) and all(counts.values()) and set(canonical.values())==set(modules))
missing=sorted(set(canonical)-set(original));extra=sorted(set(original)-set(canonical));owner_diff=[{'name':n,'original':original[n],'canonical':canonical[n]} for n in sorted(set(original)&set(canonical)) if original[n]!=canonical[n]]
dump(OUT/'CANONICAL_NAMES.json',{'schema':'canonical_public_owner_names_v1','modules':modules,'declarations':rows,'name_count':len(canonical),'name_set_sha256':set_sha(canonical),'per_module_counts':counts})
dump(OUT/'NAME_SET_DIFFERENCES.json',{'missing_from_original_audit':missing,'extra_in_original_audit':extra,'changed_owners':owner_diff})
with guard_log.open('rb') as f:f.seek(offset);events=[json.loads(line) for line in f if line.strip()]
events=[r for r in events if r.get('cwd')==str(PROJECT)];dump(OUT/'GUARDED_COMMANDS.json',events)
for n,r in immutable.items():assert identity(ROOT/n)==r,('Original evidence changed',n)
for n,r in project_objects.items():assert identity(r['path'])==r,('Project object changed',n)
for key in ['project_sources','native_sources']:
 for name,row in selection[key].items():assert sha(row['installed_path'])==row['identity']['sha256'],name
report.update(status=('PASS_CANONICAL_COVERAGE_EQUAL' if complete and not missing and not extra and not owner_diff else 'MISSING_CANONICAL_PUBLIC_NAMES' if complete and missing and not extra and not owner_diff else 'FAILED_CANONICAL_COVERAGE_CHECK'),exit_code=result.returncode,wall_seconds=round(time.monotonic()-started,3),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),canonical_enumeration_complete=bool(complete),metadata_parse_errors=errors,canonical_name_count=len(canonical),canonical_name_set_sha256=set_sha(canonical),name_sets_equal=set(canonical)==set(original),canonical_owner_bindings_equal=not missing and not extra and not owner_diff,missing_names=missing,extra_names=extra,owner_changes=owner_diff,per_module_canonical_public_counts=counts,canonical_names_file=identity(OUT/'CANONICAL_NAMES.json'),set_differences=identity(OUT/'NAME_SET_DIFFERENCES.json'),raw_log=identity(log_path),guarded_commands=identity(OUT/'GUARDED_COMMANDS.json'),original_evidence_unchanged=True,all70_project_olean_files_unchanged=True,all526_selected_source_files_unchanged=True)
dump(receipt_path,report);print(json.dumps({k:report[k] for k in ['status','exit_code','wall_seconds','original_name_count','canonical_name_count','original_name_set_sha256','canonical_name_set_sha256','missing_names','extra_names','owner_changes']},indent=2))
raise SystemExit(0 if complete else 1)
