import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,datetime
r=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
p=r/'ImbalancedChen/CurrentChenUpsilon9HarmonicIntegral.lean'
oldp=r/'.lake/proof-continuation/source-reviews/drafts/CurrentChenUpsilon9HarmonicIntegral.62b7ac7d605a9b57721b7ab0ed5163bedd45f44554138165c6e67617caea3716.lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
old=oldp.read_bytes();new=p.read_bytes()
assert sha(old)=='62b7ac7d605a9b57721b7ab0ed5163bedd45f44554138165c6e67617caea3716'
assert sha(new)=='26e4363c199bb367bfe12af8ec80c96547af24fd056680cb7e19bc5066c54ca3'
a=b"  field_simp [hx.ne', (sub_pos.mpr hx1).ne', hy.ne', hgap.ne']"
nl=b'\r\n' if b'\r\n' in old else b'\n'
b=a+nl+b'  change (1 - x - y - -y) * (1 - x - y) = (1 - x) * (1 - x - y)'+nl+b'  ring'
assert old.count(a)==1 and new.count(b)==1 and old.replace(a,b)==new and new.replace(b,a)==old
headers=lambda s:re.findall(r'(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def)\s+[\s\S]*?(?=:=)',s)
oh=headers(old.decode());nh=headers(new.decode());assert oh==nh and len(nh)==3
imports=lambda s:re.findall(r'(?m)^import .+$',s)
assert imports(old.decode())==imports(new.decode()) and not re.search(r'(?m)^(?:private )?def ',new.decode())
log=r/'.lake/proof-continuation/runs/20261015T210422276195Z-ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral/stdout.log'
assert log.read_text().count('error:')==1
assert '(1 - x - id y - -y) * (1 - x - y) = (1 - x) * (1 - x - id y)' in log.read_text()
out=r/'.lake/proof-continuation/source-reviews/20261016-U9HarmonicIntegral-beta-ring-owner-rebind.json'
data={'status':'SOURCE_ONLY_EXACT_PROOF_REPAIR_REBIND','reviewer':'lower_resume source owner, not independent validation','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'module':'ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral','old_source_sha256':sha(old),'new_source_sha256':sha(new),'old_snapshot':str(oldp.relative_to(r)),'actual_failed_log':str(log.relative_to(r)),'actual_failed_log_sha256':sha(log.read_bytes()),'actual_sole_diagnostic':'After the actual field_simp step, the remaining polynomial goal contains id y instead of its definitional value y.','exact_mutation':'After the existing field_simp, add a change spelling the same goal with id y reduced to y, then ring. No existing source line is replaced.','inverse_transform_recovers_entire_old_bytes':True,'complete_declaration_count':len(nh),'complete_headers_unchanged':True,'complete_headers':nh,'definitions':0,'imports_unchanged':True,'thresholds_pins_unchanged':True,'source_dag_reused_not_rewalked':'.lake/proof-continuation/source-reviews/20261016-U9HarmonicIntegral-proper-dag.json','source_independent_review':'.lake/proof-continuation/source-reviews/20261016-U9HarmonicIntegral-root-independent-semantics.json','parent_current':{'module':'ImbalancedChen.CurrentChenUpsilon9HarmonicSlices','source_sha256':sha((r/'ImbalancedChen/CurrentChenUpsilon9HarmonicSlices.lean').read_bytes()),'proof_only_independent_rebind':'.lake/proof-continuation/source-reviews/20261016-U9HarmonicSlices-integral-zero-independent-rebind.json','owned_audit':'.lake/proof-continuation/audits/20261015T210221936534Z/receipt.json','note':'The exact audit directory timestamp is referenced by runtime as 210221; source hash and the independent proof-only rebind are the actual checked source binding here. No child runtime acceptance is inferred.'},'no_compiler_invoked':True,'no_kernel_or_axiom_acceptance_claimed':True,'bytecode_writes_disabled':True,'remaining':'The repaired source awaits independent exact rebind and runtime recompile under the previously authorized precise configuration.'}
# Do not invent the audit path: resolve the actual unique runtime directory.
audit_paths=list((r/'.lake/proof-continuation/audits').glob('20261015T210221*/receipt.json'))
assert len(audit_paths)==1
data['parent_current']['owned_audit']=str(audit_paths[0].relative_to(r))
out.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'report':str(out.relative_to(r)),'sha256':sha(out.read_bytes()),'source_sha256':sha(new),'headers':len(nh),'parent_audit':data['parent_current']['owned_audit']}))
