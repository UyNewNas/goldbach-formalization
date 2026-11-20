#!/usr/bin/env python3
"""Select only frontier edges supported by exact-parent historical manifests.

These are conditional source selections, not typechecking or proof acceptance.
"""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parent
OLD=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r18'
T=ROOT/'docs/source-only/20261110-yellow-closure-10t'
R={
 'early':T/'t03_saved87_actual_gain/successor_early_135/REGISTRY.json',
 'later':T/'t05_all22_actual_density/successor_sixth_history/LATER_PAYMENT_REGISTRY.json',
 'g7repair':T/'t01_remote_fifth_kernel/successor_G7_review_repairs/SELECTED_INSTALL_MANIFEST.json',
 'g7cont':T/'t01_remote_fifth_kernel/successor_G7_continuation/REGISTRY.json',
 'g7pay':T/'t01_remote_fifth_kernel/successor_G7_payment/REGISTRY.json',
 'g4':T/'t05_all22_actual_density/G4_PHYSICAL_REGISTRY.json'}
# child, registry, exact selected child sha
S=[
 ('P1OriginalFourthCofinalGain','early','6697cc6e4d53107454cdd8508361f5f14a24633efdd49c2a6bbfbfe9687a9e86'),
 ('P1OriginalFourthUniformCutoffLicence','early','23cf5eac21a4a85f30db4d13be6b57783c3e278815a35cdadd858d355f71fc31'),
 ('P2OriginalLaterSixthJointTests','later','32f628112d2f42dfcc9e6372b10eb3bdd1d593fe7ac45b764e8853d43ce03506'),
 ('P2OriginalSixthInnerPrimeTests','g7repair','515a0148e9e979f51acca3445a0f00b61d9b991b436524a848a39c16c844ae5e'),
 ('P4AOriginalElevenOrderedLocal','g7repair','64300da1bbbc17a0ed5d3eab264addb531cc1f9e962bf6a0d8cec51adba653da'),
 ('P4AOriginalElevenRankSixSigned','g7cont','5adca3b07eebf866ee92f451a5b0571ac269c2fff335487cf588107281c499c1'),
 ('P4AOriginalOrderedSixthStages','g7pay','818eeb7322c0c8b648df0a6bfe76cfea63bf4b3f2e81e754f6a40b63ab19778e'),
 ('P4AOriginalSavedSixthOccurrence','g4','fb40cbeabb0b00152917b943c8b040d98228d37cdd909da68090bf082df6fd61'),
 ('P4AOriginalSixthTupleReverse','g7cont','8aec02bd304fea834c2a149322d72d3b5ec4dd94e40bb0f5ffe322acbcc5b87f')]
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def imports(b):
 out=[]
 for line in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:out+=m.group(1).split()
 return out
def walk(x):
 if isinstance(x,dict):
  yield x
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
manifest=json.loads((OLD/'INSTALL_MANIFEST.json').read_bytes()); audit=json.loads((OLD/'IMPORT_AUDIT.json').read_bytes()); candidates=json.loads((OLD/'UNBOUND_CANDIDATES.json').read_bytes()); rows={x['module']:x for x in candidates['rows']}
regs={k:json.loads(p.read_bytes()) for k,p in R.items()};evidence=[]
for short,key,childsha in S:
 mod='ImbalancedChen.'+short; assert mod in audit['missing_project_modules']
 selected=regs[key]['selected_files'] if key=='g7repair' else list(walk(regs[key]))
 child=[x for x in selected if x.get('module')==mod and x.get('sha256')==childsha];assert child,(mod,key)
 child=child[0];paths={p for x in rows[mod]['candidate_registry_records'] if x['sha256']==childsha for p in x['matching_local_paths']};assert len(paths)==1,(mod,paths)
 path=next(iter(paths)); data=(ROOT/path).read_bytes();assert sha(data)==childsha
 assert len(data)==child.get('bytes',len(data));assert not child.get('git_blob_sha1') or blob(data)==child['git_blob_sha1']
 ci=child.get('direct_imports',child.get('imports'));assert ci is not None and imports(data)==ci,(mod,ci,imports(data))
 parents=[]
 for name,p in audit['visited'].items():
  if mod not in p['imports']:continue
  found=[]
  for rk in dict.fromkeys((key,'g7pay' if key=='g7cont' else key)):
   space=regs[rk]['selected_files'] if rk=='g7repair' else walk(regs[rk])
   for v in space:
    if v.get('module')==name and v.get('sha256')==p['sha256'] and mod in v.get('imports',v.get('direct_imports',[])):
     found.append({'registry':str(R[rk].relative_to(ROOT)),'registry_sha256':sha(R[rk].read_bytes()),'parent_sha256':p['sha256']})
  parents.append({'module':name,'sha256':p['sha256'],'registered_edges':found})
 assert any(p['registered_edges'] for p in parents),(mod,parents)
 evidence.append({'module':mod,'source':path,'sha256':childsha,'blob':blob(data),'bytes':len(data),'imports':ci,'registry':str(R[key].relative_to(ROOT)),'registry_sha256':sha(R[key].read_bytes()),'parent_edges':parents})
 manifest['records'].append({'source':path,'target':audit['missing_project_modules'][mod],'sha256':childsha,'hash_registry':str(R[key].relative_to(ROOT)),'selection':'conditional_exact_historical_parent_and_child_pending_P4A5_elaboration','selection_evidence':'r19 recorded actual parent SHA and direct import edge; source SHA, length, imports and available blob match same source-only registry'})
manifest['baseline']='7d0bf2a60b66e9a31d9eca7ce338ab01d70b6c5d';manifest['scope']='partial source-only install, r18 plus nine exact historical registry edges; compatibility unverified'
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
(HERE/'EDGE_EVIDENCE.json').write_text(json.dumps({'status':'SOURCE_ONLY_CONDITIONAL_UNCOMPILED','rows':evidence},indent=2,ensure_ascii=False)+'\n')
print('selected',len(evidence))
