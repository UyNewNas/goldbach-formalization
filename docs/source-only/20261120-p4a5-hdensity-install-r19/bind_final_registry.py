#!/usr/bin/env python3
"""Bind three further edges using explicit historical cross-registry pins.

The recorded edges and source bytes are evidence, not Lean verification.
"""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
B='docs/source-only/20261110-yellow-closure-10t/'
S=[
 ('P2OriginalLaterSixthArchive','P2OriginalLaterSixthOwnedIntegral','eefd21efa289fe2a029afbc7673b769dcab43beb7aeeb447736c33a2509c6a9d','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/P2OriginalLaterSixthArchive.lean','b76b2559bcff838a680d0b931fba5817d709da35d395eaa21ca31190be38128d'),
 ('P2OriginalLaterSixthKernel','P2OriginalLaterSixthRationalGates','d245cd213f337da89f0a2eddb80d369127d4c28c67960551889054414c1722d9','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/P2OriginalLaterSixthKernel.lean','5cb132dd52bac5cd4c6bf5914dff23b4f3da78db33df7b752adae8c556dadbdd'),
 ('P4AOriginalSavedSixthBank','P4AOriginalSavedSixthIntegral','01805e8fa90c809680e12780fb60cc4d3d8a1c26eb1b2cfb0c4d6dc603dcd904','t05_all22_actual_density/G4_SOURCE_REGISTRY.json','t05_all22_actual_density/G4_SOURCE_REGISTRY.json','t05_all22_actual_density/P4AOriginalSavedSixthBank.lean','d37c1a5846272475bf16bf697df46a13f3f6eb1c1aed07b62124263b063cbedc')]

def sha(x):return hashlib.sha256(x).hexdigest()
def imports(b):
 out=[]
 for l in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',l)
  if m:out+=m.group(1).split()
 return out
a=json.loads((HERE/'POST_CROSS_IMPORT_AUDIT.json').read_bytes());m=json.loads((HERE/'POST_CROSS_INSTALL_MANIFEST.json').read_bytes());out=[]
for child,parent,psha,pr,sr,sp,ssha in S:
 child='ImbalancedChen.'+child;parent='ImbalancedChen.'+parent
 assert child in a['missing_project_modules'] and a['visited'][parent]['sha256']==psha and child in a['visited'][parent]['imports']
 prp=ROOT/(B+pr);srp=ROOT/(B+sr);prb=prp.read_bytes();srb=srp.read_bytes();b=(ROOT/(B+sp)).read_bytes()
 assert psha.encode() in prb and child.split('.')[-1].encode() in prb and ssha.encode() in srb and sha(b)==ssha
 out.append({'module':child,'source':B+sp,'source_sha256':ssha,'source_bytes':len(b),'source_imports':imports(b),'parent':parent,'parent_sha256':psha,'parent_registry':B+pr,'parent_registry_sha256':sha(prb),'source_registry':B+sr,'source_registry_sha256':sha(srb),'status':'conditional_cross_registry_uncompiled'})
 m['records'].append({'source':B+sp,'target':a['missing_project_modules'][child],'sha256':ssha,'hash_registry':B+sr,'selection':'conditional_cross_registry_exact_parent_and_child_pending_P4A5_elaboration','selection_evidence':'r19: actual parent SHA/import verified; linked source-only registries pin the selected source'})
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
(HERE/'FINAL_REGISTRY_EVIDENCE.json').write_text(json.dumps({'scope':'conditional explicit cross-registry candidates, repair compatibility not compiled','rows':out},indent=2,ensure_ascii=False)+'\n')
print('selected',len(out))
