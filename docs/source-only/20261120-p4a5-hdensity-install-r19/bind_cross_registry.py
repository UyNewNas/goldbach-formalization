#!/usr/bin/env python3
"""Bind five further edges using explicit historical cross-registry pins.

The recorded edges and source bytes are evidence, not Lean verification.
"""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
B='docs/source-only/20261110-yellow-closure-10t/'
S=[
 ('P1OriginalFourthActualQuantizedLicence','P1OriginalFourthSameScheduleLicence','588cca0cc5b387699e9c314a9cd6e602a80ad816077b804b8e1ceaecf3ab3766','t02_full87_volume_integral/successor_fourth/SAME_SCHEDULE_REGISTRY.json','t02_full87_volume_integral/successor_fourth/QUANTIZED_SUPPLEMENT_REGISTRY.json','t02_full87_volume_integral/successor_fourth/P1OriginalFourthActualQuantizedLicence.lean','bb3241c135ee5650f34e19852acc10b20ed1c0368a371199db3a9447e7c0168f'),
 ('P2OriginalLaterSixthSourceIntegral','P2OriginalLaterSixthCorrections','7a37eef4f987146e5771c106ba33d6a2bb07f9da7840ca2e3e3b8067e924ad2e','t05_all22_actual_density/successor_sixth_history/LATER_PAYMENT_REGISTRY.json','t05_all22_actual_density/successor_sixth_history/LATER_PAYMENT_REGISTRY.json','t05_all22_actual_density/successor_sixth_history/stage_repairs/P2OriginalLaterSixthSourceIntegral.lean','3bbe109004d5708c5ce9457a7fdf8d19da59fae3a56d68d6f34ce11166e13048'),
 ('P4AOriginalLaterSixthStages','P4AOriginalOrderedSixthStages','818eeb7322c0c8b648df0a6bfe76cfea63bf4b3f2e81e754f6a40b63ab19778e','t01_remote_fifth_kernel/successor_G7_payment/REGISTRY.json','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/P4AOriginalLaterSixthStages.lean','8acdac3d37381755041fe20da6cb58d9d2f12e06d7b29adc90bd12c2b15b5ec5'),
 ('P4AOriginalSavedSixthIntegral','P4AOriginalSavedSixthPrimeMean','251fdd9bd77f82d97000f3e444957bd9ca23714f98b0f3248c53adc5214d6bec','t05_all22_actual_density/G4_SOURCE_REGISTRY.json','t05_all22_actual_density/G4_SOURCE_REGISTRY.json','t05_all22_actual_density/P4AOriginalSavedSixthIntegral.lean','01805e8fa90c809680e12780fb60cc4d3d8a1c26eb1b2cfb0c4d6dc603dcd904'),
 ('P4AOriginalSixthResidualFloor','P4AOriginalOrderedSixthStages','818eeb7322c0c8b648df0a6bfe76cfea63bf4b3f2e81e754f6a40b63ab19778e','t01_remote_fifth_kernel/successor_G7_payment/REGISTRY.json','t05_all22_actual_density/successor_sixth/STAGE_REGISTRY.json','t05_all22_actual_density/successor_sixth/P4AOriginalSixthResidualFloor.lean','95dfb3e8a7f8decccad3d58a06fdaf7113f3474a6dc912238ab6f9a6248546f5')]
def sha(x):return hashlib.sha256(x).hexdigest()
def imports(b):
 out=[]
 for l in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',l)
  if m:out+=m.group(1).split()
 return out
a=json.loads((HERE/'ITERATED_IMPORT_AUDIT.json').read_bytes());m=json.loads((HERE/'ITERATED_INSTALL_MANIFEST.json').read_bytes());out=[]
for child,parent,psha,pr,sr,sp,ssha in S:
 child='ImbalancedChen.'+child;parent='ImbalancedChen.'+parent
 assert child in a['missing_project_modules'] and a['visited'][parent]['sha256']==psha and child in a['visited'][parent]['imports']
 prp=ROOT/(B+pr);srp=ROOT/(B+sr);prb=prp.read_bytes();srb=srp.read_bytes();b=(ROOT/(B+sp)).read_bytes()
 assert psha.encode() in prb and child.split('.')[-1].encode() in prb and ssha.encode() in srb and sha(b)==ssha
 out.append({'module':child,'source':B+sp,'source_sha256':ssha,'source_bytes':len(b),'source_imports':imports(b),'parent':parent,'parent_sha256':psha,'parent_registry':B+pr,'parent_registry_sha256':sha(prb),'source_registry':B+sr,'source_registry_sha256':sha(srb),'status':'conditional_cross_registry_uncompiled'})
 m['records'].append({'source':B+sp,'target':a['missing_project_modules'][child],'sha256':ssha,'hash_registry':B+sr,'selection':'conditional_cross_registry_exact_parent_and_child_pending_P4A5_elaboration','selection_evidence':'r19: actual parent SHA/import verified; linked source-only registries pin the selected source'})
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
(HERE/'CROSS_REGISTRY_EVIDENCE.json').write_text(json.dumps({'scope':'conditional explicit cross-registry candidates, repair compatibility not compiled','rows':out},indent=2,ensure_ascii=False)+'\n')
print('selected',len(out))
