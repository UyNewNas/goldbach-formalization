#!/usr/bin/env python3
"""Select G4's three recorded original chain files on literal parent edges."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
RP='docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G4_SOURCE_REGISTRY.json';rp=ROOT/RP;raw=rp.read_bytes();assert hashlib.sha256(raw).hexdigest()=='6be461bce8278834e64ea00ae8e3140065b60e3649eb0a542b362c54d00c9262'
r=json.loads(raw)['sources'];rows={x['install'].replace('/','.').removesuffix('.lean'):x for x in r}
sel=[('P4AOriginalSavedSixthCornerIntegral','P4AOriginalSavedSixthBank'),('P4AOriginalSavedSixthPlanes','P4AOriginalSavedSixthCornerIntegral'),('P4AOriginalSavedSixthWordAccess','P4AOriginalSavedSixthPlanes')]
m=json.loads((HERE/'BEFORE_G4_INSTALL_MANIFEST.json').read_bytes());a=json.loads((HERE/'BEFORE_G4_IMPORT_AUDIT.json').read_bytes());edges=[]
for child,parent in sel:
 child='ImbalancedChen.'+child;parent='ImbalancedChen.'+parent;c=rows[child];p=rows[parent]
 assert child.split('.')[-1] in p['direct_imports']
 if parent in a['visited']:assert a['visited'][parent]['sha256']==p['sha256'] and child in a['visited'][parent]['imports']
 else:assert any(x['module']==parent and x['sha256']==p['sha256'] for x in edges)
 path='docs/source-only/'+c['path'].replace('\\','/').split('/docs/source-only/',1)[1];b=(ROOT/path).read_bytes();assert hashlib.sha256(b).hexdigest()==c['sha256'] and len(b)==c['bytes']
 edges.append({'module':child,'sha256':c['sha256'],'source':path,'parent':parent,'parent_sha256':p['sha256'],'registry':RP,'registry_sha256':hashlib.sha256(raw).hexdigest(),'note':'registered unqualified direct import interpreted as ImbalancedChen module; compatibility not typechecked'})
 m['records'].append({'source':path,'target':c['install'],'sha256':c['sha256'],'hash_registry':RP,'selection':'conditional_G4_original_exact_edge_pending_compatibility','selection_evidence':'G4 source-only registry exact parent/child SHA and unqualified direct import'})
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
(HERE/'G4_CHAIN_EVIDENCE.json').write_text(json.dumps({'scope':'original G4 chain; separate word-access variant requires compatibility check','rows':edges},indent=2,ensure_ascii=False)+'\n')
print('selected',len(edges))
