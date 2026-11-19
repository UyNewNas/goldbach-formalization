#!/usr/bin/env python3
"""Bind seven literal frontier modules without promoting their compatibility."""
import hashlib
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREV = ROOT / 'docs/source-only/20261120-p4a5-hdensity-install-r11'
BASE = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density'
T04 = ROOT / 'docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment'

def load(path, sha):
    b = path.read_bytes()
    assert hashlib.sha256(b).hexdigest() == sha, str(path)
    return json.loads(b)

g = load(BASE/'G3_REGISTRY.json','c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d')
j = load(BASE/'REGISTRY.json','7242b3ae59e3c171eef6d0366f81824a95d41daaca5c0ea29d2876682bc1e4ea')
t = load(T04/'REGISTRY.json','279ed3950cf692f472d4a604cf780a713f709c0b73ff975badf7be1b989b4b82')
a = load(PREV/'IMPORT_AUDIT.json','64c6405ba0d2a8f8e1272e3c854d81351a75fce97c6411634a65164c7dfbab85')
m = load(PREV/'INSTALL_MANIFEST.json','fdcd707bcda682e14375cb914ad8b5449dadf75bfde46f038d31d02d2b9960a3')
m['baseline'] = '223ad22588b928e8756131b10d55da4e334ace25'
m['scope'] = 'partial source-only installation; registry-identified frontier sources conditional on closure compatibility'
parent = next(x for x in j['primary_sources'] if x['module']=='ImbalancedChen.P4AOriginalFull87CompiledCounting')
leaves = ['P2OriginalSaving16HistoricalMesh','P4AFull87CompilerCapRead','P4AFull87CompilerChangedPartition',
          'P4AOriginalFull87SlotTwoFive','P4AOriginalNewFifthBoxIntegral',
          'P4AUpperTaggedContinuationAccounting','P5OriginalHistoryGapCorner']
out = []
for leaf in leaves:
    mod = 'ImbalancedChen.'+leaf
    if leaf in ('P2OriginalSaving16HistoricalMesh','P5OriginalHistoryGapCorner'):
        record,reg = g['direct_imports_by_module'][mod],BASE/'G3_REGISTRY.json'
        declared = None
    elif leaf == 'P4AOriginalNewFifthBoxIntegral':
        record = next(x for x in g['supplement_sources'] if x['module']==mod)
        reg,declared = BASE/'G3_REGISTRY.json',record['direct_imports']
    elif leaf == 'P4AFull87CompilerChangedPartition':
        record = dict(t['proofs'][leaf+'.lean'])
        record['repository_path'] = str((T04/(leaf+'.lean')).relative_to(ROOT))
        reg,declared = T04/'REGISTRY.json',record['imports']
        assert record['namespace']==mod and record['install_as']=='ImbalancedChen/'+leaf+'.lean'
    else:
        record = next(x for x in parent['direct_imports'] if x['module']==mod)
        reg,declared = BASE/'REGISTRY.json',None
        prim = [x for x in j['primary_sources'] if x['module']==mod]
        if prim:
            assert prim[0]['sha256']==record['sha256'] and prim[0]['repository_path']==record['repository_path']
            declared=[x['module'] for x in prim[0]['direct_imports']]
        if leaf == 'P4AFull87CompilerCapRead':
            p=t['proofs'][leaf+'.lean']
            assert (p['sha256'],p['bytes'])==(record['sha256'],record['bytes'])
            declared=p['imports']
    path=record['repository_path'];target='ImbalancedChen/'+leaf+'.lean'
    assert a['missing_project_modules'][mod]==target
    b=(ROOT/path).read_bytes(); assert len(b)==record['bytes'] and hashlib.sha256(b).hexdigest()==record['sha256']
    direct=[q.group(1) for line in b.decode().splitlines() if (q:=re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*',line))]
    if declared is not None: assert direct==declared
    parents=[{'module':name,'sha256':v['sha256'],'origin':v['origin'],'path':v['path']}
             for name,v in a['visited'].items() if mod in v['imports']]
    assert parents
    m['records'].append({'source':path,'target':target,'sha256':record['sha256'],
      'hash_registry':str(reg.relative_to(ROOT)),'selection':'conditional_registered_frontier_pending_full_elaboration',
      'selection_evidence':'actual r11 frontier; registry path/hash/length match; Lean compatibility unverified'})
    out.append({'module':mod,'source':path,'target':target,'bytes':len(b),'sha256':record['sha256'],
      'registry':str(reg.relative_to(ROOT)),'direct_imports':direct,'direct_imports_registry_checked':declared is not None,
      'direct_importers':parents})
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'scope':'registered source identity and literal edges; not Lean elaboration','sources':out},indent=2))
