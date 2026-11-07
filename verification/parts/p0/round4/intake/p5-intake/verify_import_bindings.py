#!/usr/bin/env python3
"""Compare historical source/object/import witnesses, preserving relocation identity."""
from pathlib import Path
import json, hashlib, subprocess

R=Path(__file__).resolve().parent
B=R/'fixed-source/verification/parts/p5/round4/s1lowerrosser'
REPO=Path('/workspace/scratch/535d89efd063/goldbach-formalization')
old=json.loads((R/'context/verification/parts/p5/round3/s1carrier/preflight.json').read_text())
new=json.loads((B/'preflight.json').read_text())
old_by={x['module']:x for x in old['local_compiled_imports']}
rows=[]
for n in new['local_compiled_imports_rechecked']:
    o=old_by[n['module']];c=o['certificate'];v=c['result']
    actual={x['module']:x['sha256'] for x in n['recorded_direct_imports_matched']}
    expected=v.get('import_olean_sha256',{})
    rawref=n['reused_raw_log']
    raw=subprocess.check_output(['git','-C',str(REPO),'show',rawref['commit']+':'+rawref['path']])
    object_equal=[(x['sha256'],x['bytes']) for x in n['objects']]==[(x['sha256'],x['bytes']) for x in o['objects']]
    suffix=n['module'].replace('.','/')+'.olean'
    paths_preserve_module=(n['objects'][0]['path'].endswith(suffix)
      and o['objects'][0]['path'].endswith(suffix)
      and [x['path'].rsplit('/lib/lean/',1)[-1] for x in n['objects']]
          == [x['path'].rsplit('/lib/lean/',1)[-1] for x in o['objects']])
    matches=(n['source']['sha256']==o['source']['sha256']==v['source_sha256_before']==v['source_sha256_after']
      and object_equal and paths_preserve_module and n['objects'][0]['sha256']==v['olean_sha256']
      and actual==expected and hashlib.sha256(raw).hexdigest()==c['raw_log_sha256']==rawref['sha256']
      and 'FRONTEND_OK module='+n['module']+' trustLevel=0' in raw.decode()
      and v['returncode']==0 and v['trustLevel']==0 and not v['metadata_adapter'])
    rows.append({'module':n['module'],'matches_prior_source_object_import_witness':matches,
      'direct_import_bindings':len(actual),'prior_diagnostic_strict':v['strict'],
      'path_relocated':n['objects']!=o['objects'],
      'old_path':o['objects'][0]['path'],'new_path':n['objects'][0]['path'],
      'source_sha256':n['source']['sha256'],'object_sha256':n['objects'][0]['sha256']})
report={'status':'PASS' if all(x['matches_prior_source_object_import_witness'] for x in rows) else 'FAIL',
 'local_historical_modules':len(rows),'direct_import_bindings':sum(x['direct_import_bindings'] for x in rows),
 'relocated_same_hash_objects':sum(x['path_relocated'] for x in rows),
 'scope':'Read-only comparison of fixed prior/current evidence; no fresh build or replay of imported closure.',
 'first_consumer_failure':'HISTORICAL_IMPORT_BINDINGS_FIRST_CONSUMER_FAILURE.json',
 'second_consumer_failure':'HISTORICAL_IMPORT_BINDINGS_SECOND_CONSUMER_FAILURE.json',
 'consumer_correction':'Initial consumer compared full absolute object paths across cache restoration. All 62 mismatches are exactly the documented relocations. The second consumer incorrectly required every companion file to end in .olean, excluding .olean.private/.server and .ir companions for ten modules. Final comparison requires the .olean target and exact equality of all module-relative filenames, SHA256/size, source and historical import hashes. Original within-stage before/after paths remain fully equal; no producer data or proof changed.',
 'rows':rows}
(R/'P5_HISTORICAL_IMPORT_BINDINGS.json').write_text(json.dumps(report,indent=2)+'\n')
restore=json.loads((B/'restoration/namespace-import-diagnostic.json').read_text())
audit=json.loads((B/'audit-helper-diagnostic.json').read_text())
first={'restoration':{'classification':restore['classification'],
 'raw_log':'fixed-source/verification/parts/p5/round4/s1lowerrosser/restoration/raw/20261012T123841752421Z-PrimeNumberTheoremAnd.Wiener.log',
 'raw_log_sha256':restore['raw_log_sha256'],'controller_returncode':restore['controller_returncode'],
 'frontend_returncode':restore['frontend_returncode'],'frontend_returncode_note':restore['frontend_returncode_note'],
 'diagnostic':restore['diagnostic'],'source_unchanged':True,'repair':restore['repair']},
 'auxiliary_audit':audit,'target_proof_failure':None,'P0_proof_repair':None}
(R/'FIRST_DIAGNOSTICS.json').write_text(json.dumps(first,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
raise SystemExit(0 if report['status']=='PASS' else 2)
