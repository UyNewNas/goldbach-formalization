#!/usr/bin/env python3
"""Bind the historical final-reviewed Reader and inventory its data inputs.

This verifies source/manifest bytes and literal file-name coverage only;
it neither executes the Lean elaborator nor evaluates the certificates.
"""
import hashlib,json,re
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
PREV='docs/source-only/20261119-p4a5-hdensity-install-r7/'
G3='docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/'
REVIEW='docs/source-only/20261110-yellow-closure-10t/t09_review_density_history/REPORT.md'
T03='docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/FINAL_REGISTRY.json'
def data(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(data(p))
def imports(b):
 out=[]
 for line in b.decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:out.extend(m.group(1).split())
 return out

def main():
 reg=js(G3+'G3_REGISTRY.json');fixtures=js(G3+'G3_FIXTURES.json');audit=js(PREV+'IMPORT_AUDIT.json');prev=js(PREV+'INSTALL_MANIFEST.json')
 reader='ImbalancedChen.P4AOriginalNewFifthArchiveReader'; datamod='ImbalancedChen.P4AOriginalNewFifthArchiveData'
 if reader not in audit['missing_project_modules'] or datamod not in audit['visited'] or reader not in audit['visited'][datamod]['imports']:
  raise ValueError('Reader is not the actual prior Data import frontier')
 r=next(x for x in reg['supplement_sources'] if x.get('module')==reader)
 d=next(x for x in reg['supplement_sources'] if x.get('module')==datamod)
 rb=data(r['repository_path']); db=data(d['repository_path'])
 if sha(rb)!=r['sha256'] or len(rb)!=r['bytes'] or imports(rb)!=r['direct_imports']:
  raise ValueError('final Reader identity/imports mismatch')
 if sha(db)!=d['sha256'] or len(db)!=d['bytes'] or imports(db)!=d['direct_imports']:
  raise ValueError('Data source identity/imports mismatch')
 old=next(x for x in js(T03)['external_inputs_at_review'] if x['path'].endswith('/P4AOriginalNewFifthArchiveReader.lean'))['sha256']
 review=data(REVIEW).decode()
 if old==sha(rb) or old not in review or sha(rb) not in review:
  raise ValueError('unresolved or unrecorded Reader version relationship')
 fixture_reg=reg['original_G3']['staging_fixture_manifest'] if 'staging_fixture_manifest' in reg['original_G3'] else None
 if fixture_reg is None:
  fixture_reg=next(v for v in reg['original_G3'].values() if isinstance(v,dict) and v.get('repository_path','').endswith('G3_FIXTURES.json'))
 archive_reg=reg['original_G3']['immutable_fixture_zip']
 if sha(data(G3+'G3_FIXTURES.json'))!=fixture_reg['sha256'] or fixtures['staging_archive_sha256']!=archive_reg['sha256']:
  raise ValueError('G3 fixture/ZIP registry hash mismatch')
 pairs=re.findall(r'include_new_fifth_pair%\s+"([^"\\]+)"\s+"([^"\\]+)"',db.decode())
 blocks=fixtures['blocks'];expected=[]
 for block in blocks:
  members=block['members']
  if len(members)!=2:raise ValueError('unexpected manifest member count')
  pair=[x['staged'] for x in members]
  for path in pair:
   pp=PurePosixPath(path)
   if len(pp.parts)!=2 or pp.parts[0]!='g3-fixtures' or pp.suffix!='.npy':raise ValueError('unexpected fixture path '+path)
  expected.append(tuple(pair))
 if len(pairs)!=94 or len(blocks)!=94 or pairs!=expected or len({x for pair in pairs for x in pair})!=188:
  raise ValueError('Data source and G3 fixture list disagree')
 target=r['stage_as']
 if any(x['target']==target for x in prev['records']):raise ValueError('duplicate Reader target')
 prev['records'].append({'source':r['repository_path'],'target':target,'sha256':r['sha256'],
  'hash_registry':G3+'G3_REGISTRY.json','selection':'conditional_final_G3_reviewed_reader_pending_full_P4A5_elaboration',
  'selection_evidence':'T09 explicitly selects final G3 Reader; same Data direct import and final G3 registry SHA; SOURCE_ONLY'})
 prev['baseline']='a205d080c1b3900706f2dc31ffc2689ef4b62e34'
 prev['scope']='partial staging with final G3 Reader conditional on full compatibility; no fixture or Lean execution'
 members=[x for b in blocks for x in b['members']]
 evidence={'scope':'source/fixture path and SHA records, not evaluated data or Lean verification',
  'G3_registry':G3+'G3_REGISTRY.json','G3_registry_sha256':sha(data(G3+'G3_REGISTRY.json')),
  'fixture_manifest':G3+'G3_FIXTURES.json','fixture_manifest_sha256':sha(data(G3+'G3_FIXTURES.json')),
  'data_source':d['repository_path'],'data_source_sha256':sha(db),'reader_source':r['repository_path'],'reader_sha256':sha(rb),
  'old_reader_sha256':old,'historical_review':REVIEW,'historical_review_sha256':sha(data(REVIEW)),
  'archive_name':fixtures['staging_archive'],'archive_sha256':archive_reg['sha256'],'archive_bytes':archive_reg['bytes'],
  'pair_count':len(pairs),'member_count':len(members),'total_member_bytes':sum(x['bytes'] for x in members),
  'staging_destination':'ImbalancedChen/g3-fixtures','data_evaluated':False,'members':members}
 (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
 (DEST/'G3_EVIDENCE.json').write_text(json.dumps(evidence,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'reader_bound':reader,'pairs':len(pairs),'members':len(members),'total_bytes':evidence['total_member_bytes']}))
if __name__=='__main__':main()
