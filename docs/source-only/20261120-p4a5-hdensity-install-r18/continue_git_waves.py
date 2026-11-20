#!/usr/bin/env python3
"""Continue literal graph waves using exact T06 parent and local source hashes.

Only copies unchanged source bytes into a new external stage. This is a
conditional cross-registry inventory, not Lean parsing or proof acceptance.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from collections import Counter,defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
REG=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
def digest(b):return hashlib.sha256(b).hexdigest()
def read(path,sha):
 b=path.read_bytes();assert digest(b)==sha,str(path);return json.loads(b)
manifest=read(HERE/'PRE_FINAL_INSTALL_MANIFEST.json','cfb7cd2c0942d71e76a6a8501ce2d31c33a3c1d494759a892cff7bb5bb28ea17')
audit=read(HERE/'PRE_FINAL_IMPORT_AUDIT.json','9303212b4ceaef77a94c43655479a6e4d05e1c04eeb019a4fe4ccb64230241b3')
r=read(REG,'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9')
files={x['module']:x for x in r['files']};assert len(files)==len(r['files'])
paths=defaultdict(list)
for p in sorted(subprocess.run(['rg','--files','-g','*.lean'],cwd=ROOT,text=True,check=True,capture_output=True).stdout.splitlines()):paths[Path(p).name].append(p)
ap=argparse.ArgumentParser();ap.add_argument('--previous-stage',type=Path,required=True);ap.add_argument('--stage',type=Path,required=True);ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args()
prev=args.previous_stage.resolve(strict=True);stage=args.stage.resolve();out=args.output_dir.resolve()
assert not stage.exists() and stage!=ROOT and ROOT not in stage.parents and stage!=prev and prev not in stage.parents and stage not in prev.parents
assert not out.exists() or not any(out.iterdir())
shutil.copytree(prev,stage);out.mkdir(parents=True,exist_ok=True)
cache={}
def getbytes(p):
 if p not in cache:cache[p]=p.read_bytes()
 return cache[p]
def imports(data):
 out=[]
 for line in data.decode('utf-8-sig').splitlines():
  match=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if match:out+=match.group(1).split()
 return out
def walk():
 pending=['ImbalancedChen.P4AOriginalFiniteAll22FineDensity'];visited={};missing={};external=set()
 while pending:
  mod=pending.pop()
  if mod in visited or mod in missing:continue
  if not mod.startswith('ImbalancedChen.'):external.add(mod);continue
  rel=Path(*mod.split('.')).with_suffix('.lean');src=stage/rel if (stage/rel).is_file() else ROOT/rel
  if not src.is_file():missing[mod]=str(rel);continue
  data=getbytes(src);i=imports(data)
  visited[mod]={'origin':'stage' if stage in src.parents else 'checkout','path':str(rel),'sha256':digest(data),'imports':i}
  pending.extend(i)
 return {'staged_count':len(manifest['records'])+1,'visited_project_modules':len(visited),
  'missing_project_modules':missing,'external_modules':sorted(external),'visited':visited}
initial=walk();assert initial==audit,'previous stage does not match its audit'
waves=[]
for number in range(1,51):
 candidates=[];status=Counter()
 for mod,target in sorted(audit['missing_project_modules'].items()):
  rec=files.get(mod)
  if not rec:status['missing_from_T06']+=1;continue
  parents=[(n,x) for n,x in audit['visited'].items() if mod in x['imports']]
  exact=[(n,x) for n,x in parents if n in files and files[n]['sha256']==x['sha256'] and mod in files[n]['imports']]
  if not exact:status['no_exact_parent']+=1;continue
  choices=[]
  for path in paths[mod.split('.')[-1]+'.lean']:
   data=getbytes(ROOT/path)
   if digest(data)==rec['sha256']:choices.append((path,data))
  if not choices and rec.get('origin',{}).get('kind')=='git':
   origin=rec['origin']
   git=subprocess.run(['git','show',origin['commit']+':'+origin['path']],cwd=ROOT,capture_output=True)
   if git.returncode==0 and digest(git.stdout)==rec['sha256']:
    pin=HERE/'pinned'/Path(*mod.split('.')[1:]).with_suffix('.lean')
    assert not pin.exists() or pin.read_bytes()==git.stdout
    pin.parent.mkdir(parents=True,exist_ok=True)
    if not pin.exists():pin.write_bytes(git.stdout)
    path=str(pin.relative_to(ROOT));paths[pin.name].append(path);choices.append((path,git.stdout))
  if not choices:status['no_exact_local_source_or_git_object']+=1;continue
  assert len(choices)==1 and rec['install_path']==target,mod
  path,data=choices[0];assert len(data)==rec['bytes']
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  assert blob==rec['git_blob_sha1'] and imports(data)==rec['imports'],mod
  candidates.append({'module':mod,'source':path,'target':target,'sha256':rec['sha256'],
    'git_blob_sha1':blob,'bytes':len(data),'direct_imports':rec['imports'],
    'T06_origin':rec.get('origin'),'T06_selection':rec.get('selection'),
    'actual_importers':[{'module':n,'origin':x['origin'],'sha256':x['sha256'],
      'T06_parent_sha_matches':n in files and files[n]['sha256']==x['sha256'] and mod in files[n]['imports']} for n,x in parents]})
  status['conditional_exact_parent_and_local_source']+=1
 assert sum(status.values())==len(audit['missing_project_modules'])
 if not candidates:
  waves.append({'wave':number,'prior_missing':len(audit['missing_project_modules']),'summary':dict(status),'sources':[]});break
 for x in candidates:
  target=stage/x['target'];assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True)
  data=getbytes(ROOT/x['source']);target.write_bytes(data);assert digest(target.read_bytes())==x['sha256']
  manifest['records'].append({'source':x['source'],'target':x['target'],'sha256':x['sha256'],
   'hash_registry':str(REG.relative_to(ROOT)),
   'selection':'conditional_T06_exact_parent_source_pending_P4A5_elaboration',
   'selection_evidence':'iterated actual missing edge with at least one exact T06 parent; source SHA, blob, size and imports match; cross-target compatibility unverified'})
 old=set(audit['missing_project_modules']);audit=walk();new=set(audit['missing_project_modules'])
 waves.append({'wave':number,'prior_missing':len(old),'resolved':len(old-new),'new':len(new-old),'remaining':len(new),'summary':dict(status),'sources':candidates})
else:raise RuntimeError('50-wave guard reached; not a closure claim')
manifest['scope']='partial source-only install with iterated exact T06 parent/source waves; compatibility unverified'
(out/'INSTALL_MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
(out/'IMPORT_AUDIT.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
(out/'ITERATED_WAVES.json').write_text(json.dumps({'scope':'conditional literal source inventory; no Lean evaluation','waves':waves},indent=2)+'\n')
print(json.dumps({'wave_summaries':[{k:v for k,v in x.items() if k!='sources'} for x in waves],
 'staged':audit['staged_count'],'visited':audit['visited_project_modules'],
 'missing':len(audit['missing_project_modules']),'external':len(audit['external_modules'])},indent=2))
