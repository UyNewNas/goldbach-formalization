#!/usr/bin/env python3
"""Reconstruct the 20 T06 global alternatives from exact historical objects.

Only source bytes and their textual differences are checked. No Lean proof runs.
"""
import difflib,hashlib,json,subprocess,sys
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
T=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json';tb=T.read_bytes();assert hashlib.sha256(tb).hexdigest()=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
f={x['module']:x for x in json.loads(tb)['files']};prev=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r19';a=json.loads((prev/'IMPORT_AUDIT.json').read_bytes());v=json.loads((prev/'T06_VARIANTS.json').read_bytes())['different_edges'];counts=Counter(x['dependency'] for x in v)
stage=Path(sys.argv[1]).resolve(strict=True);out=Path(sys.argv[2]).resolve();assert ROOT not in out.parents and not out.exists();out.mkdir(parents=True)
rows=[]
for module in sorted(counts):
 x=f[module];origin=x['origin'];assert origin['kind']=='git'
 proc=subprocess.run(['git','show',origin['commit']+':'+origin['path']],cwd=ROOT,capture_output=True,check=True);b=proc.stdout
 inputsha=hashlib.sha256(b).hexdigest(); expected_input=x['pre_input']['sha256'] if x.get('transform') else x['sha256'];assert inputsha==expected_input,(module,inputsha,expected_input)
 applied=[]
 for transform in x.get('transform',[]):
  old=transform['old'].encode();new=transform['new'].encode();n=b.count(old);assert n==transform['count'],(module,n);b=b.replace(old,new);applied.append({'old':transform['old'],'new':transform['new'],'count':n})
 assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']
 target=out/(module.split('.')[-1]+'.lean');target.write_bytes(b)
 oldmeta=a['visited'][module];oldpath=(stage if oldmeta['origin']=='stage' else ROOT)/oldmeta['path'];old=oldpath.read_bytes();assert hashlib.sha256(old).hexdigest()==oldmeta['sha256']
 diff=list(difflib.unified_diff(old.decode('utf-8-sig').splitlines(),b.decode('utf-8-sig').splitlines(),fromfile='r19-selected',tofile='t06-alternative',lineterm=''))
 oldimports=[l for l in old.decode('utf-8-sig').splitlines() if l.lstrip().startswith('import ')]
 newimports=[l for l in b.decode('utf-8-sig').splitlines() if l.lstrip().startswith('import ')]
 rows.append({'module':module,'edge_count':counts[module],'r19_sha256':oldmeta['sha256'],'t06_sha256':x['sha256'],'t06_blob':x['git_blob_sha1'],'origin':origin,'origin_input_sha256':inputsha,'transform':applied,'imports_changed':oldimports!=newimports,'diff':diff})
(HERE/'RECONSTRUCTED_VARIANTS.json').write_text(json.dumps({'scope':'exact T06 alternative source reconstruction and literal diff; no compatibility or proof judgment','rows':rows},indent=2,ensure_ascii=False)+'\n')
print('modules',len(rows),'edges',sum(x['edge_count'] for x in rows),'transformed',sum(bool(x['transform']) for x in rows),'import_changes',sum(x['imports_changed'] for x in rows))
for x in rows:
 print(x['module'],x['edge_count'],'diff_lines',sum(l.startswith(('+','-')) and not l.startswith(('+++','---')) for l in x['diff']),'import_change',x['imports_changed'],'transform',len(x['transform']))
