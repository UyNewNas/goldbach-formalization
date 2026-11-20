#!/usr/bin/env python3
"""Compare exact-parent literal edges with T06's global source selections.

Differences identify candidate reconciliation work, not kernel incompatibility.
"""
import hashlib,json
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
p=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json';b=p.read_bytes();assert hashlib.sha256(b).hexdigest()=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
t=json.loads(b);files={x['module']:x for x in t['files']};a=json.loads((HERE/'IMPORT_AUDIT.json').read_bytes());rows=[]
for parent,x in sorted(a['visited'].items()):
 p=files.get(parent)
 if not p or p['sha256']!=x['sha256']:continue
 for dep in x['imports']:
  if dep not in p['imports'] or dep not in files or dep not in a['visited']:continue
  expected=files[dep]['sha256'];actual=a['visited'][dep]['sha256'];rows.append({'parent':parent,'parent_sha256':x['sha256'],'dependency':dep,'t06_global_sha256':expected,'staged_sha256':actual,'status':'match' if expected==actual else 'different_global_selection'})
print(json.dumps({'scope':'T06 source-only global selected hashes on exact-parent recorded edges; mismatches require version reconciliation and do not by themselves establish Lean failure','counts':dict(Counter(x['status'] for x in rows)),'different_edges':[x for x in rows if x['status']!='match']},indent=2))
