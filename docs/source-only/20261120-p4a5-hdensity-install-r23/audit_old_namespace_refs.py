#!/usr/bin/env python3
"""Textually search exact old qualified names in the hash-bound reached set."""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent;stage=Path(sys.argv[1]).resolve(strict=True);audit=json.loads((HERE/'IMPORT_AUDIT.json').read_bytes());terms=['MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiProposition118SourceTPlus','MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer_one_two_odd_nonneg'];hits=[]
for module,x in sorted(audit['visited'].items()):
 p=(stage if x['origin']=='stage' else ROOT)/x['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'];text=b.decode('utf-8-sig')
 for term in terms:
  for n,line in enumerate(text.splitlines(),1):
   if term in line:hits.append({'module':module,'line':n,'term':term})
print(json.dumps({'scope':'literal exact-name search over hash-bound source text only; not Lean name resolution','source_count':len(audit['visited']),'old_qualified_terms':terms,'hits':hits},indent=2))
