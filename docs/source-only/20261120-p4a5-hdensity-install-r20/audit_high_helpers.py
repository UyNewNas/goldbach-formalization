#!/usr/bin/env python3
"""Check the prior 12 named high-range sources and their literal imports."""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
p=ROOT/'docs/source-only/20261112-resume/t03/T01_FINE_COFINAL_ALLOWLIST.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='060921b499f9a71cdd31608b27b2ca252ac604913426a74687895cc352b95c89';x=json.loads(raw)['existing_high_sources_reached_within_that_record'];assert len(x)==12
stage=Path(sys.argv[1]).resolve(strict=True);rows=[]
for z in x:
 source=ROOT/z['path'].replace('goldbach-proof-continuation/','',1);b=source.read_bytes();sha=hashlib.sha256(b).hexdigest();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert (len(b),sha,blob)==(z['bytes'],z['sha256'],z['git_blob_sha1'])
 imports=[]
 for line in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:imports+=m.group(1).split()
 assert imports==z['imports'];target=stage/z['installation_target'];assert target.read_bytes()==b
 rows.append({'module':z['installation_target'].removesuffix('.lean').replace('/','.'),'source':str(source.relative_to(ROOT)),'sha256':sha,'git_blob_sha1':blob,'imports':imports,'target':z['installation_target']})
print(json.dumps({'scope':'12 historical helper bytes and literal direct imports, not Lean compilation','allowlist_sha256':hashlib.sha256(raw).hexdigest(),'rows':rows},indent=2))
