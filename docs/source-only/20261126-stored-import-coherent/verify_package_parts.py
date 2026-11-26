"""Fail closed on missing, mismatched, or shadowed parent package facets. Never run Lean."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from collections import Counter

LOCK_SHA = '22003ce8e81821ce0421dd1263c52405000641d5480e88e9fb530caade82ae10'
EXPECTED = Counter({'olean': 133, 'private':133, 'server':133, 'ir':133, 'sig':133})

def read_lock(path):
    data=path.read_bytes()
    if hashlib.sha256(data).hexdigest()!=LOCK_SHA:
        raise ValueError('package-lock digest differs')
    obj=json.loads(data)
    if len(obj)!=665 or Counter(name.rsplit('.',1)[-1] for name in obj)!=EXPECTED:
        raise ValueError('package-lock member census differs')
    for k,h in obj.items():
        pp=PurePosixPath(k)
        if pp.is_absolute() or pp.parts[:2]!=('.lake','packages') or '..' in pp.parts or not re.fullmatch('[0-9a-f]{64}',h):
            raise ValueError('unreviewed package path/hash: '+k)
    return obj

def verify(project, lock):
    project=project.resolve(strict=True)
    report={'missing':[], 'mismatched':[], 'nonphysical':[], 'verified':0}
    for rel,expected in lock.items():
        path=project/rel
        if path.resolve()!=path:
            report['nonphysical'].append(rel); continue
        if not path.is_file():
            report['missing'].append(rel); continue
        with path.open('rb') as stream:
            val=hashlib.file_digest(stream,'sha256').hexdigest()
        if val != expected:
            report['mismatched'].append(rel); continue
        report['verified'] += 1
    report['status']='PASS_PACKAGE_BYTES_ONLY' if report['verified']==len(lock) else 'BLOCK_PACKAGE_BYTES'
    report['package_lock_sha256']=LOCK_SHA
    report['lean_invoked']=False
    report['cache_qualified']=False
    report['proof_accepted']=False
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project',type=Path,required=True)
    p.add_argument('--lock',type=Path,required=True)
    p.add_argument('--report',type=Path,required=True)
    a=p.parse_args()
    result=verify(a.project,read_lock(a.lock))
    with a.report.open('x') as file:
        json.dump(result,file,indent=2,sort_keys=True); file.write('\n')
    print(result['status'], 'verified', result['verified'], 'missing',len(result['missing']),
          'mismatched',len(result['mismatched']),'nonphysical',len(result['nonphysical']))
    return int(result['status'] != 'PASS_PACKAGE_BYTES_ONLY') * 2

if __name__=='__main__':
    sys.exit(main())
