"""Materialize accepted source/object pairs, without touching Lake or running Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import zipfile

PARENT = 'ImbalancedChen.P5SubdivisionStoredParentTypes'
AGG = 'ImbalancedChen.P5SubdivisionStoredParentArchive'
PREFIX = 'ImbalancedChen.Data.P5SubdivisionStoredBlock'
REGEX = r'ImbalancedChen\.(?:P5SubdivisionStoredParentTypes|Data\.P5SubdivisionStoredBlock[0-9]{3})'
WORK_ROOT = '/home/runner/work/_temp/t01-project/'
PARENT_SOURCE = '87f1a913c44347bac32b2ed3458b4e16e136a81a0e7d98f38b4296d722a44a0e'
PARENT_OLEAN = '5279a69ca840610060458af722024d79af001be859eb1f8efc78d7c15ae7c2af'
COHORTS = ((0,4),(5,8),(9,19),(20,30),(31,41),(42,52),(53,63),(64,71))
LATE = {
    '053-063': [14055053555, 457455858, 'ee0171d3ef0bfed16ed6da993184e0b2ec83e5877cc00b689919d9aa8307bbbe'],
    '064-071': [14084344602, 402834046, 'f4983f48f5b24f3f02eb04415bd3d47c0390aa84095714c6a28ea4b430640160'],
}
AGG_SOURCE = 'ed93ab0ca2a1b6e3f537c5349baa60f13d94b9cae26abd161364e67b5d4d07c0'

def need(condition, error):
    if not condition:
        raise ValueError(error)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def checked_read(z, member, expected, size=None):
    matches = [i for i in z.infolist() if i.filename == member]
    need(len(matches) == 1 and not matches[0].is_dir(), 'missing or ambiguous ZIP member: '+member)
    if size is not None:
        need(matches[0].file_size == size, 'ZIP member length differs: '+member)
    data = z.read(matches[0])
    need(sha(data) == expected, 'ZIP member hash differs: '+member)
    return data

def coherent_index(z):
    paths = {}
    for line in z.read('RAW_FILES.jsonl').splitlines():
        row = json.loads(line)
        if row['original_path'].startswith(WORK_ROOT):
            path = row['original_path'][len(WORK_ROOT):]
            need(path not in paths, 'duplicate original coherent path: '+path)
            paths[path] = row
    return paths

def coherent_payload(z, idx, path, expected):
    row = idx.get(path, {})
    name = row.get('payload', '')
    need(row.get('sha256') == expected and name == 'objects/'+expected,
         'coherent locator or actual payload absent: '+path)
    return checked_read(z, name, expected, row['bytes'])

def stage_pair(out, module, source, olean, source_hash, olean_hash):
    need(bool(re.fullmatch(REGEX,module)), 'unexpected Lean module name')
    need(sha(source) == source_hash and sha(olean) == olean_hash, 'unbound pair: '+module)
    stem = module.replace('.', '/')
    paths = (out/'source'/(stem+'.lean'), out/'lib'/(stem+'.olean'))
    if any(p.exists() or p.is_symlink() for p in paths):
        raise FileExistsError(module)
    for p,data in zip(paths,(source,olean)):
        p.parent.mkdir(parents=True, exist_ok=True)
        need(p.parent.resolve() == p.parent.absolute(), 'symlink in output ancestry')
        with p.open('xb') as f:
            f.write(data)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archives',type=Path,required=True)
    parser.add_argument('--lock-index',type=Path,required=True)
    parser.add_argument('--lock-index-sha',required=True)
    parser.add_argument('--artifact-index',type=Path,required=True)
    parser.add_argument('--artifact-index-sha',required=True)
    parser.add_argument('--out',type=Path,required=True)
    a=parser.parse_args()
    lock_bytes, artifact_bytes = a.lock_index.read_bytes(), a.artifact_index.read_bytes()
    need(sha(lock_bytes)==a.lock_index_sha and sha(artifact_bytes)==a.artifact_index_sha, 'lock/index digest changed')
    lock = json.loads(lock_bytes)
    manifest={x['cohort']:x for x in json.loads(artifact_bytes)}
    need(lock['status']=='STATIC_HISTORICAL_SNAPSHOT_MATCH_ONLY' and lock['target']==AGG and
         lock['target_source_sha256']==AGG_SOURCE and lock['parent_olean']==PARENT_OLEAN, 'wrong receiver lock')
    need(set(lock['blocks'])=={PREFIX+f'{i:03}' for i in range(72)}, 'block source set changed')
    out=a.out.absolute()
    need(out.parent.is_dir() and out.parent.resolve()==out.parent, 'output parent must be physical and present')
    out.mkdir(mode=0o700)
    receipts={}
    for lo,hi in COHORTS:
        label=f'{lo:03}-{hi:03}'
        archive=a.archives/(label+'.zip')
        row=manifest[label]
        aid, size, expected=LATE.get(label, [row['artifact'],row['bytes'],row['sha256']])
        with archive.open('rb') as f:
            actual=hashlib.file_digest(f,'sha256').hexdigest()
        need(archive.stat().st_size==size and actual==expected, 'archive bytes differ: '+label)
        with zipfile.ZipFile(archive) as z:
            idx=coherent_index(z) if label in LATE else None
            for i in range(lo,hi+1):
                name=PREFIX+f'{i:03}'
                stem=name.replace('.','/')
                rec=lock['blocks'][name]
                sh,oh=rec['source_sha256'],rec['olean_sha256']
                if idx is None:
                    member='compiled-blocks/'+name.rsplit('.',1)[1]
                    source=checked_read(z,member+'.lean',sh)
                    olean=checked_read(z,member+'.olean',oh)
                else:
                    source=coherent_payload(z,idx,stem+'.lean',sh)
                    olean=coherent_payload(z,idx,'.lake/build/lib/lean/'+stem+'.olean',oh)
                stage_pair(out,name,source,olean,sh,oh)
                receipts[name]={'artifact_id':aid,'source_sha256':sh,'olean_sha256':oh}
            if label=='020-030':
                member='compiled-parent/P5SubdivisionStoredParentTypes'
                src=checked_read(z,member+'.lean',PARENT_SOURCE)
                obj=checked_read(z,member+'.olean',PARENT_OLEAN)
                stage_pair(out,PARENT,src,obj,PARENT_SOURCE,PARENT_OLEAN)
                receipts[PARENT]={'artifact_id':aid,'source_sha256':PARENT_SOURCE,'olean_sha256':PARENT_OLEAN}
    need(len(receipts)==73, 'incomplete staged file census')
    result={'status':'VERIFIED_PAIRS_MATERIALIZED_NOT_IMPORTED','modules':receipts,
            'lock_sha256':a.lock_index_sha, 'artifact_index_sha256':a.artifact_index_sha,
            'package_facets_verified_in_current_runner':False,
            'lean_source_compiler_started':False,'lake_cache_qualified':False,
            'new_proof_accepted':False, 'next':'verify original parent stock restore and warm package hashes before any import'}
    with (out/'TRANSPORT_RECEIPT.json').open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print(result['status'], len(receipts))

if __name__ == '__main__':
    main()
