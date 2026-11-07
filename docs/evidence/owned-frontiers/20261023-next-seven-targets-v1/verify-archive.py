#!/usr/bin/env python3
"""Offline verifier for published owned-frontier evidence packages; stdlib only."""
import argparse, gzip, hashlib, io, json
from pathlib import Path, PurePosixPath

def sha(data): return hashlib.sha256(data).hexdigest()
def need(ok, msg):
    if not ok: raise ValueError(msg)
def safe_member(package, rel):
    p=PurePosixPath(rel)
    need(not p.is_absolute() and all(x not in ('', '.', '..') for x in p.parts), 'Unsafe manifest member: '+rel)
    target=(package.joinpath(*p.parts)).resolve()
    need(target.is_relative_to(package.resolve()) and target.is_file(), 'Missing/unsafe package member: '+rel)
    return target
def restore(package,row):
    data=safe_member(package,row['stored_path']).read_bytes()
    need(sha(data)==row['stored_sha256'], 'Stored SHA mismatch: '+row['stored_path'])
    if row['encoding']=='gzip-mtime0-empty-filename':
        need(len(data)>=10 and data[:10]==b'\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff', 'Non-canonical gzip header')
        with gzip.GzipFile(fileobj=io.BytesIO(data),mode='rb') as f: raw=f.read(row['source_bytes']+1)
    else:
        need(row['encoding']=='raw','Unknown encoding: '+str(row['encoding']))
        raw=data
    need(len(raw)==row['source_bytes'] and sha(raw)==row['source_sha256'], 'Recovered source bytes differ: '+row['original_path'])
    return raw
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,help='Repository clone root')
    ap.add_argument('--package',required=True,help='Repository-relative package path')
    args=ap.parse_args(); root=Path(args.root).resolve(); rel=PurePosixPath(args.package)
    need(not rel.is_absolute() and all(x not in ('','..') for x in rel.parts),'Unsafe package path')
    package=(root.joinpath(*rel.parts)).resolve(); need(package.is_relative_to(root) and package.is_dir(),'Missing/unsafe package')
    manifest_path=safe_member(package,'archive-manifest.json'); manifest=json.loads(manifest_path.read_bytes())
    need(isinstance(manifest.get('files'),dict) and isinstance(manifest.get('source_refs'),dict),'Unsupported archive manifest structure')
    declared=set(manifest['files']); actual={p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}
    need(actual==declared|{'archive-manifest.json'},'Package members differ from manifest files')
    for name,digest in manifest['files'].items():
        need(isinstance(name,str) and isinstance(digest,str),'Invalid files row')
        data=safe_member(package,name).read_bytes(); need(sha(data)==digest,'Manifest file SHA mismatch: '+name)
    for role,row in manifest['source_refs'].items(): restore(package,row)
    stage_raw=safe_member(package,'stage-paths.nul').read_bytes()
    need(stage_raw.endswith(b'\0'),'Stage list is not NUL terminated')
    pieces=stage_raw.split(b'\0'); need(pieces[-1]==b'','Stage list malformed')
    try: stage=[p.decode('utf-8') for p in pieces[:-1]]
    except UnicodeDecodeError as e: raise ValueError('Stage path is not UTF-8') from e
    need(all(stage),'Empty stage path')
    need(stage==sorted(set(stage)),'Stage paths must be sorted and unique')
    sources=manifest.get('publication_source_sha256')
    need(isinstance(sources,dict) and sources,'Missing published source hashes')
    expected={'.gitattributes',*sources.keys(),*(rel.as_posix()+'/'+name for name in declared|{'archive-manifest.json'})}
    need(stage==sorted(expected),'Stage list is not exactly the unique published package/source scope')
    print('PASS: manifest files, source recovery, fixed gzip metadata, and exact unique NUL stage list')
if __name__=='__main__':
    try: main()
    except Exception as exc: raise SystemExit('FAIL: '+str(exc))
