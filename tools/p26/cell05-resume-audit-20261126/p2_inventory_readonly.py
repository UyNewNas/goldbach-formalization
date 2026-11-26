#!/usr/bin/env python3
"""Read only exact Cell05 supplier/target filenames and explicit metadata pins."""
from pathlib import Path
import collections
import hashlib
import json
import os
import stat
import time

START=time.monotonic()
BASE=Path('/workspace/p26-continuation-59264dd64286')
SUPPLIERS=PAYLOAD['suppliers']
TARGETS=PAYLOAD['targets']
CACHE={}
found=collections.defaultdict(dict)
target_found=collections.defaultdict(dict)
variants=collections.defaultdict(list)
extras=[]
errors=[]


def fp(path):
    path=Path(path)
    if 'row001' in str(path).lower():raise ValueError('row001 excluded')
    real=path.resolve(strict=True)
    if not real.is_relative_to(Path('/workspace')):raise ValueError('outside workspace')
    st=real.stat()
    if not stat.S_ISREG(st.st_mode):raise ValueError('not regular')
    key=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns)
    if key not in CACHE:
        h=hashlib.sha256()
        with real.open('rb') as incoming:
            for block in iter(lambda:incoming.read(1024*1024),b''):h.update(block)
        after=real.stat()
        if (after.st_size,after.st_mtime_ns)!=(st.st_size,st.st_mtime_ns):raise ValueError('file changed')
        CACHE[key]={'bytes':st.st_size,'sha256':h.hexdigest()}
    return {'path':str(real),**CACHE[key]}


def same(actual,expected):
    return all(actual.get(k)==expected.get(k) for k in ('bytes','sha256'))


def candidate(path,index,kind,target=False):
    if not path.is_file():return
    try:actual=fp(path)
    except (OSError,ValueError) as e:
        errors.append({'path':str(path),'error':str(e)});return
    row=TARGETS[index] if target else SUPPLIERS[index]
    if target:
        if kind=='object':target_found[index].setdefault('objects',[]).append(actual)
        elif same(actual,row['source']):target_found[index].setdefault('source',actual)
    elif same(actual,row[kind]):found[index].setdefault(kind,actual)
    elif kind=='object' and len(variants[index])<8:variants[index].append(actual)


for i,row in enumerate(SUPPLIERS):
    rel=row['module'].replace('.','/')
    for label in ('fields73','rows15'):
        root=Path(PAYLOAD['batches'][label]['stage'])
        for kind,directory,suffix in [('source','project','.lean'),('object','objects','.olean')]:
            if kind not in found[i]:candidate(root/directory/(rel+suffix),i,kind)

wanted={}
for i,row in enumerate(SUPPLIERS):
    for kind,suffix in [('source','.lean'),('object','.olean')]:
        if kind not in found[i]:wanted[row['module'].split('.')[-1]+suffix]=(i,kind,False)
for i,row in enumerate(TARGETS):
    for kind,suffix in [('source','.lean'),('object','.olean')]:
        wanted[row['module'].split('.')[-1]+suffix]=(i,kind,True)
directories=0
for folder,dirs,files in os.walk('/workspace',followlinks=False):
    dirs[:]=[d for d in dirs if d not in ('.git','.compile-home','node_modules','__pycache__') and 'row001' not in d.lower()]
    directories+=1
    if time.monotonic()-START>100:
        errors.append({'scan_budget_exceeded':True});break
    for name in set(files).intersection(wanted):candidate(Path(folder)/name,*wanted[name])
    if 'p26' in folder:
        for name in files:
            lower=name.lower()
            if ('row' in lower and 'capsule' in lower and lower.endswith(('.tar.xz','.json'))) or \
                    (name in ('SUPPLIER_JOIN.json','RUNTIME_GUARD.json') and ('cell05' in folder or 'connections' in folder)) or \
                    (name.endswith('.py') and 'connections' in folder and ('verify' in lower or 'export' in lower or 'join' in lower)):
                try:extras.append(fp(Path(folder)/name))
                except (OSError,ValueError) as e:errors.append({'path':str(Path(folder)/name),'error':str(e)})

metadata=[]
for label,spec in PAYLOAD['batches'].items():
    for key in ('archive','run','success'):
        expected=spec[key];path=Path(expected['path']);actual=fp(path) if path.is_file() else None
        metadata.append({'label':label,'kind':key,'expected':expected,'actual':actual,'matches':bool(actual and same(actual,expected))})
for label,expected in [('runtime_snapshot',PAYLOAD['runtime_snapshot']),*PAYLOAD['runtime_binaries'].items()]:
    path=Path(expected['path']);actual=fp(path) if path.is_file() else None
    metadata.append({'label':label,'expected':expected,'actual':actual,'matches':bool(actual and same(actual,expected))})

result=[]
for i,row in enumerate(SUPPLIERS):
    result.append({'module':row['module'],'evidence_basis':row['evidence_basis'],
                   'source':found[i].get('source'),'object':found[i].get('object'),
                   'object_variants':variants[i]})
targets=[{'module':row['module'],**target_found[i]} for i,row in enumerate(TARGETS)]
disk=os.statvfs('/workspace')
print(json.dumps({'schema':'p26_cell05_p2_resume_readonly_inventory_v1',
                  'status':'METADATA_FINISHED' if not errors else 'METADATA_ERRORS_OR_PARTIAL',
                  'supplier_count':103,'source_matches':sum(x['source'] is not None for x in result),
                  'object_matches':sum(x['object'] is not None for x in result),'suppliers':result,
                  'new_targets':targets,'explicit_metadata':metadata,'other_cell05_capsule_join_runner_locators':extras,
                  'runtime_root_directories':[{'path':x['physical_root'],'exists':Path(x['physical_root']).is_dir()} for x in PAYLOAD['runtime_roots']],
                  'workspace_free_bytes':disk.f_bavail*disk.f_frsize,'directories_scanned':directories,
                  'unique_file_hashes':len(CACHE),'errors':errors,'elapsed_seconds':round(time.monotonic()-START,3),
                  'proof_commands_executed':False,'old_files_written':False,'remote_files_written':False,
                  'archives_unpacked':False,'row001_files_accessed':False},sort_keys=True,separators=(',',':')))
