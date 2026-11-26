#!/usr/bin/env python3
"""Resolve only still-missing exact supplier names through file/dir symlinks."""
import hashlib
import json
import os
from pathlib import Path
import stat
import time
START=time.monotonic()
ROWS=PAYLOAD['rows']
WANTED={row['module'].split('.')[-1]+suffix:(i,kind) for i,row in enumerate(ROWS)
        for suffix,kind in (('.lean','source'),('.olean','object'))}
cache={}
matches=[]
variants=[]
dead=[]
aliases=[]
seen=set()
candidate_count=0
directory_links=0

def check(path,index,kind):
    global candidate_count
    try:
        real=path.resolve(strict=True)
        st=real.stat()
        if not stat.S_ISREG(st.st_mode):return
    except OSError:
        if len(dead)<30:dead.append(str(path))
        return
    key=(index,kind,str(real))
    if key in seen:return
    seen.add(key);candidate_count+=1
    filekey=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns)
    if filekey not in cache:
        h=hashlib.sha256()
        with real.open('rb') as incoming:
            for b in iter(lambda:incoming.read(1024*1024),b''):h.update(b)
        cache[filekey]={'path':str(real),'bytes':st.st_size,'sha256':h.hexdigest()}
    pin={**cache[filekey],'path':str(real)}
    expected=ROWS[index]['source'] if kind=='source' else ROWS[index]['expected_object']
    record={'module':ROWS[index]['module'],'kind':kind,'alias':str(path),'pin':pin}
    if all(pin[k]==expected[k] for k in ('bytes','sha256')):matches.append(record)
    elif kind=='object':variants.append(record)

for folder,dirs,files in os.walk('/workspace',followlinks=False):
    dirs[:]=[d for d in dirs if d not in ('.git','.compile-home','node_modules','__pycache__')
             and not ('row001' in d.lower() and 'completed' in d.lower())]
    for name in set(files).intersection(WANTED):
        path=Path(folder)/name
        if path.is_symlink():check(path,*WANTED[name])
    for name in dirs:
        path=Path(folder)/name
        if not path.is_symlink():continue
        directory_links+=1
        try:real=path.resolve(strict=True)
        except OSError:continue
        # Every real path within /workspace was covered by the prior global
        # regular-file scan. Probe standard module roots only for external roots.
        if real.is_relative_to(Path('/workspace')):continue
        aliases.append({'alias':str(path),'resolved':str(real)})
        for prefix in ('','ImbalancedChen','lib/lean/ImbalancedChen','build/lib/lean/ImbalancedChen',
                       '.lake/build/lib/lean/ImbalancedChen','project/ImbalancedChen',
                       'objects/ImbalancedChen','sources/ImbalancedChen'):
            root=path/prefix
            if not root.is_dir():continue
            for filename,(index,kind) in WANTED.items():
                candidate=root/filename
                if candidate.is_file():check(candidate,index,kind)
print(json.dumps({'schema':'p26_p3_exact_symlink_resolution_v1','status':'CHECK_COMPLETE',
                  'wanted_modules':len(ROWS),'matches':matches,'object_variants':variants,
                  'candidate_files':candidate_count,'directory_symlinks':directory_links,
                  'external_directory_aliases':aliases,'dangling_candidate_aliases':dead,
                  'elapsed_seconds':round(time.monotonic()-START,3),
                  'archives_opened':False,'proof_commands_executed':False,'remote_files_written':False,
                  'source_or_object_bodies_emitted':False},sort_keys=True,separators=(',',':')))
