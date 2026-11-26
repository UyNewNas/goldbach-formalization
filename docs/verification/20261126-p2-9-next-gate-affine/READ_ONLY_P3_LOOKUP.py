from pathlib import Path
import os,json,hashlib,time
W=Path('/workspace')
targets=['P2FiniteMarkedGamma5NonradialSupport','FinitePrimeGeometryCore']
mods=['ImbalancedChen.'+n for n in targets]
expected_sources={'P2FiniteMarkedGamma5NonradialSupport':'3d6f71b982a984e7fdd880b21ab496237ebeb656bed24990dedcfec96dff74bd','FinitePrimeGeometryCore':'becd322d719aa8ae9f0cc7b3bedbc19b87edd347bbc79788ce8f6ca7e5694d85'}
report={'schema':'p29_gate_two_supplier_read_only_lookup_v1','time_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'exact_basenames':targets,'lean_calls':0,'writes':0,'roots':[],'sources':[],'objects':[],'producer_records':[],'bounded_search':True}
def digest(p):
    p=Path(p);st=p.stat();h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(1<<20):h.update(b)
    st2=p.stat()
    return {'path':str(p),'bytes':st.st_size,'sha256':h.hexdigest(),'mtime_ns':st.st_mtime_ns,'inode':st.st_ino,'stable_before_after':(st.st_ino,st.st_size,st.st_mtime_ns)==(st2.st_ino,st2.st_size,st2.st_mtime_ns)}
roots=[]
for p in sorted(W.iterdir()):
    if p.is_dir() and not p.is_symlink() and (p.name.startswith(('goldbach','p2-','p3-','p29-')) or p.name in ['cache','caches','lean-cache','compiler-cache'] or (p/'lakefile.toml').is_file() or (p/'lakefile.lean').is_file()):
        roots.append(p)
skip={'.git','packages','node_modules','mathlib','Mathlib','MathlibNt','docs','evidence','received','lean-action','toolchains','vendor','__pycache__'}
record_names={'records.json','report.json','prepare-state.json','BORROWED_OBJECTS.json','SOURCE_OBJECT_BINDING.json','production.json','PRODUCTION.json','latest.json'}
record_paths=set();seen_objects=set();seen_sources=set()
for root in roots:
    searches=[]
    for sub in ['.lake','cache','caches','project/.lake','suppliers']:
        p=root/sub
        if p.is_dir() and not p.is_symlink():searches.append(p)
    report['roots'].append({'root':str(root),'searched_subroots':[str(p) for p in searches]})
    for prefix in [root,root/'project']:
        for name in targets:
            p=prefix/'ImbalancedChen'/(name+'.lean')
            if p.is_file() and str(p.resolve()) not in seen_sources:
                row=digest(p);row['matches_selected_source']=row['sha256']==expected_sources[name];row['direct_imports']=[l[7:] for l in p.read_text().splitlines() if l.startswith('import ')]
                report['sources'].append(row);seen_sources.add(str(p.resolve()))
    for start in searches:
        for d,dirs,files in os.walk(start,followlinks=False):
            dirs[:]=[n for n in dirs if n not in skip and not Path(d,n).is_symlink()]
            for name in targets:
                fn=name+'.olean'
                if fn not in files:continue
                p=Path(d,fn);resolved=str(p.resolve())
                if resolved in seen_objects:continue
                seen_objects.add(resolved);row=digest(p);row['module']='ImbalancedChen.'+name;row['project_root']=str(root);row['adjacent_facets']=[]
                for suffix in ['.olean.hash','.ilean','.ilean.hash','.olean.server','.olean.private','.trace','.setup.json']:
                    q=Path(d,name+suffix)
                    if q.is_file():
                        rec=digest(q)
                        if suffix in ['.olean.hash','.ilean.hash','.trace','.setup.json'] and q.stat().st_size<=131072:rec['text']=q.read_text(errors='replace')
                        row['adjacent_facets'].append(rec)
                report['objects'].append(row)
            if str(start).endswith('/.lake'):
                for n in record_names.intersection(files):
                    p=Path(d,n)
                    if p.stat().st_size<=67108864:record_paths.add(p)
    for p in [root/'BORROWED_OBJECTS.json',root/'verification/BORROWED_OBJECTS.json',root/'project/verification/BORROWED_OBJECTS.json']:
        if p.is_file():record_paths.add(p)
def relevant_key(k):
    return any(k==m or k.endswith('/'+n+'.lean') or k.endswith('/'+n+'.olean') for n,m in zip(targets,mods))
def select(x,loc='$'):
    out=[]
    if isinstance(x,dict):
        if x.get('module') in mods:
            return [{'json_path':loc,'record':x}]
        for k,v in x.items():
            if relevant_key(k):out.append({'json_path':loc+'.'+k,'record':v})
            elif isinstance(v,(dict,list)):out.extend(select(v,loc+'.'+k))
    elif isinstance(x,list):
        for i,v in enumerate(x):
            if isinstance(v,(dict,list)):out.extend(select(v,loc+'['+str(i)+']'))
    return out
for p in sorted(record_paths):
    raw=p.read_bytes()
    if not any(n.encode() in raw for n in targets):continue
    try:x=json.loads(raw)
    except Exception as e:report['producer_records'].append({'path':str(p),'parse_error':str(e)});continue
    rows=select(x)
    if rows:rec=digest(p);rec['matching_records']=rows;report['producer_records'].append(rec)
report['candidate_producer_files_checked']=len(record_paths)
report['object_count']=len(report['objects'])
report['qualification']='Presence and exact byte matching only. No imported closure or new compile/kernel credit is granted by this lookup.'
print(json.dumps(report,ensure_ascii=False,sort_keys=True))
