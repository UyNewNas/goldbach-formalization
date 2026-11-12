"""Remote-only source graph, immutable artifact snapshot and strict serialized receipt."""
import hashlib, json, os, pathlib, re, sys
root=pathlib.Path(os.environ['PROJECT']); logs=pathlib.Path(os.environ['LOGS'])
mode=sys.argv[1]
manifest=json.loads(pathlib.Path(os.environ['DENSITY_MANIFEST']).read_text())
targets=[manifest['targets'][0]['primary_module']]
def imports(text):
    # Lean nested block comments must not create phantom imports.
    text=re.sub(r'--[^\n]*','',text)
    while '/-' in text:
        start=text.index('/-');depth=1;i=start+2
        while depth and i<len(text):
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif text[i:i+2]=='-/':depth-=1;i+=2
            else:i+=1
        assert depth==0
        text=text[:start]+' '+text[i:]
    return [m for line in text.splitlines() if re.match(r'^\s*(?:public\s+)?import\s',line) for m in re.sub(r'^\s*(?:public\s+)?import\s+','',line).split()]
seen=set();modules=[]
def visit(m):
    if m in seen:return
    p=root/(m.replace('.','/')+'.lean')
    if not p.exists():
        assert not m.startswith('ImbalancedChen.'),m
        return
    seen.add(m)
    for n in imports(p.read_text()):visit(n)
    modules.append(m)
for m in targets:visit(m)
assert set(targets)<=set(modules)
assert modules==[r['module'] for r in manifest['files']], 'Exact declared closure differs'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=list(root.glob('ImbalancedChen/**/*.lean'))
    for directory in [root/'.lake/build', *root.glob('.lake/packages/*/.lake/build')]:
        paths.extend(p for p in directory.rglob('*') if p.is_file())
    return {str(p.relative_to(root)):digest(p) for p in sorted(paths) if p.is_file()}
if mode=='prepare':
    assert manifest['mathematical_modules']==modules+sorted(r['module'] for r in manifest['native_sources'])
    assert len(manifest['mathematical_modules'])==1851
    assert manifest['fresh_kernel_modules']==manifest['mathematical_modules']+manifest['audit_wrapper_modules']
    assert len(manifest['fresh_kernel_modules'])==1854
    for record in manifest['audit_sources']:
        path=root/record['install_path']
        assert path.stat().st_size==record['bytes'] and digest(path)==record['sha256']
    (logs/'modules.txt').write_text('\n'.join(modules)+'\n')
    (logs/'kernel_modules.txt').write_text('\n'.join(manifest['fresh_kernel_modules'])+'\n')
elif mode=='snapshot':
    (logs/'BATCH_OBJECTS_BEFORE.json').write_text(json.dumps(snapshot(),sort_keys=True))
elif mode=='verify':
    before=json.loads((logs/'BATCH_OBJECTS_BEFORE.json').read_text());assert before==snapshot(),'Source/import object changed during replay/audit'
    lines=(logs/'batch-types.log').read_text().splitlines()
    ds=[json.loads(x.removeprefix('P0_ROUND6_DECL ')) for x in lines if x.startswith('P0_ROUND6_DECL ')]
    inv=[json.loads(x.removeprefix('P0_ROUND6_SERIALIZED ')) for x in lines if x.startswith('P0_ROUND6_SERIALIZED ')]
    assert {x['module'] for x in inv}==set(manifest['mathematical_modules']) and len(inv)==len(manifest['mathematical_modules'])
    assert len({x['name'] for x in ds})==len(ds)
    for m in manifest['mathematical_modules']:
        names={d['name'] for d in ds if d['module']==m};i=next(i for i in inv if i['module']==m)
        assert names==set(i['serialized_constant_names'])==set(i['environment_constant_names'])
        if 'StoredBlock' in m: assert all(m+'.'+s in names for s in ['rows','rows_size','source_index_at'])
    assert all(not(d['is_unsafe'] or d['is_partial'] or d['is_axiom']) and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and all(d[k].strip() and '⋯' not in d[k] for k in ['type','readable_type']) for d in ds)
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(manifest['fresh_kernel_modules']) and set(replay)==set(manifest['fresh_kernel_modules'])
    (logs/'BATCH_ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_EXACT_CANDIDATE_CLOSURE_ONLY','modules':manifest['fresh_kernel_modules'],'mathematical_modules':manifest['mathematical_modules'],'complete_serialized_declarations':len(ds),'source_commit':os.environ['SOURCE_COMMIT'],'whole_PP_accepted':False,'proof_artifact_hash':digest(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else:raise SystemExit('bad mode')
