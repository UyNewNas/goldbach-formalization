"""Bind and check the exact staged P1 candidate; never invokes Lean."""
import hashlib, json, os, pathlib, re, subprocess, sys
root=pathlib.Path(os.environ['PROJECT'])
logs=pathlib.Path(os.environ['LOGS'])
runner=pathlib.Path(os.environ['GITHUB_WORKSPACE'])
mode=sys.argv[1]
manifest=json.loads(pathlib.Path(__file__).with_name('candidate.json').read_text())
ref=manifest['ref']
assert ref == os.environ['SOURCE_COMMIT']
targets=[manifest['target']]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(b): return hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()
def name_path(m): return pathlib.Path(m.replace('.','/')+'.lean')
if mode=='stage':
    git=['git','-C',str(runner/'candidate')]
    assert subprocess.check_output(git+['rev-parse','HEAD'],text=True).strip()==ref
    root.mkdir(exist_ok=False)
    logs.mkdir(exist_ok=False)
    items=[(f,f,b) for f,b in manifest['config'].items()]
    items.extend((x['path'],name_path(x['m']),x['sha']) for x in manifest['modules'])
    for src,dest,expected in items:
        b=subprocess.check_output(git+['cat-file','blob',ref+':'+src])
        assert blob(b)==expected,src
        p=root/dest
        p.parent.mkdir(parents=True,exist_ok=True)
        with p.open('xb') as out: out.write(b)
    (logs/'SOURCE_BINDING.json').write_text(json.dumps(manifest,indent=2)+'\n')
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

assert modules==[x['m'] for x in manifest['modules']], 'Unexpected local closure'
for record in manifest['modules']:
    p=root/name_path(record['m'])
    assert blob(p.read_bytes())==record['sha']
    assert imports(p.read_text())==record['deps'], record['m']
def snapshot():
    paths=[root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json']
    paths+=list(root.glob('ImbalancedChen/**/*.lean')) + list(root.glob('.lake/build/lib/lean/**/*.olean*')) + list(root.glob('.lake/packages/*/.lake/build/lib/lean/**/*.olean*'))
    return {str(p.relative_to(root)):sha(p) for p in sorted(paths) if p.is_file()}
if mode=='stage':
    pass
elif mode=='prepare':
    source=runner/'verification/parts/p0/p5-original-common-brun-power-reserve-api/Round6AuditTemplate.lean'
    assert blob(source.read_bytes())=='5a69afa2fb5034594ad5b7ef7b9443793483cf01'
    audit=source.read_text();audit=audit[audit.index('set_option pp.all'):]
    start=audit.index('  let modules := #[');end=audit.index('  let allowed :=',start)
    audit=audit[:start]+'  let modules := #['+','.join('`'+m for m in modules)+']\n'+audit[end:]
    audit=audit.replace('  if names.contains finalBridge then\n    throwError "Final bridge must not be included in the owned-module census"\n','').replace('(names.push finalBridge).qsort','names.qsort')
    start=audit.index('    if name == finalBridge then');end=audit.index('  for (m, count) in counts do',start)
    audit=audit[:start]+'    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"\n'+audit[end:]
    audit='\n'.join('import '+m for m in modules)+'\nimport Lean.Util.CollectAxioms\n'+audit
    (root/'CandidateAudit.lean').write_text(audit)
    (logs/'modules.txt').write_text('\n'.join(modules)+'\n')
elif mode=='snapshot':
    (logs/'BATCH_OBJECTS_BEFORE.json').write_text(json.dumps(snapshot(),sort_keys=True))
elif mode=='verify':
    before=json.loads((logs/'BATCH_OBJECTS_BEFORE.json').read_text());assert before==snapshot(),'Source/import object changed during replay/audit'
    lines=(logs/'batch-types.log').read_text().splitlines()
    ds=[json.loads(x.removeprefix('P0_ROUND6_DECL ')) for x in lines if x.startswith('P0_ROUND6_DECL ')]
    inv=[json.loads(x.removeprefix('P0_ROUND6_SERIALIZED ')) for x in lines if x.startswith('P0_ROUND6_SERIALIZED ')]
    assert {x['module'] for x in inv}==set(modules) and len(inv)==len(modules)
    assert len({x['name'] for x in ds})==len(ds)
    for m in modules:
        names={d['name'] for d in ds if d['module']==m}; i=next(r for r in inv if r['module']==m)
        assert names and names==set(i['serialized_constant_names'])==set(i['environment_constant_names'])
    assert all(d['module'] in modules and not (d['is_unsafe'] or d['is_partial'] or d['is_axiom']) and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and all(d[k].strip() and '⋯' not in d[k] for k in ['type','readable_type']) for d in ds)
    result=[d for d in ds if d['name']==targets[0]+'.exists_common_trim_and_local_support_reserve' and d['module']==targets[0] and d['kind']=='theorem']
    assert len(result)==1
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(modules) and set(replay)==set(modules)
    (logs/'BATCH_ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_EXACT_CANDIDATE_AND_LOCAL_CLOSURE_ONLY','modules':modules,'complete_serialized_declarations':len(ds),'source_commit':ref,'target':result[0],'whole_P1_accepted':False,'proof_artifact_hash':sha(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else: raise SystemExit('unexpected mode')
