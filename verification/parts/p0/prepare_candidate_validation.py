"""Materialize reviewed kernel-bounded proof expressions; never invokes Lean."""
import hashlib, json, os, pathlib, re, sys
root=pathlib.Path(os.environ['PROJECT']); logs=pathlib.Path(os.environ['LOGS'])
mode=sys.argv[1]
targets=['ImbalancedChen.Certificates.P2ThirdZeroGeometry','ImbalancedChen.Certificates.P2HybridThirdChargeLedger']
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
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=list(root.glob('ImbalancedChen/**/*.lean'))+list(root.glob('.lake/build/lib/lean/**/*.olean*'))+list(root.glob('.lake/packages/*/.lake/build/lib/lean/**/*.olean*'))
    return {str(p.relative_to(root)):digest(p) for p in sorted(paths) if p.is_file()}
if mode=='prepare':
    source=pathlib.Path(os.environ['GITHUB_WORKSPACE'])/'verification/parts/p0/Round6Audit.lean'
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
        names={d['name'] for d in ds if d['module']==m};i=next(i for i in inv if i['module']==m)
        assert names==set(i['serialized_constant_names'])==set(i['environment_constant_names'])
        if 'StoredBlock' in m: assert all(m+'.'+s in names for s in ['rows','rows_size','source_index_at'])
    assert all(not(d['is_unsafe'] or d['is_partial'] or d['is_axiom']) and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and all(d[k].strip() and '⋯' not in d[k] for k in ['type','readable_type']) for d in ds)
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(modules) and set(replay)==set(modules)
    (logs/'BATCH_ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_EXACT_CANDIDATE_CLOSURE_ONLY','modules':modules,'complete_serialized_declarations':len(ds),'source_commit':os.environ['SOURCE_COMMIT'],'whole_p2_accepted':False,'proof_artifact_hash':digest(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else:raise SystemExit('bad mode')
