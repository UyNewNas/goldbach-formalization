"""Validate the exact P1 common local support reserve source without proof edits."""
import hashlib, json, os, pathlib, re, subprocess, sys, tomllib
root=pathlib.Path(os.environ['PROJECT'])
logs=pathlib.Path(os.environ['LOGS'])
runner=pathlib.Path(os.environ['GITHUB_WORKSPACE'])
mode=sys.argv[1]
manifest=json.loads(pathlib.Path(__file__).with_name('candidate.json').read_text())
ref=manifest['ref']
assert ref == os.environ['SOURCE_COMMIT']
targets=manifest['targets']
patches={p['m']:p for p in manifest['patches']}
assert len(targets)==1 and not patches
source_specs={pathlib.Path(x['path']):x for x in manifest['modules']}
assert len(source_specs)==len(manifest['modules'])==47
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
project_limits=('maxRecDepth=50000','maxHeartbeats=40000000')
def blob(b): return hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()
def name_path(m): return pathlib.Path(m.replace('.','/')+'.lean')
lint_manifest_path=pathlib.Path(__file__).with_name('strict_lint_compat.json')
lint_manifest=json.loads(lint_manifest_path.read_text())
assert lint_manifest['source']==ref
lint={pathlib.Path(row['path']):row for row in lint_manifest['rows']}
assert len(lint)==len(lint_manifest['rows'])==0 and set(lint)<=set(source_specs)
assert {source_specs[p]['m'] for p in lint}.isdisjoint(targets)
def apply_lint_compat(b, row):
    assert blob(b)==row['base_blob'] and hashlib.sha256(b).hexdigest()==row['base_sha256']
    lines=b.decode().split('\n')
    for number,(old,new) in row['edits'].items():
        i=int(number)-1
        assert lines[i]==old and old!=new
        lines[i]=new
    effective='\n'.join(lines).encode()
    assert blob(effective)==row['post_blob'] and hashlib.sha256(effective).hexdigest()==row['post_sha256']
    for number,(old,new) in row['edits'].items():
        i=int(number)-1
        assert lines[i]==new
        lines[i]=old
    assert '\n'.join(lines).encode()==b
    return effective
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
        entry=source_specs.get(pathlib.Path(src))
        pch=patches.get(entry['m']) if entry else None
        if pch:
            assert hashlib.sha256(b).hexdigest()==pch['base_sha256'],src
            original=b
            for old,new in pch['patches']:
                old,new=old.encode(),new.encode()
                assert b.count(old)==1,src
                b=b.replace(old,new,1)
            assert hashlib.sha256(b).hexdigest()==pch['effective_sha256'],src
            effective=b
            for old,new in reversed(pch['patches']):
                old,new=old.encode(),new.encode()
                assert b.count(new)==1,src
                b=b.replace(new,old,1)
            assert b==original,src
            b=effective
            assert blob(b)==pch['candidate_blob'],src
        row=lint.get(pathlib.Path(src))
        if row:
            assert not pch
            b=apply_lint_compat(b,row)
        p=root/dest
        p.parent.mkdir(parents=True,exist_ok=True)
        with p.open('xb') as out: out.write(b)
    (logs/'SOURCE_BINDING.json').write_text(json.dumps(manifest,indent=2)+'\n')
    (logs/'STRICT_LINT_COMPAT.json').write_bytes(lint_manifest_path.read_bytes())
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
    expected=lint.get(pathlib.Path(record['path']),{}).get('post_blob',record['sha'])
    assert blob(p.read_bytes())==patches.get(record['m'],{}).get('candidate_blob',expected)
    assert imports(p.read_text())==record['deps'], record['m']
def snapshot():
    paths=[root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json']
    paths+=list(root.glob('ImbalancedChen/**/*.lean')) + list(root.glob('.lake/build/lib/lean/**/*.olean*')) + list(root.glob('.lake/packages/*/.lake/build/lib/lean/**/*.olean*'))
    return {str(p.relative_to(root)):sha(p) for p in sorted(paths) if p.is_file()}
def bind_project_runtime():
    conf=root/'lakefile.toml'
    old=conf.read_bytes()
    assert blob(old)==manifest['config']['lakefile.toml']
    assert old.endswith(b'name = "ImbalancedChen"\n')
    new=old+b'moreLeanArgs = ["-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]\n'
    parsed=tomllib.loads(new.decode())
    assert parsed['lean_lib'][0].pop('moreLeanArgs')==['-D'+x for x in project_limits]
    assert parsed==tomllib.loads(old.decode())
    conf.write_bytes(new)
    (logs/'PROJECT_LEAN_OPTIONS.json').write_text(json.dumps({
        'original_config_blob':blob(old),'effective_config_blob':blob(new),
        'cli_options':list(project_limits),'strict_targets':targets,'strict_source_proofs_changed':False},indent=2)+'\n')

def assert_runtime_options(records, expected):
    actual={}
    strict={str(root/name_path(m)) for m in targets}|{str(root/'CandidateAudit.lean')}
    for e in records:
        if e['tool']!='lean':
            continue
        args=e['command'][1:]
        files=[p for p in args if p in expected]
        if not files:
            continue
        assert len(files)==1
        assert args[:3]==['-t0','-j2','-M12288'],(files,args[:3])
        settings=[]
        for i,arg in enumerate(args):
            if arg=='-D':
                assert i+1<len(args)
                settings.append(args[i+1])
            elif arg.startswith('-D'):
                settings.append(arg[2:])
        for opt in project_limits:
            key=opt.split('=',1)[0]
            assert [x for x in settings if x.split('=',1)[0]==key]==[opt],(files,key,settings)
        assert [x for x in settings if x.split('=',1)[0]=='warningAsError']==(['warningAsError=true'] if files[0] in strict else []), (files,settings)
        actual[files[0]]=actual.get(files[0],0)+1
    assert set(actual)==expected, sorted(expected-set(actual))
    return actual

if mode=='stage':
    pass
elif mode=='bind_project_runtime':
    bind_project_runtime()
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
    options=json.loads((logs/'PROJECT_LEAN_OPTIONS.json').read_text())
    assert options['effective_config_blob']==blob((root/'lakefile.toml').read_bytes())
    assert options['cli_options']==list(project_limits)
    inputs={str(root/name_path(m)) for m in modules}|{str(root/'CandidateAudit.lean'),'CandidateAudit.lean'}
    records=[json.loads(l) for l in (logs/'runtime/compiler-commands.jsonl').read_text().splitlines()]
    # The owned-audit invocation can use its absolute or relative project path.
    audit_abs=str(root/'CandidateAudit.lean')
    for e in records:
        if e['tool']=='lean' and e.get('cwd')==str(root):
            e['command']=[audit_abs if x=='CandidateAudit.lean' else x for x in e['command']]
    inputs.remove('CandidateAudit.lean')
    observed=assert_runtime_options(records, inputs)
    (logs/'PROJECT_LEAN_OPTIONS_ACTUAL.json').write_text(json.dumps(observed,sort_keys=True,indent=2)+'\n')
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
    actual={m:{d['name'] for d in ds if d['module']==m} for m in modules}
    endpoint=manifest['accepted_endpoint']
    assert endpoint in actual[targets[0]], endpoint
    assert next(d for d in ds if d['name']==endpoint)['kind']=='theorem'
    replay=[x.removeprefix('replaying ') for x in (logs/'batch-checker.log').read_text().splitlines() if x.startswith('replaying ')]
    assert len(replay)==len(modules) and set(replay)==set(modules)
    (logs/'SUPPORT_RESERVE_RECEIPT.json').write_text(json.dumps({'status':'PASS_EXACT_SUPPORT_RESERVE_MODULE_ONLY','modules':modules,'complete_serialized_declarations':len(ds),'source_commit':ref,'target_modules':targets,'matched_owned_names':{m:len(actual[m]) for m in targets},'target_endpoint':endpoint,'scope':'one strict module, 46 ordinary-warning project dependencies, stock project replay and all owned declarations; no full P1 or policy-support theorem credit','whole_P1_accepted':False,'proof_artifact_hash':sha(logs/'BATCH_OBJECTS_BEFORE.json')},indent=2))
else: raise SystemExit('unexpected mode')
