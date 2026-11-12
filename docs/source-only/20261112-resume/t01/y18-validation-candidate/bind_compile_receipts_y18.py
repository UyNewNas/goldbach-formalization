"""CI-only exact source/command/config/import joins. No proof evaluator or restorer."""
from pathlib import Path
import hashlib,json,os,tomllib

HERE=Path(__file__).resolve().parent
RESOURCE_KEYS={'maxRecDepth','maxHeartbeats'}
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def raw_blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
def exact_file(p,r):
    p=Path(p);assert p.is_file() and not p.is_symlink(),str(p)
    b=p.read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],str(p)
    if r.get('git_blob_sha1'):assert raw_blob(b)==r['git_blob_sha1'],str(p)
    return {'path':str(p.resolve()),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob_sha1':raw_blob(b)}
def option(command,flag):
    args=command['command'][1:];values=[]
    for i,a in enumerate(args):
        if a==flag:
            assert i+1<len(args);values.append(args[i+1])
        elif flag.startswith('--') and a.startswith(flag+'='):values.append(a[len(flag)+1:])
    assert len(values)<=1,(flag,values)
    if not values:return None
    p=Path(values[0]);return (Path(command['cwd'])/p).resolve() if not p.is_absolute() else p.resolve()
def definitions(argv):
    result={};i=0
    while i<len(argv):
        a=argv[i]
        assert a!='--','Unreviewed end-of-options compilation form'
        if a=='-D':
            i+=1;assert i<len(argv);value=argv[i]
        elif a.startswith('-D'):value=a[2:]
        else:i+=1;continue
        assert '=' in value,value
        key,value=value.split('=',1);assert key and key not in result,('Duplicate/overriding Lean option',key)
        result[key]=value;i+=1
    return result
def profiles(m,project):
    cfg=m['compiler_profiles'];root=exact_file(project/'lakefile.toml',cfg['project']['configuration'])
    native=exact_file(project/'.lake/packages/goldbach/lakefile.toml',cfg['goldbach']['configuration'])
    lock=read(project/'lake-manifest.json');pkg=next(p for p in lock['packages'] if p['name']=='goldbach')
    assert pkg['rev']==m['native_rev'] and pkg['configFile']=='lakefile.toml'
    for role,path,lib in [('project',project/'lakefile.toml','ImbalancedChen'),('goldbach',project/'.lake/packages/goldbach/lakefile.toml','MathlibNt')]:
        c=tomllib.loads(path.read_text(encoding='utf-8'));p=cfg[role]
        assert c.get('moreLeanArgs',[])==p['moreLeanArgs'] and c.get('leanOptions',[])==[]
        libraries=[x for x in c['lean_lib'] if x['name']==lib];assert len(libraries)==1
        assert libraries[0].get('moreLeanArgs',[])==[] and libraries[0].get('leanOptions',[])==[]
        if role=='goldbach':
            assert c['lean_lib']==cfg['goldbach']['selected_libraries']
            assert all(x.get('moreLeanArgs',[])==[] and x.get('leanOptions',[])==[] for x in c['lean_lib'])
    return {'project_configuration':root,'goldbach_configuration':native,'goldbach_lock_record':pkg}
def normalizer(m):
    path=HERE/'reused/ci_runtime_guard.py';record=next(r for r in m['support_files'] if r['path']=='reused/ci_runtime_guard.py')
    exact_file(path,record)
    # Load the already hash-checked source directly; do not trust a .pyc cache.
    namespace={'__name__':'frozen_fine_runtime_guard','__file__':str(path)}
    exec(compile(path.read_text(encoding='utf-8'),str(path),'exec'),namespace)
    return namespace['normalize_lean_args']
def command_binding(m,command,source,source_record,root,role,normalize,state):
    assert command['tool']=='lean' and command['sysroot']==state['shadow']
    assert command['command'][0]==state['shadow']+'/bin/lean-runtime'
    actual=command['command'][1:]
    assert actual==normalize(command['input_args']) and actual[:3]==['-t0','-j2','-M12288']
    actual_defs=definitions(actual);expected=m['compiler_profiles'][role]['definition_options']
    assert actual_defs==expected,{'source':str(source),'expected':expected,'observed':actual_defs}
    sources=[]
    for a in command['input_args']:
        if a.endswith('.lean'):
            p=Path(a);sources.append((Path(command['cwd'])/p).resolve() if not p.is_absolute() else p.resolve())
    assert sources==[source.resolve()],('Actual compiler source does not match selected canonical path',sources,str(source))
    source_receipt=exact_file(source,source_record)
    name=source_record.get('module',source.stem);rel=Path(*name.split('.'))
    stem=root/'.lake/build/lib/lean'/rel;ir=root/'.lake/build/ir'/rel
    assert option(command,'-o')==stem.with_suffix('.olean').resolve()
    assert option(command,'-i')==stem.with_suffix('.ilean').resolve()
    if role=='wrapper':
        assert option(command,'--setup') is None
        assert option(command,'-c')==ir.with_suffix('.c').resolve()
    else:
        setup=ir.with_suffix('.setup.json');assert option(command,'--setup')==setup.resolve()
        is_module=read(setup).get('isModule',False)
        assert option(command,'-c')==ir.with_suffix('.c').resolve() or (is_module and option(command,'-c') is None)
    return {'module':name,'source':source_receipt,'actual_command':command,'profile':role,'expected_definition_options':expected,'observed_definition_options':actual_defs,'managed_resources':{'trust':0,'threads':2,'memory_MiB':12288}}

def bind_wrappers(m,project,logs):
    assert os.environ.get('GITHUB_ACTIONS')=='true'
    config=profiles(m,project);normalize=normalizer(m);state=read(logs/'runtime/state.json')
    commands=[json.loads(s) for s in Path(state['log']).read_text(encoding='utf-8').splitlines() if s.strip()]
    rows=[]
    for record in m['audit_sources']:
        name=Path(record['install_path']).stem;source=project/record['install_path']
        expected=project/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')
        candidates=[c for c in commands if c.get('tool')=='lean' and option(c,'-o')==expected.resolve()]
        assert len(candidates)==1,('Missing/duplicate wrapper build command',name,len(candidates))
        bound=command_binding(m,candidates[0],source,{**record,'module':name},project,'wrapper',normalize,state)
        facets=[]
        for directory in [project/'.lake/build/lib/lean',project/'.lake/build/ir']:
            for p in sorted(directory.glob(name+'.*')):
                assert p.is_file() and not p.is_symlink();facets.append({'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':sha(p)})
        paths={r['path'] for r in facets}
        for p in [expected,expected.with_suffix('.ilean'),project/'.lake/build/ir'/Path(name).with_suffix('.c')]:
            assert str(p.resolve()) in paths and p.stat().st_size>0,str(p)
        rows.append({**bound,'facets':facets})
    assert [r['module'] for r in rows]==m['audit_wrapper_modules']
    write(logs/'WRAPPER_OBJECT_BINDINGS.json',{'status':'BOUND_GUARDED_WRAPPER_BUILD_OUTPUTS_NOT_KERNEL_ACCEPTANCE','source_commit':os.environ['SOURCE_COMMIT'],'manifest_sha256':sha(HERE/'Y18_MANIFEST.json'),'configurations':config,'wrappers':rows})

def bind_completed(m,project,logs,checkpoint):
    assert os.environ.get('GITHUB_ACTIONS')=='true'
    cp=read(checkpoint/'CHECKPOINT.json');state=read(logs/'runtime/state.json');normalize=normalizer(m)
    assert cp['runtime_audit_valid'] and cp['all_dependency_source_pins_valid'] and not cp['issues']
    configuration=profiles(m,project)
    source_pre=read(logs/'SOURCE_PRE.json');source_post=read(logs/'SOURCE_POST.json')
    for r,mode in [(source_pre,'pre_compile'),(source_post,'post_compile')]:
        assert r['mode']==mode and r['source_commit']==os.environ['SOURCE_COMMIT']
        assert r['run_id']==os.environ['GITHUB_RUN_ID'] and r['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
        assert r['manifest_sha256']==sha(HERE/'Y18_MANIFEST.json')
    assert source_post['pre_source_receipt_binding']['sha256']==sha(logs/'SOURCE_PRE.json')
    files={r['resolved_path']:r for r in cp['files'].values()};hash_cache={};setup_cache={}
    def captured(path):
        p=Path(path).resolve();key=str(p);assert key in files,key
        r=files[key];assert p.is_file() and p.stat().st_size==r['bytes']
        if key not in hash_cache:hash_cache[key]=sha(p)
        assert hash_cache[key]==r['sha256'];return r
    # Every selected import, including transitive setup entries, must consume
    # the same module's canonical guarded producer facets. No accepted alias or
    # restored project/native cache is available in this candidate.
    selected_output_parts = {}
    for supplier in m['files'] + m['all_native_sources']:
        supplier_root = project if supplier['module'].startswith('ImbalancedChen.') else project/'.lake/packages/goldbach'
        base = supplier_root/'.lake/build/lib/lean'/Path(*supplier['module'].split('.'))
        parts = {}
        for suffix in ['.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig']:
            path = base.with_suffix(suffix).resolve()
            if path.is_file():
                receipt = captured(path)
                assert receipt['bytes'] > 0
                parts[str(path)] = {'part': suffix, 'path': str(path), 'sha256': receipt['sha256'], 'bytes': receipt['bytes']}
        assert str(base.with_suffix('.olean').resolve()) in parts
        selected_output_parts[supplier['module']] = parts
    def setup_imports(entry,record):
        setup_path=Path(entry['setup']['resolved_path']);captured(setup_path)
        if str(setup_path) not in setup_cache:setup_cache[str(setup_path)]=read(setup_path)
        setup=setup_cache[str(setup_path)];assert setup['name']==record['module']
        arts=setup.get('importArts',{});items=arts.items() if isinstance(arts,dict) else arts
        arts=dict(items);expected=[n for n in record['imports'] if n.split('.')[0] not in ['Lean','Init','Std']]
        imported=[]
        for name, arrays in arts.items():
            if name not in selected_output_parts:
                continue
            parts = []
            for array in arrays:
                assert isinstance(array, list)
                for value in array:
                    assert isinstance(value, str)
                    path = Path(value)
                    if not path.is_absolute():
                        path = Path(entry['command']['cwd'])/path
                    path = path.resolve()
                    receipt = captured(path)
                    canonical = selected_output_parts[name]
                    assert str(path) in canonical, ('Selected import consumes another module/path/cache artifact', record['module'], name, str(path), sorted(canonical))
                    producer = canonical[str(path)]
                    assert (receipt['sha256'], receipt['bytes']) == (producer['sha256'], producer['bytes'])
                    parts.append(producer)
            assert any(p['part'] == '.olean' for p in parts), ('Selected setup import missing public canonical olean', record['module'], name)
            imported.append({'module': name, 'selected_canonical_producer_join': parts, 'includes_transitive_setup_entries': True})
        for name in expected:
            assert name in arts,('Missing actual expected direct import',record['module'],name)
            paths=[]
            for array in arts[name]:
                assert isinstance(array,list)
                for value in array:
                    assert isinstance(value,str);p=Path(value)
                    if not p.is_absolute():p=Path(entry['command']['cwd'])/p
                    receipt=captured(p);assert receipt['bytes']>0
                    paths.append({'path':str(p.resolve()),'sha256':receipt['sha256']})
            assert any(p['path'].endswith('.olean') for p in paths),('Empty public olean direct import',name)
            imported.append({'module':name,'actual_parts':paths})
        return imported
    pre=read(logs/'NATIVE_SOURCE_PRE.json');post=read(logs/'NATIVE_SOURCE_POST.json')
    for r in [pre,post]:
        assert r['source_commit']==os.environ['SOURCE_COMMIT'] and r['run_id']==os.environ['GITHUB_RUN_ID'] and r['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
        assert r['native_commit']==m['native_rev'] and r['acceptance_manifest_sha256']==sha(HERE/'Y18_MANIFEST.json')
    assert post['pre_install_receipt_binding']['sha256']==sha(logs/'NATIVE_SOURCE_PRE.json')
    before={r['module']:r for r in pre['files']};after={r['module']:r for r in post['files']}
    native_expected={r['module']:r for r in m['all_native_sources']}
    assert len(pre['files'])==len(post['files'])==len(before)==len(after)==1348 and set(before)==set(after)==set(native_expected)
    package=project/'.lake/packages/goldbach';native_rows=[]
    for name,record in native_expected.items():
        canonical=(package/record['install_path']).resolve()
        for r in [before[name],after[name]]:
            assert r['original_revision']==m['native_rev'] and r['original_research_path']==record['path']
            assert r['installed_relative_path']==record['install_path'] and Path(r['installed_path']).resolve()==canonical
            assert r['canonical_readback_verified'] and r['bytes']==record['bytes'] and r['sha256']==record['sha256'] and r['git_blob_sha1']==record['git_blob_sha1']
        entries=[r for r in cp['all_guarded_package_compilations'] if r.get('package')=='goldbach' and r.get('module')==name and r['classification']=='PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND']
        assert entries,('Missing completed native compile',name)
        joined=[]
        for e in entries:
            assert Path(e['source']['resolved_path']).resolve()==canonical
            assert e['source']['sha256']==record['sha256'] and e['source']['bytes']==record['bytes']
            bound=command_binding(m,e['command'],canonical,record,package,'goldbach',normalize,state)
            joined.append({**bound,'expected_direct_imports':record['imports'],'actual_expected_import_parts':setup_imports(e,record),'setup':e['setup']})
        native_rows.append({'module':name,'original_revision':m['native_rev'],'original_research_path':record['path'],'original_git_blob_sha1':record['git_blob_sha1'],'pre':before[name],'post':after[name],'completed_compiles':joined})
    project_rows=[];owned={r['module']:r for r in cp['modules']}
    assert len(cp['modules'])==len(owned)==337 and set(owned)==set(m['project_modules'])
    for record in m['files']:
        e=owned[record['module']];source=project/record['install_path']
        assert e['completed_guarded_compile_candidate'] and Path(e['source']['resolved_path']).resolve()==source.resolve()
        assert e['source']['sha256']==record['sha256'] and e['source']['bytes']==record['bytes']
        assert e['guarded_source_commands']
        commands=[command_binding(m,c,source,record,project,'project',normalize,state) for c in e['guarded_source_commands']]
        imported=setup_imports({**e,'command':e['guarded_source_commands'][0]},record)
        project_rows.append({'module':record['module'],'guarded_compiles':commands,'actual_expected_import_parts':imported,'setup':e['setup']})
    wrappers=read(logs/'WRAPPER_OBJECT_BINDINGS.json')
    assert wrappers['manifest_sha256']==sha(HERE/'Y18_MANIFEST.json') and wrappers['source_commit']==os.environ['SOURCE_COMMIT']
    assert [r['module'] for r in wrappers['wrappers']]==m['audit_wrapper_modules']
    for row,record in zip(wrappers['wrappers'],m['audit_sources']):
        command_binding(m,row['actual_command'],project/record['install_path'],{**record,'module':row['module']},project,'wrapper',normalize,state)
        for facet in row['facets']:
            p=Path(facet['path']);assert p.is_file() and p.stat().st_size==facet['bytes'] and sha(p)==facet['sha256'];captured(p)
    receipt={'status':'PASS_EXACT_SELECTED_SOURCE_CONFIG_FLAGS_IMPORT_OUTPUT_JOINS_ONLY','manifest_sha256':sha(HERE/'Y18_MANIFEST.json'),'source_commit':os.environ['SOURCE_COMMIT'],'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'configurations':configuration,'project_modules':project_rows,'native_modules':native_rows,'wrapper_binding_sha256':sha(logs/'WRAPPER_OBJECT_BINDINGS.json'),'receipts_and_raw_outputs':{n:{'sha256':sha(logs/n),'bytes':(logs/n).stat().st_size} for n in ['SOURCE_PRE.json','SOURCE_POST.json','NATIVE_SOURCE_PRE.json','NATIVE_SOURCE_POST.json','batch-types.log','TARGET17_RESULT.json','batch-checker.log','WRAPPER_OBJECT_BINDINGS.json']},'restore_accepted':False}
    write(logs/'COMPILE_INPUT_BINDINGS.json',receipt)
    return receipt
