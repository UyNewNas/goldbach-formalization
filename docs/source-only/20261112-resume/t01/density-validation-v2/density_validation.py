"""Dedicated CI-only FineDensity binding/final acceptance. Never run locally."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys

HERE=Path(__file__).resolve().parent
def digest(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
def checked(p,r):
    b=Path(p).read_bytes()
    assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],str(p)
    if r.get('git_blob_sha1'):assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob_sha1']
    return b
def run(*args):subprocess.run(list(map(str,args)),check=True)
def git(*args):return subprocess.check_output(['git','-C',os.environ['GITHUB_WORKSPACE'],*args])

def bound():
    assert os.environ.get('GITHUB_ACTIONS')=='true','Remote CI only'
    workspace=Path(os.environ['GITHUB_WORKSPACE']);commit=os.environ['GITHUB_SHA']
    assert re.fullmatch('[0-9a-f]{40}',commit) and git('rev-parse','HEAD').decode().strip()==commit
    selection_path='verification/parts/p0/FINE_DENSITY_DRIVER_SELECTION.json'
    raw=git('show',commit+':'+selection_path)
    assert (workspace/selection_path).read_bytes()==raw
    s=json.loads(raw)
    assert s['schema']=='fine-density-root-driver-selection-v2'
    for k in ['bundle_registry_sha256','manifest_sha256']:assert re.fullmatch('[0-9a-f]{64}',s[k])
    assert s['source_base']=='5d1786aa1096b3b3c5112ef8cb5e56fca72b59db'
    assert re.fullmatch('[0-9a-f]{40}',s['driver_base'])
    assert s['driver_branch']=='ci/fine-density-20261112'
    assert os.environ['GITHUB_EVENT_NAME']=='push' and os.environ['GITHUB_REF']=='refs/heads/'+s['driver_branch']
    headers=git('cat-file','commit',commit).split(b'\n\n',1)[0].decode().splitlines()
    assert [h[7:] for h in headers if h.startswith('parent ')]==[s['driver_base']]
    assert s['bundle_path']=='docs/source-only/20261112-resume/t01/density-validation-v2'
    assert HERE.resolve()==(workspace/s['bundle_path']).resolve()
    assert s['workflow_path']=='.github/workflows/fine-density-validation.yml'
    assert digest(HERE/'REGISTRY.json')==s['bundle_registry_sha256']
    registry=read(HERE/'REGISTRY.json')
    for r in registry['files']:
        p=(HERE/r['path']).resolve();assert p.is_relative_to(HERE.resolve());checked(p,r)
    assert digest(HERE/'DENSITY_MANIFEST.json')==s['manifest_sha256']
    m=read(HERE/'DENSITY_MANIFEST.json')
    assert m['source_base']==s['source_base'] and m['project_modules']==[r['module'] for r in m['files']]
    assert len(m['files'])==len(set(m['project_modules']))==1808
    assert m['targets'][0]['primary_module']=='ImbalancedChen.P4AOriginalFiniteAll22FineDensity'
    assert m['mathematical_modules']==m['project_modules']+sorted(r['module'] for r in m['native_sources'])
    assert len(m['mathematical_modules'])==len(set(m['mathematical_modules']))==1851
    assert m['audit_wrapper_modules']==['CandidateAudit','DensityAudit','T01Audit']
    assert m['fresh_kernel_modules']==m['mathematical_modules']+m['audit_wrapper_modules']
    assert len(m['fresh_kernel_modules'])==len(set(m['fresh_kernel_modules']))==1854
    assert m['unresolved']==[] and m['accepted_objects']==[]
    assert len(m['full_final_paths'])==22 and len(set(m['full_final_paths']))==22
    assert len({r['install_path'] for r in m['data_inputs']})==357
    actual={p.relative_to(workspace).as_posix() for pat in ['*.yml','*.yaml'] for p in (workspace/'.github/workflows').glob(pat)}
    expected={r['path']:r for r in s['reviewed_driver_workflows']}
    assert len(expected)==len(s['reviewed_driver_workflows']) and actual==set(expected)
    own=next(r for r in registry['files'] if r['path']=='fine-density-validation.yml')
    assert expected[s['workflow_path']]['sha256']==own['sha256']
    for p,r in expected.items():assert checked(workspace/p,r)==git('show',commit+':'+p)
    assert s['other_auto_push_exclusion_review']=='PASS_EXACT_REVIEWED_DRIVER_WORKFLOW_BYTES'
    return m,dict(driver_commit=commit,driver_base=s['driver_base'],root_selection_sha256=hashlib.sha256(raw).hexdigest(),manifest_sha256=s['manifest_sha256'],registry_sha256=s['bundle_registry_sha256'])

def native(m,mode,logs,project):
    args=[sys.executable,HERE/'stage_native_density.py','--package',project/'.lake/packages/goldbach','--plan-sha256',m['native_research_overlay']['sha256'],'--mode',mode,'--acceptance-manifest',HERE/'DENSITY_MANIFEST.json','--acceptance-manifest-sha256',digest(HERE/'DENSITY_MANIFEST.json'),'--receipt',logs/('NATIVE_SOURCE_PRE.json' if mode=='install' else 'NATIVE_SOURCE_POST.json')]
    if mode=='verify_existing':args+=['--pre-install-receipt',logs/'NATIVE_SOURCE_PRE.json','--pre-install-receipt-sha256',digest(logs/'NATIVE_SOURCE_PRE.json')]
    run(*args)

def source_gate(mode,logs,project):
    args=[sys.executable,HERE/'verify_density_sources.py','--project',project,'--manifest',HERE/'DENSITY_MANIFEST.json','--manifest-sha256',digest(HERE/'DENSITY_MANIFEST.json'),'--mode',mode,'--receipt',logs/('SOURCE_PRE.json' if mode=='pre_compile' else 'SOURCE_POST.json')]
    if mode=='post_compile':args+=['--pre-source-receipt',logs/'SOURCE_PRE.json','--pre-source-receipt-sha256',digest(logs/'SOURCE_PRE.json')]
    run(*args)

def named(m,logs):
    req=read(HERE/'PRINT_TARGETS.json');lines=(logs/'density-types.log').read_text(encoding='utf-8').splitlines()
    records=[]
    for marker in ['DENSITY_DECL ','DENSITY_DEF ']:records += [json.loads(x[len(marker):]) for x in lines if x.startswith(marker)]
    expected={r['name']:r for r in req['required_declared_module_and_source_binding']}
    assert len(records)==len(expected) and {r['name'] for r in records}==set(expected)
    sources={r['module']:r['sha256'] for r in m['files']}
    for r in records:
        e=expected[r['name']];assert r['module']==e['defining_module'] and sources[r['module']]==e['source_sha256']
        assert r['kind']==('theorem' if r['name'] in req['required_unelided_theorem_types'] else 'definition')
        assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert all(r[k].strip() and '⋯' not in r[k] and '…' not in r[k] for k in ['type','readable_type'])
    assert lines.count('DENSITY_COUNT '+str(len(req['required_unelided_theorem_types'])))==1
    assert lines.count('DENSITY_DEF_COUNT '+str(len(req['required_unelided_definitions'])))==1
    for name in req['required_unelided_definitions']:
        begin='DENSITY_BODY_BEGIN '+name;end='DENSITY_BODY_END '+name
        assert lines.count(begin)==lines.count(end)==1
        a,b=lines.index(begin),lines.index(end);assert a<b
        text='\n'.join(lines[a+1:b]);assert name in text and '⋯' not in text and '…' not in text
    run(sys.executable,HERE/'audit_floor.py','--project',Path(os.environ['PROJECT']),'--log',logs/'floor-types.log','--manifest',HERE/'DENSITY_MANIFEST.json','--output',logs/'FLOOR_TYPE_AXIOM_RESULT.json')
    floor=read(logs/'FLOOR_TYPE_AXIOM_RESULT.json')
    assert floor['status']=='PASS_EXACT_NINE_FULL_TYPES_AND_TRANSITIVE_AXIOMS'
    write(logs/'NAMED_ACCEPTANCE.json',dict(status='PASS_EXACT_FINE_AND_ORIGINAL_FLOOR_TYPES_ONLY',names=sorted(expected),floor_names=sorted(r['name'] for r in floor['targets']),floor_result_sha256=digest(logs/'FLOOR_TYPE_AXIOM_RESULT.json'),raw_density_log_sha256=digest(logs/'density-types.log'),raw_floor_log_sha256=digest(logs/'floor-types.log')))

def main():
    m,binding=bound();logs=Path(os.environ['LOGS']);logs.mkdir(parents=True,exist_ok=True);mode=sys.argv[1]
    if mode=='select':write(logs/'DRIVER_BINDING.json',binding);return
    assert read(logs/'DRIVER_BINDING.json')==binding
    project=Path(os.environ['PROJECT'])
    if mode=='fetch':
        commits={m['source_base'],m['inherited_T01']['publication_commit']}
        for r in m['files']+m['data_inputs']:
            for origin in [r['origin'],r.get('pre_input',{}).get('origin',{})]:
                if origin.get('kind')=='git':commits.add(origin['commit'])
        for c in sorted(commits):
            assert re.fullmatch('[0-9a-f]{40}',c)
            run('git','-C',os.environ['GITHUB_WORKSPACE'],'fetch','--no-tags','--depth=1','origin',c)
        write(logs/'SOURCE_REFS.json',sorted(commits))
    elif mode=='stage':
        run(sys.executable,HERE/'stage_density.py','--repo',os.environ['GITHUB_WORKSPACE'],'--dest',project,'--release-asset',os.environ['RELEASE_ASSET'],'--manifest-sha256',binding['manifest_sha256'],'--purpose','source_validation')
    elif mode=='build_wrapper':
        name=sys.argv[2];assert name in m['audit_wrapper_modules']
        record=next(r for r in m['audit_sources'] if Path(r['install_path']).stem==name)
        checked(project/record['install_path'],record)
        stem=project/'.lake/build/lib/lean'/name;ir=project/'.lake/build/ir'/name
        stem.parent.mkdir(parents=True,exist_ok=True);ir.parent.mkdir(parents=True,exist_ok=True)
        command=['lake','env','lean',*m['wrapper_build_lean_args'],'-o',str(stem.with_suffix('.olean')),'-i',str(stem.with_suffix('.ilean')),'-c',str(ir.with_suffix('.c')),record['install_path']]
        log={'CandidateAudit':'batch-types.log','DensityAudit':'density-types.log','T01Audit':'floor-types.log'}[name]
        with (logs/log).open('wb') as output:
            process=subprocess.Popen(command,cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            for block in iter(lambda:process.stdout.read(65536),b''):
                output.write(block);output.flush();sys.stdout.buffer.write(block);sys.stdout.buffer.flush()
            result=process.wait()
        if result:raise subprocess.CalledProcessError(result,command)
    elif mode=='bind_wrappers':
        from bind_compile_receipts import bind_wrappers
        bind_wrappers(m,project,logs)
    elif mode=='native_pre':native(m,'install',logs,project);source_gate('pre_compile',logs,project)
    elif mode=='post':source_gate('post_compile',logs,project);native(m,'verify_existing',logs,project)
    elif mode=='named':named(m,logs)
    elif mode=='finalize':
        batch=read(logs/'BATCH_ACCEPTANCE.json')
        assert batch['status']=='PASS_EXACT_CANDIDATE_CLOSURE_ONLY'
        assert batch['modules']==m['fresh_kernel_modules'] and batch['source_commit']==os.environ['SOURCE_COMMIT']
        assert batch['mathematical_modules']==m['mathematical_modules']
        assert batch['proof_artifact_hash']==digest(logs/'BATCH_OBJECTS_BEFORE.json')
        assert read(logs/'NAMED_ACCEPTANCE.json')['status']=='PASS_EXACT_FINE_AND_ORIGINAL_FLOOR_TYPES_ONLY'
        rt=read(logs/'runtime/audit.json');state=read(logs/'runtime/state.json')
        assert rt['status']=='PASS_RUNTIME_GUARD_ONLY' and rt['probe'] and rt['source_commands']>0
        assert digest(logs/'runtime/state.json')==rt['state_sha256'] and digest(state['log'])==rt['command_log_sha256']
        cp=read(Path(os.environ['CHECKPOINT'])/'CHECKPOINT.json')
        assert cp['source_commit']==os.environ['SOURCE_COMMIT'] and cp['manifest_sha256']==binding['manifest_sha256']
        assert cp['run_id']==os.environ['GITHUB_RUN_ID'] and cp['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
        assert cp['runtime_audit_valid'] and cp['all_dependency_source_pins_valid'] and not cp['issues']
        assert len(cp['modules'])==1808 and {r['module'] for r in cp['modules']}==set(m['project_modules'])
        assert all(r['completed_guarded_compile_candidate'] for r in cp['modules'])
        from bind_compile_receipts import bind_completed
        joined=bind_completed(m,project,logs,Path(os.environ['CHECKPOINT']))
        named_result=read(logs/'NAMED_ACCEPTANCE.json')
        assert named_result['floor_result_sha256']==digest(logs/'FLOOR_TYPE_AXIOM_RESULT.json')
        assert named_result['raw_density_log_sha256']==digest(logs/'density-types.log') and named_result['raw_floor_log_sha256']==digest(logs/'floor-types.log')
        write(logs/'FINAL_ACCEPTANCE.json',dict(status='PASS_EXACT_FINE_DENSITY_CLOSURE_ONLY',**binding,project_modules=1808,native_modules=43,mathematical_serialized_modules=1851,audit_wrapper_modules=3,kernel_modules=1854,checkpoint_sha256=digest(Path(os.environ['CHECKPOINT'])/'CHECKPOINT.json'),compile_input_bindings_sha256=digest(logs/'COMPILE_INPUT_BINDINGS.json'),receipts_and_raw_outputs=joined['receipts_and_raw_outputs'],whole_PP_accepted=False,whole_hUpper_accepted=False,restoration_accepted=False))
    else:raise SystemExit('Unknown mode')

if __name__=='__main__':main()
