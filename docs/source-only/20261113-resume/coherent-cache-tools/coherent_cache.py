"""GitHub-only authentic checkpoint input restoration and stock Lake qualification.

All cache payloads remain unmodified. A completed compile cache is not proof
acceptance. This module is also the shared single-parent API for the separately
bound Stored caller; the two scopes cannot be installed together.
"""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import threading
import urllib.error
import urllib.request
import zlib

HERE = Path(__file__).resolve().parent
NATIVE = 'P2_NATIVE_398'
PARENT = 'STORED_PARENT'
SELECTORS = {
    NATIVE: ('P2_NATIVE_398_CHECKPOINT_SELECTION.json', '4ad7329984a1df0ee9dfd4b142adb4d42c0cc0952275f110b4934d609563eab9'),
    PARENT: ('STORED_PARENT_T01_COHERENT_SELECTION.json', 'c25b5c29bc303bed700af61237f1088e104cf3a23067df7217f96f0cc24bcc03')}
CHECKPOINT_SHA = 'aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a'
BASELINE_GUARD = '837f00360ca1364eb6adede88c05a72122acbbbbff2437c83026f2851836a877'


def require(ok, text):
    if not ok: raise ValueError(text)


def sha(path):
    with Path(path).open('rb') as f: return hashlib.file_digest(f, 'sha256').hexdigest()


def read(path): return json.loads(Path(path).read_text(encoding='utf-8'))


def write(path, value):
    path = Path(path); require(not path.exists(), 'Refusing receipt overwrite: ' + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((json.dumps(value, indent=2) + '\n').encode())


def checked(path, row):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/nonregular payload: ' + str(path))
    require(path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], 'Changed payload: ' + str(path))


def git(*args):
    return subprocess.check_output(['git', '-c', 'protocol.allow=never', *map(str, args)],
                                   env=dict(os.environ, GIT_NO_LAZY_FETCH='1'))


def bind_inputs(scope):
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux', 'GitHub Linux only; never execute locally')
    require(scope in SELECTORS and os.environ['CACHE_SCOPE'] == scope, 'Explicit one-scope binding required')
    selector, expected = SELECTORS[scope]
    require(sha(HERE / 'inputs' / selector) == expected, 'Wrong reviewed checkpoint selector')
    if scope == NATIVE:
        workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
        caller = (workspace / os.environ['P2_BUNDLE']).resolve()
        require(caller.is_relative_to(workspace), 'P2 caller escapes committed workspace')
        sys.path.insert(0, str(caller))
        from p2_validation import load_bound_bundle
        manifest, binding = load_bound_bundle()
        logs = Path(os.environ['LOGS'])
        require(read(logs / 'DRIVER_BINDING.json') == binding, 'Wrong actual P2 driver binding')
        require(manifest['compile_cache']['scope'] == NATIVE and manifest['compile_cache']['selection_sha256'] == expected,
                'Native398 cache not adopted by exact P2 manifest')
        from cache_bootstrap import ADOPTION, load_inputs
        require(manifest['compile_cache']['bootstrap_cache'] == ADOPTION,'Authentic Cache bootstrap was not explicitly adopted')
        load_inputs()
        tools = manifest['compile_cache']['tools_bundle']
        require(HERE == (workspace / tools['path']).resolve() and sha(HERE/'REGISTRY.json') == tools['registry_sha256'],
                'Wrong explicitly adopted shared cache tools')
        for row in read(HERE/'REGISTRY.json')['files']:
            target=(HERE/row['path']).resolve();require(target.is_relative_to(HERE),'Shared tools registry path escape');checked(target,row)
        return {'scope': scope, 'driver_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
                'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'], 'job': os.environ['GITHUB_JOB'],
                'source_commit': manifest['source_commit'], 'manifest_sha256': binding['manifest_sha256'],
                'bundle_registry_sha256': binding['bundle_registry_sha256'], 'selection_sha256': expected}
    # Parent caller must make an independent explicit committed adoption. It
    # cannot inherit the P2 route or expand native398 into this project graph.
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve(); commit = os.environ['GITHUB_SHA']
    control_path = Path(os.environ['CACHE_ROOT_CONTROL']).resolve()
    require(control_path.is_relative_to(workspace), 'Parent control outside immutable checkout')
    require(git('-C', workspace, 'show', commit + ':' + control_path.relative_to(workspace).as_posix())
            == control_path.read_bytes(), 'Parent control differs from committed bytes')
    c = read(control_path)
    require(c['schema'] == 'stored-parent-coherent-cache-root-selection-v1' and c['cache_scope'] == PARENT,
            'Wrong parent-only root adoption')
    require(os.environ['GITHUB_EVENT_NAME'] == 'push' and os.environ['GITHUB_REF'] == 'refs/heads/' + c['driver_branch'], 'Wrong parent branch/event')
    headers = git('-C', workspace, 'cat-file', 'commit', commit).split(b'\n\n', 1)[0].splitlines()
    require([x[7:].decode() for x in headers if x.startswith(b'parent ')] == [c['driver_base']], 'Wrong driver parent')
    require(HERE == (workspace / c['bundle_path']).resolve() and sha(HERE / 'REGISTRY.json') == c['bundle_registry_sha256'], 'Wrong parent tool bundle')
    for row in read(HERE / 'REGISTRY.json')['files']:
        target = (HERE / row['path']).resolve(); require(target.is_relative_to(HERE), 'Registry path escape'); checked(target, row)
    workflows = {r['path']: r for r in c['reviewed_driver_workflows']}
    actual = {p.relative_to(workspace).as_posix() for pat in ('*.yml','*.yaml') for p in (workspace/'.github/workflows').glob(pat)}
    require(len(workflows) == len(c['reviewed_driver_workflows']) and set(workflows) == actual and c['workflow_path'] in actual
            and c['other_auto_push_exclusion_review'] == 'PASS_EXACT_REVIEWED_DRIVER_WORKFLOW_BYTES', 'Wrong full workflow set')
    for relative, row in workflows.items():
        checked(workspace/relative, row); require(git('-C',workspace,'show',commit+':'+relative) == (workspace/relative).read_bytes(), 'Workflow changed')
    source = (workspace / c['source_selection']['path']).resolve()
    require(source.is_relative_to(workspace), 'Selection escape'); checked(source,c['source_selection'])
    require(git('-C',workspace,'show',commit+':'+source.relative_to(workspace).as_posix()) == source.read_bytes(), 'Stored source selection not committed')
    stored_admission(c,read(source))
    from cache_bootstrap import ADOPTION, load_inputs
    require(c['bootstrap_cache']==ADOPTION,'Stored authentic bootstrap not explicitly adopted');load_inputs()
    return {'scope':scope, 'driver_commit':commit, 'run_id':os.environ['GITHUB_RUN_ID'],
            'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'], 'job':os.environ['GITHUB_JOB'],
            'source_commit':commit,'manifest_sha256':sha(source),'root_control_sha256':sha(control_path),
            'bundle_registry_sha256':c['bundle_registry_sha256'],'selection_sha256':expected}



def stored_admission(control, selection):
    admission=control['source_admission'];new=admission['new_modules'];protected=admission['protected_modules']
    parent='ImbalancedChen.P5SubdivisionStoredParentTypes'
    pattern=r'ImbalancedChen\.Data\.P5SubdivisionStoredBlock[0-9]{3}'
    require(selection['schema']=='STORED053_063_EXACT_SOURCE_SCOPE_PROPOSAL_V1'
            and len(new)==11 and len(protected)==54 and len(set(new+protected))==65
            and all(re.fullmatch(pattern,n) for n in new+protected[1:]) and protected[0]==parent
            and new==[f'ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}' for i in range(53,64)]
            and protected==[parent]+[f'ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}' for i in range(53)]
            and admission['audit_filename']=='StoredBatchAudit.lean'
            and selection['parent']['module']==parent
            and all(selection[key]==new for key in ['new_modules','new_proof_compile_scope','kernel_replay_scope','owned_types_axioms_scope'])
            and all(selection[key]==protected for key in ['forbidden_old_source_compile_modules','forbidden_old_kernel_replay_modules'])
            and [r['module'] for r in selection['files']]==new,
            'Stored explicit new-only/protected source scope differs')
    return admission


def scope_policy(scope, project, logs, binding):
    roots, exact = [], []
    if scope == NATIVE: roots = [str(project / ('.lake/packages/'+name)) for name in ['goldbach','LeanArchitect']]
    else:
        control=read(os.environ['CACHE_ROOT_CONTROL'])
        selection=read(Path(os.environ['GITHUB_WORKSPACE'])/control['source_selection']['path'])
        modules=stored_admission(control,selection)['protected_modules']
        exact = [str(project / (n.replace('.', '/') + '.lean')) for n in modules]
        for name in modules:
            for directory, suffixes in [('.lake/build/lib/lean',['.olean','.ilean','.ir','.ir.sig']),('.lake/build/ir',['.c','.bc'])]:
                exact += [str(project / directory / (name.replace('.', '/') + suffix)) for suffix in suffixes]
    denial = logs / 'CACHE_COMPILER_DENIALS.jsonl'; events = logs / 'CACHE_PREEXEC_EVENTS.jsonl'
    require(not denial.exists() and not events.exists(), 'Admission journals already exist'); denial.touch(); events.touch()
    shadow = Path(os.environ['RUNNER_TEMP']).resolve() / 'p0-ci-shadow-toolchain'
    realroot = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.0-rc1'
    substitutions = {'{project}':str(project), '{shadow}':str(shadow), '{realroot}':str(realroot)}
    def substitute(value):
        if isinstance(value, str):
            for before, after in substitutions.items(): value = value.replace(before, after)
        elif isinstance(value, list): value = [substitute(x) for x in value]
        elif isinstance(value, dict): value = {k:substitute(v) for k,v in value.items()}
        return value
    protocol = read(HERE / 'COMPILER_PROTOCOL.json')
    if scope in {NATIVE,PARENT}:
        from cache_bootstrap import load_inputs
        bootstrap,_,_ = load_inputs()
        roots += [str(project/'.lake/packages/mathlib'/relative) for relative in ['Cache','.lake/build/lib/lean/Cache','.lake/build/ir/Cache']]
        for row in bootstrap['rows']:
            if row['package']=='batteries':
                exact += [str(project/'.lake/packages/batteries'/part['path']) for part in [row['source'],*row['facets']]]
    commands = [substitute(r) for r in protocol['commands'] if r['package'] != 'LeanArchitect']
    if scope == NATIVE:
        caller = Path(os.environ['GITHUB_WORKSPACE']) / os.environ['P2_BUNDLE']
        sys.path.insert(0,str(caller))
        from p2_validation import load_bound_bundle
        manifest, _ = load_bound_bundle()
        from cache_project import ADOPTION, load_inputs
        require(manifest['compile_cache']['root_project_cache']==ADOPTION,'Root86 cache adoption differs')
        selected,_=load_inputs();protected={r['module'] for r in selected['rows']}
        for row in selected['rows']:
            exact += [str(project/part['path']) for part in [row['source'],*row['facets']]]
        sources = [dict(path=str(project/r['install_path']), bytes=r['bytes'], sha256=r['sha256'])
                   for r in manifest['modules'] if r['module'] not in protected]
        flags = []; audits = ['CandidateAudit.lean', 'FinitePiPilot.lean']
    else:
        # The independent caller binds these exact eleven source postimages in
        # its original selection and retains the original 26a6 project profile.
        control = read(os.environ['CACHE_ROOT_CONTROL'])
        selection = read(Path(os.environ['GITHUB_WORKSPACE'])/control['source_selection']['path'])
        expected=stored_admission(control,selection)['new_modules']
        sources = [dict(path=str(project/r['install_path']),bytes=r['bytes'],sha256=r['sha256']) for r in selection['files']]
        flags = ['-D','maxRecDepth=100000','-D','maxHeartbeats=4000000']; audits = ['StoredBatchAudit.lean']
    for source in sources:
        relative = Path(source['path']).relative_to(project).with_suffix('')
        argv = ['-t0','-j2','-M12288',*flags,source['path'], '-o',str(project/'.lake/build/lib/lean'/relative)+'.olean',
                '-i',str(project/'.lake/build/lib/lean'/relative)+'.ilean', '-c',str(project/'.lake/build/ir'/relative)+'.c',
                '--setup',str(project/'.lake/build/ir'/relative)+'.setup.json','--json']
        commands.append({'tool':'lean','argv':argv,'phase':'qualified-project','classification':'EXACT_CURRENT_CALLER_SOURCE','source':source})
    for name in audits:
        source = {'path':str(project/name)}
        commands.append({'tool':'lean','argv':['-t0','-j2','-M12288','-D','warningAsError=true',source['path']],
                         'phase':'qualified-project','classification':'EXACT_ORIGINAL_CALLER_AUDIT','source':source})
    native_objects = [r['argv'][r['argv'].index('-o')+1] for r in commands if r['tool']=='clang']
    return {'scope':scope,'context':binding,'project':str(project),'deny_roots':roots,'deny_exact_paths':exact,
            'denial_log':str(denial),'event_log':str(events),'metadata_cwds':[str(project),str(shadow.parent)],
            'admitted_commands':commands,'qualification':str(logs/'CACHE_QUALIFICATION.json'),
            'caller_inputs':str(logs/'CACHE_CALLER_INPUTS.json'),
            'cache_link_output':str(project/'.lake/packages/mathlib/.lake/build/bin/cache'),
            'cache_link_response':str(project/'.lake/packages/mathlib/.lake/build/bin/cache.rsp'),
            'historical_cache_rsp':protocol['historical_cache_rsp'],
            'bootstrap_native_objects':native_objects,'toolchain_library_roots':[str(realroot/'lib'),str(shadow/'lib')],
            'toolchain_roots':{'realroot':str(realroot),'shadow':str(shadow)},
            'bootstrap_cache_reuse_only':True,
            'unknown_tools_modes_flags_and_response_files':'DENY_BEFORE_COMPILER_EXEC',
            'no_cold_rebuild_fallback':True,'cache_hit_is_not_proof_acceptance':True}


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl): return None


class ArchiveReader:
    def __init__(self, anchor):
        self.anchor=anchor; self.token=os.environ['GH_TOKEN']
        self.api='https://api.github.com/repos/'+os.environ['GITHUB_REPOSITORY']+'/actions/artifacts/'+str(anchor['artifact'])
        with self.request(self.api) as response:metadata=json.load(response)
        require(metadata['id']==anchor['artifact'] and not metadata['expired'] and metadata['size_in_bytes']==anchor['artifactBytes']
                and metadata['digest']=='sha256:'+anchor['githubWholeArtifactDigest']
                and metadata['workflow_run']['id']==anchor['run'], 'Historical GitHub artifact identity changed')
        self.metadata=metadata;self.redirect_lock=threading.Lock();self.refresh_redirect()

    def refresh_redirect(self):
        request=urllib.request.Request(self.api+'/zip',headers=self.headers())
        try: urllib.request.build_opener(NoRedirect()).open(request,timeout=60)
        except urllib.error.HTTPError as error:
            require(error.code==302 and error.headers.get('Location','').startswith('https://'),'No authenticated artifact redirect')
            self.url=error.headers['Location']
        else: raise ValueError('Expected a redirect; never stream a whole archive accidentally')

    def headers(self): return {'Authorization':'Bearer '+self.token,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'}
    def request(self,url): return urllib.request.urlopen(urllib.request.Request(url,headers=self.headers()),timeout=60)

    def part(self,start,size):
        end=start+size-1
        previous=self.url
        request=urllib.request.Request(previous,headers={'Range':f'bytes={start}-{end}'})
        try:response=urllib.request.urlopen(request,timeout=120)
        except urllib.error.HTTPError as error:
            require(error.code in {401,403},'Artifact range request failed; no unbounded fallback')
            # GitHub redirects expire after roughly ten minutes. Renew only the
            # same immutable artifact URL, then retry this exact failed range.
            # Concurrent readers reuse the first worker's renewed redirect.
            with self.redirect_lock:
                if self.url==previous:self.refresh_redirect()
            response=urllib.request.urlopen(urllib.request.Request(self.url,headers={'Range':f'bytes={start}-{end}'}),timeout=120)
        with response:
            require(response.status==206 and response.headers.get('Content-Range')==f'bytes {start}-{end}/{self.anchor["artifactBytes"]}',
                    'Exact bounded HTTP range required; no whole-archive fallback')
            data=response.read(size+1);require(len(data)==size,'Wrong range length');return data

    def fetch(self,name,row,destination):
        e=row['zip']; head=self.part(e['h'],30)
        signature,version,flags,method,mtime,mdate,crc,compressed,plain,nlen,xlen=struct.unpack('<IHHHHHIIIHH',head)
        require(signature==0x04034b50 and method==e['c']==0 and not flags&1,'Unsupported/encrypted ZIP member')
        actual=self.part(e['h']+30,nlen+xlen)
        require(actual[:nlen].decode()==name and e['s']==e['z']==row['bytes'],'Wrong ZIP member name/size')
        if not flags&8: require((crc,compressed,plain)==(e['crc'],e['z'],e['s']),'Local/central member disagreement')
        target=destination/name;require(target.resolve().is_relative_to(destination.resolve()),'Unsafe member path')
        target.parent.mkdir(parents=True,exist_ok=True);require(not target.exists(),'Existing cache payload')
        pos=e['h']+30+nlen+xlen;remaining=row['bytes'];check=hashlib.sha256();crc_actual=0
        with target.open('xb') as output:
            while remaining:
                data=self.part(pos,min(8*1024*1024,remaining));output.write(data);check.update(data);crc_actual=zlib.crc32(data,crc_actual)
                remaining-=len(data);pos+=len(data)
        require(check.hexdigest()==row['sha256'] and crc_actual==e['crc'],'Payload SHA/CRC changed')
        return {'member':name,'bytes':row['bytes'],'sha256':row['sha256']}


class CacheSession:
    def __init__(self,scope):
        self.scope=scope;self.binding=bind_inputs(scope)
        self.project=Path(os.environ['PROJECT']).resolve();self.logs=Path(os.environ['LOGS']).resolve()
        self.inputs=Path(os.environ['CACHE_INPUTS']).resolve()
        require(not self.inputs.is_relative_to(self.project) and not self.inputs.is_relative_to(self.logs),'Disjoint cache input root required')
        self.selection=read(HERE/'inputs'/SELECTORS[scope][0]);self.index=read(HERE/'inputs'/(scope+'_PAYLOAD_INDEX.json'))
        self.prerequisites=None
        if scope==NATIVE:
            self.prerequisites=read(HERE/'inputs/P2_LEANARCHITECT_9_PREREQUISITE_SELECTION.json')
            require(self.prerequisites['original398SelectionSHA256']==SELECTORS[NATIVE][1], 'Prerequisite scope differs from original398')
            extra=read(HERE/'inputs/P2_LEANARCHITECT_9_PAYLOAD_INDEX.json')
            for name,row in extra['objects'].items():
                require(name not in self.index['objects'] or self.index['objects'][name]==row,'Conflicting content-addressed payload')
                self.index['objects'][name]=row
        from cache_bootstrap import load_inputs
        self.bootstrap_selection,bootstrap_index,_=load_inputs()
        require(bootstrap_index['whole_artifact']==self.index['whole_artifact'],'Bootstrap is not from the same authentic archive')
        for name,row in bootstrap_index['objects'].items():
            require(name not in self.index['objects'] or self.index['objects'][name]==row,'Conflicting authentic bootstrap payload')
            self.index['objects'][name]=row
        self.anchor=self.index['whole_artifact'];require(self.anchor['artifact']==13749339878,'Wrong input archive')
        self._part_cache={};self._historical_cache={};self._raw=None
        self.state=read(self.logs/'runtime/state.json');require(self.state['guard_sha256']==BASELINE_GUARD,'Baseline guard changed')
        require(Path(self.state['root']).resolve()==self.project,'Runtime project mismatch')
        self.policy_audit()

    def receipt(self,name):
        value=read(self.logs/name);require(value['binding']==self.binding,'Receipt belongs to another scope/run');return value

    def emit(self,name,value):write(self.logs/name,{'binding':self.binding,**value})

    def policy_audit(self):
        extension=read(self.logs/'CACHE_RUNTIME_EXTENSION.json')
        require(extension['binding']==self.binding and extension['baseline_guard_sha256']==BASELINE_GUARD,'Wrong policy extension binding')
        require(extension['extension_sha256']==sha(HERE/'cache_runtime_setup.py') and extension['policy_source_sha256']==sha(HERE/'cache_preexec_policy.py')
                and extension['policy_file_sha256']==sha(self.logs/'CACHE_PREEXEC_POLICY.json'),'Changed execution-denial implementation')
        require(sha(self.logs/'runtime/state.json')==extension['actual_runtime_state_sha256'],'Original actual state changed')
        for tool,expected in extension['generated_wrapper_sha256'].items():require(sha(Path(self.state['shadow'])/'bin'/tool)==expected,'Generated wrapper changed')
        denial=self.logs/'CACHE_COMPILER_DENIALS.jsonl';require(denial.is_file() and not denial.read_bytes(),'A protected compiler exec was attempted')
        commands=[json.loads(x) for x in Path(self.state['log']).read_text().splitlines() if x.strip()]
        policy=read(self.logs/'CACHE_PREEXEC_POLICY.json')
        from cache_preexec_policy import classify
        events = [json.loads(x) for x in (self.logs/'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines() if x.strip()]
        require(len(commands)==len(events),'Pre-exec classification/actual compiler-log census differs')
        for row,event in zip(commands,events):
            require(event['context']==self.binding and event['compiler_exec_permitted'] is True
                    and (row['pid'],row['tool'],row['command'][1:],row['cwd'])==(event['pid'],event['tool'],event['argv'],event['cwd']),
                    'Compiler command lacks its own pre-exec admission event')
            require(row['input_args']==event['raw_argv'],'Raw compiler argv differs from pre-exec classification')
            classified = classify(row['tool'],row['command'][1:],row['cwd'],policy,check_phase=False,raw_argv=row['input_args'])
            require(classified['classification']==event['classification'] and classified['physical_inputs']==event['physical_inputs'],
                    'Compiler classification or actual command input changed')
        return commands

    def fixtures(self):
        output=self.logs/'cache-fixtures.stdout.log';errors=self.logs/'cache-fixtures.stderr.log'
        require(not output.exists() and not errors.exists(),'Fixture process already recorded')
        argv=[sys.executable,str(HERE/'cache_negative_fixtures.py')]
        with output.open('wb') as out,errors.open('wb') as err:
            result=subprocess.run(argv,cwd=self.project,stdout=out,stderr=err)
        self.emit('CACHE_FIXTURE_EXECUTION.json',{'argv':argv,'cwd':str(self.project),'exit_code':result.returncode,
            'source_sha256':sha(HERE/'cache_negative_fixtures.py'),'contract_sha256':sha(HERE/'CACHE_FIXTURE_CONTRACT.json'),
            'result_sha256':sha(self.logs/'CACHE_FIXTURE_RESULT.json'),'stdout_sha256':sha(output),'stderr_sha256':sha(errors)})
        require(result.returncode==0,'Actual policy fixture process failed')
        self.require_fixtures()

    def require_fixtures(self):
        process=self.receipt('CACHE_FIXTURE_EXECUTION.json')
        require(process['exit_code']==0 and process['argv']==[sys.executable,str(HERE/'cache_negative_fixtures.py')]
                and process['source_sha256']==sha(HERE/'cache_negative_fixtures.py')
                and process['contract_sha256']==sha(HERE/'CACHE_FIXTURE_CONTRACT.json')
                and process['result_sha256']==sha(self.logs/'CACHE_FIXTURE_RESULT.json')
                and process['stdout_sha256']==sha(self.logs/'cache-fixtures.stdout.log')
                and process['stderr_sha256']==sha(self.logs/'cache-fixtures.stderr.log'),'Fixture process/command binding changed')
        value=self.receipt('CACHE_FIXTURE_RESULT.json');expected=read(HERE/'CACHE_FIXTURE_CONTRACT.json')['test_names']
        require(value['successful'] and value['test_names']==expected and value['tests_run']==len(expected)
                and value['failures']==value['errors']==value['skipped']==0,'Mandatory actual pre-exec policy fixtures did not pass')

    def acquire(self):
        self.require_fixtures()
        require(not self.inputs.exists(),'Fresh cache-input directory required');self.inputs.mkdir(parents=True)
        reader=ArchiveReader(self.anchor)
        rows=list(self.index['objects'].items())
        with ThreadPoolExecutor(max_workers=4) as pool:
            results=list(pool.map(lambda item:reader.fetch(item[0],item[1],self.inputs),rows))
        require(sha(self.inputs/'CHECKPOINT.json')==CHECKPOINT_SHA,'Wrong original checkpoint')
        self.emit('CACHE_ACQUISITION.json',{'status':'EXACT_SELECTIVE_RAW_INPUTS_ONLY','artifact_metadata':reader.metadata,
                  'members':results,'input_bytes':sum(r['bytes'] for r in results),'whole_archive_downloaded':False,'proof_acceptance':False})

    def original(self):
        self.receipt('CACHE_ACQUISITION.json');checked(self.inputs/'CHECKPOINT.json',self.index['objects']['CHECKPOINT.json'])
        if self._raw is not None:return self._raw
        raw=read(self.inputs/'CHECKPOINT.json')
        require(raw['schema']=='t01-coherent-build-checkpoint-v3' and str(raw['run_id'])==str(self.anchor['run'])
                and raw['runtime_audit_valid'] and raw['all_dependency_source_pins_valid'],'Wrong original coherent checkpoint schema/receipts')
        self._raw=raw
        return raw

    def rows(self):
        if self.scope==NATIVE:return self.prerequisites['rows']+self.selection['rows']
        return [{'module':'ImbalancedChen.P5SubdivisionStoredParentTypes',
                 'source':next(x for x in self.selection['genuineFacetsAndSource'] if x['path'].endswith('.lean')),
                 'facets':[x for x in self.selection['genuineFacetsAndSource'] if not x['path'].endswith('.lean')]}]

    def root_for(self,name=None):
        package=('mathlib' if name is not None and name.startswith('Cache.') else
                 'batteries' if name is not None and name.startswith('Batteries.') else
                 'LeanArchitect' if name is not None and (name=='Architect' or name.startswith('Architect.')) else 'goldbach')
        if name is not None and (name.startswith('Cache.') or name.startswith('Batteries.')):
            return self.project/'.lake/packages'/package
        return self.project/'.lake/packages'/package if self.scope==NATIVE else self.project

    def mapping(self,raw,path):
        value=str(path);old=raw['runtime_state']
        pairs=[(old['root'],str(self.project)),(str(Path(old['realbin']).parent),str(Path(self.state['realbin']).parent)),(old['shadow'],self.state['shadow'])]
        for before,after in pairs:
            if value==before or value.startswith(before+'/'):return after+value[len(before):]
        return value

    def map_value(self,raw,value):
        if isinstance(value,str):return self.mapping(raw,value)
        if isinstance(value,list):return [self.map_value(raw,x) for x in value]
        if isinstance(value,dict):return {k:self.map_value(raw,v) for k,v in value.items()}
        return value

    def historical_file(self,raw,path):
        previous=self._historical_cache.get(str(path))
        if previous is not None:return previous
        files=raw['files'];entry=files.get(str(path))
        if entry is None: entry=next((r for r in files.values() if r['resolved_path']==str(path)),None)
        require(entry is not None,'Historical imported file lacks a SHA receipt: '+str(path))
        current=Path(self.mapping(raw,path)).resolve(strict=True)
        info=current.stat();token=(info.st_dev,info.st_ino,info.st_size,info.st_mtime_ns)
        if self._part_cache.get(str(current))!=token:
            checked(current,entry);self._part_cache[str(current)]=token
        value={'historical_path':str(path),'path':str(current),'bytes':entry['bytes'],'sha256':entry['sha256']}
        self._historical_cache[str(path)]=value
        return value

    def setup_inputs(self,raw,setup):
        result={};arts=setup['importArts'];items=arts.items() if isinstance(arts,dict) else arts
        for name,arrays in items:
            require(name not in result and isinstance(arrays,list) and arrays,'Bad actual import map')
            parts=[]
            for group in arrays:
                require(isinstance(group,list) and group,'Empty physical import group')
                for path in group:
                    old=Path(path)
                    if not old.is_absolute():old=Path(raw['runtime_state']['root'])/old
                    parts.append(self.historical_file(raw,old))
            require(any(p['path'].endswith('.olean') for p in parts),'No public imported olean')
            result[name]=parts
        libraries=[]
        for field in ['dynlibs','plugins']:
            for value in setup[field]:
                path=value if isinstance(value,str) else value['path']
                old=Path(path)
                if not old.is_absolute():old=Path(raw['runtime_state']['root'])/old
                libraries.append({'kind':field,**self.historical_file(raw,old)})
        return result,libraries

    def validate_environment(self,raw):
        root=self.root_for()
        lock=read(self.project/'lake-manifest.json');packages={p['name']:p for p in raw['packages']}
        require(len(lock['packages'])==len(packages),'Dependency package set changed')
        for p in lock['packages']:
            old=packages[p['name']];directory=self.project/'.lake/packages'/p['name']
            require(old['pin_matches'] and old['tracked_sources_clean'] and old['rev']==p['rev']
                    and git('-C',directory,'rev-parse','HEAD').decode().strip()==p['rev'] and not git('-C',directory,'diff','HEAD','--'),'Package pin/source changed')
        # Root project profiles differ between T01 and P2; do not equate them.
        if self.scope==NATIVE:
            require(sha(root/'lakefile.toml')=='fb01f3330623d8a6aa20e81e86b93da41df1272fd85f5528da6c9631e0e9822f','Native package compiler configuration changed')
            require(sha(self.project/'lakefile.toml')=='b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254',
                    'P2 root must retain b47a profile; old T01 root objects/profile cannot be adopted')
        else:require(sha(self.project/'lakefile.toml')==self.selection['candidateFullInputProfileSHA256'],'Parent project profile changed')
        wrapper_paths={raw['runtime_state']['shadow']+'/bin/'+name for name in raw['runtime_state']['tools']}
        payloads={path:expected for path,expected in raw['runtime_state']['runtime_sha256'].items() if path not in wrapper_paths}
        require(len(payloads)==11,'Wrong original runtime payload census')
        for path,expected in payloads.items():require(sha(self.mapping(raw,path))==expected,'Original selected runtime payload changed')
        for entry in raw['native_and_toolchain_library_ABI_receipts']:checked(Path(self.mapping(raw,entry['original_path'])).resolve(strict=True),entry)

    def restore_facets(self,raw,facets,root,package):
        outputs=[]
        for facet in facets:
            payload=self.inputs/facet['object'];checked(payload,facet)
            relative=Path(facet['path']);target=root/relative
            require(not relative.is_absolute() and '..' not in relative.parts and relative.parts[:2]==('.lake','build') and not target.is_symlink() and target.resolve().is_relative_to((root/'.lake/build').resolve()),'Unsafe raw facet destination')
            old_root=Path(raw['runtime_state']['root'])/root.relative_to(self.project)
            previous=raw['files'].get(str(old_root/relative))
            require(previous and previous['payload']==facet['object'] and previous['sha256']==facet['sha256'] and previous['bytes']==facet['bytes'],'Facet not bound by original schema')
            if target.exists():checked(target,facet)
            else:
                target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(payload,target);target.chmod(previous['mode'])
            checked(target,facet)
            with (self.logs/'CACHE_RESTORE_JOURNAL.jsonl').open('a') as journal:journal.write(json.dumps({'path':str(target),'bytes':facet['bytes'],'sha256':facet['sha256'],'scope':self.scope,'binding':self.binding})+'\n')
            outputs.append({'path':str(target),'bytes':facet['bytes'],'sha256':facet['sha256'],'object':facet['object']})
        return outputs

    def restore_module(self,raw,row):
        root=self.root_for(row['module'])
        source=root/row['source']['path'];checked(source,row['source']);checked(self.inputs/row['source']['object'],row['source'])
        require(source.read_bytes()==(self.inputs/row['source']['object']).read_bytes(),'Current pinned source differs from raw producer bytes')
        outputs=self.restore_facets(raw,row['facets'],root,row.get('package','goldbach'))
        from checkpoint_original_protocol import lake_descriptor_binding
        relative=Path(*row['module'].split('.'));stem=root/'.lake/build/lib/lean'/relative;ir=root/'.lake/build/ir'/relative
        trace=read(stem.with_suffix('.trace'))
        require(trace['schemaVersion']=='2025-09-10' and trace['synthetic'] is False,'Not an original complete Lake trace')
        checks=lake_descriptor_binding(trace['outputs'],stem,ir)
        require(checks and all(r['matched'] for r in checks),'Original trace descriptors do not match real sidecars')
        return {'module':row['module'],'source':{'path':str(source),'bytes':row['source']['bytes'],'sha256':row['source']['sha256']},'facets':outputs}

    def restore(self):
        if self.scope in {NATIVE,PARENT}:
            from cache_bootstrap import validate
            validate(self)
        raw=self.original();self.validate_environment(raw);oldroot=raw['runtime_state']['root']
        old_compilations={r['module']:r for r in raw['all_guarded_package_compilations'] if r.get('package') in {'goldbach','LeanArchitect'} and 'module' in r}
        old_modules={r['module']:r for r in raw['modules']}
        restored=[]
        for row in self.rows():
            root=self.root_for(row['module'])
            prior=old_compilations[row['module']] if self.scope==NATIVE else old_modules[row['module']]
            if self.scope==NATIVE:
                classified=prior['classification']=='PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND'
                if row['module']=='Architect.Command':classified=self.command_leaf(prior,raw)
                require(classified and prior['lake_completed_trace']
                        and prior['output_bound_command'] and not prior['missing_actual_import_artifacts'],'Quarantined original native output')
            else:require(prior['completed_guarded_compile_candidate'],'Quarantined parent output')
            if self.scope==NATIVE:
                command=[x.replace(oldroot,'{root}') for x in prior['command']['command']]
                require(command==row['guardedCommandNormalized'] and not any(x.startswith('-D') for x in prior['command']['input_args']),'Historical native command/profile changed')
            restored.append(self.restore_module(raw,row))
        self.policy_audit()
        self.emit('CACHE_RAW_RESTORE.json',{'status':'AUTHENTIC_FACETS_RESTORED_PENDING_STOCK_NO_BUILD','modules':restored,
                  'historical_root_project_profile_not_asserted_equal':self.scope==NATIVE,'all_trace_setup_and_output_bytes_unmodified':True,'proof_acceptance':False})

    def leaf_runtime_identity(self,raw,rule,label):
        current_install=self.logs/'install-toolchain.log';text=current_install.read_text()
        require(rule['same_run_install_artifact']['observed_url'] in text
                and rule['same_run_install_artifact']['version_output'] in text,'Current original installer URL/version/commit/target differs')
        asset=rule['official_asset'];url='https://api.github.com/repos/leanprover/lean4/releases/assets/'+str(asset['id'])
        request=urllib.request.Request(url,headers={'Authorization':'Bearer '+os.environ['GH_TOKEN'],
            'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28'})
        with urllib.request.urlopen(request,timeout=60) as response:metadata=json.load(response)
        require(all(metadata.get(k)==v for k,v in asset.items()),'Official pinned distribution asset identity changed')
        require(rule['historical_matched_runtime_payloads']=={p:h for p,h in raw['runtime_state']['runtime_sha256'].items()
                    if p not in {raw['runtime_state']['shadow']+'/bin/'+n for n in raw['runtime_state']['tools']}},'Single-leaf runtime census differs')
        runtime=[]
        for path,expected in rule['historical_matched_runtime_payloads'].items():
            current=Path(self.mapping(raw,path));require(sha(current)==expected,'Leaf runtime payload differs');runtime.append({'path':str(current),'sha256':expected})
        require(len(rule['abi_receipts'])==8 and rule['abi_receipts']==raw['native_and_toolchain_library_ABI_receipts'],'Single-leaf ABI census differs')
        for row in rule['abi_receipts']:checked(Path(self.mapping(raw,row['original_path'])).resolve(strict=True),row)
        script="import json,os;print(json.dumps({k:os.environ.get(k,'') for k in ['LEAN_PATH','LEAN_SYSROOT']}))"
        search_process=self.run(label+'-search-path',['lake','--no-build','env',sys.executable,'-c',script])
        search=read(search_process['stdout']);require(search['LEAN_SYSROOT']==self.state['shadow'],'Leaf sysroot origin changed')
        official={Path(self.state['shadow']).joinpath('lib/lean').resolve(),Path(self.state['realbin']).parent.joinpath('lib/lean').resolve()}
        roots=[self.project/'.lake/build/lib/lean']+[self.project/'.lake/packages'/p['name']/'.lake/build/lib/lean' for p in raw['packages']]
        allowed={p.resolve() for p in roots}|official
        actual=[Path(p).resolve() for p in search['LEAN_PATH'].split(os.pathsep) if p]
        require(set(actual)<=allowed,'Unreviewed Lean search-path root')
        for root in set(actual)|{p.resolve() for p in roots}:
            if root in official:continue
            for core in ['Lean','Init','Std']:
                require(not (root/core).exists() and not list(root.glob(core+'.*')),'Package/project shadows official Lean core')
        return {'current_install_log_sha256':sha(current_install),'official_asset':metadata,'runtime_payloads':runtime,
                'abi_receipts':rule['abi_receipts'],'search_path_process':search_process,'search_path':search}

    def command_leaf(self,prior,raw):
        rule_path=HERE/'inputs/ARCHITECT_COMMAND_LEAF_RULE.json';rule=read(rule_path)
        workspace=Path(os.environ['GITHUB_WORKSPACE']);sys.path.insert(0,str(workspace/os.environ['P2_BUNDLE']))
        from p2_validation import load_bound_bundle
        manifest,binding=load_bound_bundle()
        require(manifest['compile_cache']['architect_command_leaf_rule_sha256']==sha(rule_path), 'Single-leaf rule not explicitly adopted')
        require(rule['schema']=='p2-leanarchitect-command-toolchain-leaf-qualification-v1'
                and prior['classification']==rule['original_classification']=='PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED'
                and prior['command']==rule['original_guarded_command'] and prior['actual_import_count']==0
                and prior['actual_import_map_sha256']==rule['old_map_hash'] and not prior['missing_actual_import_artifacts'],
                'Original isolated single-leaf evidence changed')
        evidence=HERE/'inputs/ARCHITECT_COMMAND_RAW'
        for row in rule['original_evidence']:checked(evidence/row['path'],row)
        require(read(self.inputs/prior['setup']['payload'])==rule['old_setup'], 'Single leaf no longer has its exact empty package import setup')
        trace_path=next(x for x in prior['facet_files'] if x['original_path'].endswith('.trace'))
        trace=read(self.inputs/trace_path['payload'])
        require(trace['depHash']==rule['old_trace_dephash'] and trace['schemaVersion']=='2025-09-10' and trace['synthetic'] is False,
                'Wrong original leaf trace')
        identity=self.leaf_runtime_identity(raw,rule,'architect-command')
        self.emit('CACHE_ARCHITECT_COMMAND_LEAF.json',{'status':'SEPARATE_RELEASE_ORIGIN_AND_ABI_LEAF_PENDING_CURRENT_STOCK_NO_BUILD',
            'rule_sha256':sha(rule_path),'original_classification_preserved':prior['classification'],
            'historical_per_core_olean_hashes_available':False,'historical_core_bytes_verified':False,
            **identity,'old_trace_dephash':trace['depHash'],'proof_acceptance':False})
        return True

    def verify_restored(self,name='CACHE_RAW_RESTORE.json'):
        receipt=self.receipt(name)
        for row in receipt['modules']:
            checked(row['source']['path'],row['source'])
            for facet in row['facets']:checked(facet['path'],facet)
            relative=Path(*row['module'].split('.'));root=self.root_for(row['module']);expected={f['path'] for f in row['facets']}
            actual={str(p) for directory in ['.lake/build/lib/lean','.lake/build/ir'] for p in (root/directory/relative).parent.glob(relative.name+'.*') if p.is_file()}
            require(actual==expected,'Cache outputs added/removed, including possible .nobuild: '+row['module'])
        return receipt

    def run(self,label,argv):
        self.policy_audit();directory=self.logs/'cache-processes';directory.mkdir(exist_ok=True)
        out=directory/(label+'.stdout');err=directory/(label+'.stderr');require(not out.exists() and not err.exists(),'Repeated stock process')
        with out.open('wb') as stdout,err.open('wb') as stderr:
            result=subprocess.run(list(map(str,argv)),cwd=self.project,stdout=stdout,stderr=stderr)
        row={'argv':list(map(str,argv)),'cwd':str(self.project),'exit_code':result.returncode,
             'stdout':str(out),'stdout_sha256':sha(out),'stderr':str(err),'stderr_sha256':sha(err)}
        write(directory/(label+'.json'),{'binding':self.binding,**row})
        self.policy_audit()
        if result.returncode!=0:
            shutil.copyfile(out,self.logs/'CACHE_FAILURE_PROCESS.stdout.log');shutil.copyfile(err,self.logs/'CACHE_FAILURE_PROCESS.stderr.log')
        require(result.returncode==0,'Stock no-build qualification rejected; no rebuild fallback: '+label)
        return row

    def qualify_setups(self,raw,names,selected_rows,target,label):
        import hashlib as _hashlib
        shared={};rows=[]
        def compare_setup(name,current,result,line_number):
            relative=Path(*name.split('.'));root=self.root_for(name)
            historical_setup=read(root/'.lake/build/ir'/relative.with_suffix('.setup.json'))
            expected=self.map_value(raw,historical_setup)
            if current!=expected:
                shutil.copyfile(result['stdout'],self.logs/'CACHE_FAILURE_SETUP.actual.json')
                write(self.logs/'CACHE_FAILURE_SETUP.expected.json',expected)
            require(current==expected,'Official current full setup differs after the sole explicit root mapping: '+name)
            imports,libraries=self.setup_inputs(raw,historical_setup)
            observed={module:[[part['historical_path'],part['sha256']] for part in parts] for module,parts in imports.items()}
            old_hash=_hashlib.sha256(json.dumps(observed,sort_keys=True,separators=(',',':')).encode()).hexdigest()
            selected=next(r for r in selected_rows if r['module']==name)
            if 'priorActualImportMapSHA256' in selected:
                require(old_hash==selected['priorActualImportMapSHA256'] and len(imports)==selected['priorActualImportCount'],'Actual original import receipt map differs')
            else:require(old_hash==self.selection['actualImportReceiptMapSHA256'] and len(imports)==self.selection['actualImportCount'],'Parent actual import map differs')
            for parts in imports.values():
                for part in parts:
                    previous=shared.get(part['path']);require(previous is None or previous==part,'Imported file changed');shared[part['path']]=part
            for part in libraries:
                previous=shared.get(part['path']);require(previous is None or previous['sha256']==part['sha256'],'Library changed');shared[part['path']]=part
            rows.append({'module':name,'official_current_setup_process':result,'official_current_setup_stdout_line':line_number,
                         'historical_raw_setup_sha256':sha(root/'.lake/build/ir'/relative.with_suffix('.setup.json')),
                         'physical_import_count':len(imports),'original_import_map_sha256':old_hash,'current_all_fields_equal_after_explicit_root_mapping':True})
        # The pinned stock :setup facet is the compiler's mkModuleSetup.
        # Read one JSON line at a time: the complete 407 setups exceed 1 GB.
        for offset in range(0,len(names),16):
            batch_names=names[offset:offset+16]
            setup_targets=[target(n) for n in batch_names]
            result=self.run(label+'-'+str(offset).zfill(3),['lake','--no-build','--json','query',*setup_targets])
            with Path(result['stdout']).open() as output:
                for number,name in enumerate(batch_names,1):
                    line=output.readline();require(bool(line),'Missing stock setup target row')
                    compare_setup(name,json.loads(line),result,number)
                require(not output.read().strip(),'Extra stock setup target row')
        return rows,shared

    def qualify(self):
        raw=self.original();restore=self.verify_restored()
        names=[r['module'] for r in restore['modules']]
        targets=['@'+('LeanArchitect' if n=='Architect' or n.startswith('Architect.') else 'goldbach')+'/+'+n+':leanArts'
                 if self.scope==NATIVE else '+'+n+':leanArts' for n in names]
        process=self.run('stock-leanArts',['lake','--no-build','build',*targets]);self.verify_restored()
        target=lambda n: '@'+('LeanArchitect' if n=='Architect' or n.startswith('Architect.') else 'goldbach')+'/+'+n+':setup' if self.scope==NATIVE else '+'+n+':setup'
        rows,shared=self.qualify_setups(raw,names,self.rows(),target,'stock-setup')
        self.verify_restored()
        self.emit('CACHE_IMPORT_PARTS.json',{'parts':shared})
        self.emit('CACHE_QUALIFICATION.json',{'status':'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY','stock_process':process,'modules':rows,
                  'physical_parts_receipt_sha256':sha(self.logs/'CACHE_IMPORT_PARTS.json'),'protected_source_compiler_events':0,
                  'proof_or_full_kernel_acceptance':False,'all_original_caller_gates_still_required':True})

    def admit(self):
        self.require_fixtures();self.verify_restored();self.policy_audit()
        if self.scope==NATIVE:
            from cache_project import validate_all
            validate_all(self)
        qualification=self.receipt('CACHE_QUALIFICATION.json')
        require(qualification['status']=='PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY','Cache qualification required before admission')
        policy=read(self.logs/'CACHE_PREEXEC_POLICY.json');sources={}
        for row in policy['admitted_commands']:
            if row['phase']!='qualified-project':continue
            source=row['source'];path=Path(source['path']);require(path.is_file() and not path.is_symlink(),'Nonregular caller source')
            actual={'path':str(path),'bytes':path.stat().st_size,'sha256':sha(path)}
            for key in ['bytes','sha256']:
                if key in source:require(source[key]==actual[key],'Caller source differs from exact selected postimage')
            if row['classification']=='EXACT_ORIGINAL_CALLER_AUDIT':
                captured=self.logs/path.name
                if captured.exists():require(captured.read_bytes()==path.read_bytes(),'Audit differs from original generated log snapshot')
                else:shutil.copyfile(path,captured)
            sources[str(path)]=actual
        self.emit('CACHE_CALLER_INPUTS.json',{'status':'EXACT_CALLER_POSTIMAGES_AND_GENERATED_AUDITS_ADMITTED_ONCE',
            'qualification_sha256':sha(self.logs/'CACHE_QUALIFICATION.json'),'sources':sources,
            'audit_source_is_bound_to_original_caller_generator_and_preexec_snapshot':True})

    def caller_inputs(self):
        value=self.receipt('CACHE_CALLER_INPUTS.json')
        require(value['qualification_sha256']==sha(self.logs/'CACHE_QUALIFICATION.json'),'Caller admission qualification changed')
        policy=read(self.logs/'CACHE_PREEXEC_POLICY.json')
        expected={r['source']['path'] for r in policy['admitted_commands'] if r['phase']=='qualified-project'}
        require(set(value['sources'])==expected,'Caller source admission census changed')
        for source in value['sources'].values():checked(source['path'],source)
        return value

    def qualification_inputs(self):
        if self.scope in {NATIVE,PARENT}:
            from cache_bootstrap import validate
            validate(self)
        value=self.receipt('CACHE_QUALIFICATION.json')
        require(value['status']=='PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY'
                and [r['module'] for r in value['modules']]==[r['module'] for r in self.rows()]
                and value['protected_source_compiler_events']==0,'Cache qualification scope changed')
        processes=[value['stock_process']]+[r['official_current_setup_process'] for r in value['modules']]
        seen=set()
        for row in processes:
            if row['stdout'] in seen:continue
            seen.add(row['stdout'])
            require(row['exit_code']==0 and row['cwd']==str(self.project)
                    and sha(row['stdout'])==row['stdout_sha256'] and sha(row['stderr'])==row['stderr_sha256'],
                    'Actual stock qualification process evidence changed')
            record=Path(row['stdout']).with_suffix('.json')
            require(read(record)=={'binding':self.binding,**row},'Stock process receipt changed')
        if self.scope==NATIVE:
            leaf=self.receipt('CACHE_ARCHITECT_COMMAND_LEAF.json')
            require(leaf['rule_sha256']==sha(HERE/'inputs/ARCHITECT_COMMAND_LEAF_RULE.json')
                    and leaf['historical_per_core_olean_hashes_available'] is False
                    and leaf['original_classification_preserved']=='PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED'
                    and leaf['current_install_log_sha256']==sha(self.logs/'install-toolchain.log'),'Single-leaf identity evidence changed')
            for row in leaf['runtime_payloads']:require(sha(row['path'])==row['sha256'],'Single-leaf runtime changed')
            raw=self.original()
            for row in leaf['abi_receipts']:checked(Path(self.mapping(raw,row['original_path'])).resolve(strict=True),row)
        return value

    def validate_final(self):
        self.require_fixtures();self.verify_restored();self.policy_audit();self.caller_inputs();self.qualification_inputs()
        final=self.receipt('CACHE_FINAL_INPUT_AUDIT.json')
        require(final['status']=='PASS_UNCHANGED_CACHE_INPUTS_AND_ZERO_PROTECTED_EXEC'
                and final['qualification_sha256']==sha(self.logs/'CACHE_QUALIFICATION.json')
                and final['runtime_state_sha256']==sha(self.logs/'runtime/state.json')
                and final['command_log_sha256']==sha(self.state['log'])
                and final['denial_log_sha256']==sha(self.logs/'CACHE_COMPILER_DENIALS.jsonl')
                and final['preexec_events_sha256']==sha(self.logs/'CACHE_PREEXEC_EVENTS.jsonl'),'Cache final evidence changed')
        require(final['caller_inputs_sha256']==sha(self.logs/'CACHE_CALLER_INPUTS.json'),'Final caller admission changed')
        if self.scope in {NATIVE,PARENT}:
            require(final['bootstrap_qualification_sha256']==sha(self.logs/'CACHE_BOOTSTRAP_QUALIFICATION.json')
                    and final['bootstrap_restore_sha256']==sha(self.logs/'CACHE_BOOTSTRAP_RESTORE.json'),
                    'Final authentic bootstrap input binding changed')
        if self.scope==NATIVE:
            from cache_project import validate_all
            require(all(final.get(k)==v for k,v in validate_all(self).items()),'Final root89 receipt binding changed')
        parts=self.receipt('CACHE_IMPORT_PARTS.json')
        require(sha(self.logs/'CACHE_IMPORT_PARTS.json')==self.receipt('CACHE_QUALIFICATION.json')['physical_parts_receipt_sha256'],'Input receipt changed')
        for row in parts['parts'].values():checked(row['path'],row)

    def audit(self):
        self.require_fixtures()
        qualification=self.qualification_inputs();self.verify_restored();self.policy_audit()
        self.caller_inputs()
        parts=self.receipt('CACHE_IMPORT_PARTS.json')
        require(sha(self.logs/'CACHE_IMPORT_PARTS.json')==qualification['physical_parts_receipt_sha256'],'Import-part receipt changed')
        for row in parts['parts'].values():checked(row['path'],row)
        bootstrap_binding={'bootstrap_qualification_sha256':sha(self.logs/'CACHE_BOOTSTRAP_QUALIFICATION.json'),
                           'bootstrap_restore_sha256':sha(self.logs/'CACHE_BOOTSTRAP_RESTORE.json')}
        if self.scope==NATIVE:
            from cache_project import validate_all
            bootstrap_binding.update(validate_all(self))
        self.emit('CACHE_FINAL_INPUT_AUDIT.json',{'status':'PASS_UNCHANGED_CACHE_INPUTS_AND_ZERO_PROTECTED_EXEC','qualification_sha256':sha(self.logs/'CACHE_QUALIFICATION.json'),
                  **bootstrap_binding,
                  'runtime_state_sha256':sha(self.logs/'runtime/state.json'),'command_log_sha256':sha(self.state['log']),
                  'denial_log_sha256':sha(self.logs/'CACHE_COMPILER_DENIALS.jsonl'),
                  'preexec_events_sha256':sha(self.logs/'CACHE_PREEXEC_EVENTS.jsonl'),
                  'caller_inputs_sha256':sha(self.logs/'CACHE_CALLER_INPUTS.json'),'proof_acceptance':False})
        # The same immutable source-admission receipt also binds dynamic audit
        # exporter bytes before their first compiler execution.


def main():
    require(len(sys.argv)==2 and sys.argv[1] in {'fixtures','acquire','bootstrap','restore','qualify','admit','audit','validate_final','retain'},'Expected fixtures/acquire/bootstrap/restore/qualify/admit/audit/validate_final/retain')
    if sys.argv[1]=='retain':
        from cache_checkpoint_retain import main as retain
        retain();return
    session=CacheSession(os.environ['CACHE_SCOPE'])
    try:
        if sys.argv[1]=='bootstrap':
            from cache_bootstrap import bootstrap
            bootstrap(session)
        else:
            getattr(session,sys.argv[1])()
            if session.scope==NATIVE and sys.argv[1] in {'acquire','restore','qualify'}:
                from cache_project import ProjectSession, PRODUCERS
                for producer in PRODUCERS:getattr(ProjectSession(session,producer),sys.argv[1])()
    except Exception as error:
        failure=session.logs/'CACHE_FAILURE.json'
        if not failure.exists():write(failure,{'binding':session.binding,'phase':sys.argv[1],'error_type':type(error).__name__,'error':str(error),'no_rebuild_fallback':True,'proof_acceptance':False})
        raise


if __name__=='__main__':main()
