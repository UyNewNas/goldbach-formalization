"""Build a genuine-evidence v6 continuation; never execute Lean or a controller."""
import argparse
import ast
import base64
import datetime
import difflib
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
WORK = HERE.parent
V5_LOCAL = WORK / 'p29-v5-builder/generated-final'
PACKET = WORK / 'p29-qualified-resume/docs/verification/20261127-p2-9-omitted-qualifier-resume'
NEW_SOURCE = WORK / 'p29-qualified-resume/docs/source-only/20261127-p2-9-omitted-prime-wall-qualified/ImbalancedChen/P2FiniteMarkedGamma5OmittedPrimeWall.lean'
BASE = PurePosixPath('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
ROOT = BASE / 'project'
V5 = BASE / 'verification-standard-package-resume-v5'
V6 = BASE / 'verification-finset-prod-resume-v6'
TARGET = 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall'
REL = TARGET.replace('.', '/')
JOB = '1aadf7911aac4b80ab0a049f967aa3ba'
PROBE_PIN = {'bytes':1552271,'sha256':'706588ac2fe74f209fe256307f9d9073beb894e93baf45dd090928989ca54632'}
DRIVER_PIN = {'bytes':173842,'sha256':'76a2bf4b3e12e4dacb05bfe9cf138012271ef8a47947ef42cf35aefb0e77483f'}
CONTRACT_SHA = '1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf'
OLD_SOURCE_PIN = {'bytes':7887,'sha256':'4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c','git_blob':'ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e'}
NEW_SOURCE_PIN = {'bytes':7894,'sha256':'559c7c09e8b38e69f4b076ea8371a48a55b7611ca51482c62686c18db2ef5353','git_blob':'8b64194e1381c1dedb59b8d13c715aad0dd94e94'}
REQUEST_PIN = {'bytes':10116,'sha256':'a23bd3591815e5512e5ced3040f4d0be00169a7579f74b23beb641f2b30605db'}
LIMITS = {'cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600}
STAGES = ['batteries-composed-view-observation','omitted-direct-imports','normal-build']
RECEIPTS = ['ACTUAL_REQUEST.json','ACTUAL_TASK_JOIN.json','ACTUAL_TERMINAL_TASK.json','ACTUAL_STDOUT.log','ACTUAL_OUTCOME.json','FRESH_SERVICE_OBSERVATION.json']
FILES = ['driver.py','INPUT_CONTRACT.json','SERVICE_OBSERVATION.json','FAILURE.json','runtime-evidence/state.json','batteries-composed-view-observation-process.json','batteries-composed-view-observation.log','ACTUAL_FIRST_NAMESPACE_PATHS.json','omitted-direct-imports-process.json','omitted-direct-imports.lean','omitted-direct-imports.log','omitted-direct-imports-bindings.json','CURRENT_INPUT_ORIGIN_BINDING.json','normal-build-process.json','normal-build.log','ORIGINAL_V3_V4_GUARD_PREFIX.jsonl','BORROWED_OBJECTS.json','COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json','COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json','REUSED_V4_PACKAGE_VIEW.json','REUSED_ORIGINAL_QUALIFICATIONS.json']


class BuildError(ValueError):
    pass


def check(value, message):
    if not value:
        raise BuildError(message)


def pin(raw):
    return {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'git_blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()}


def verify(raw, expected):
    actual = pin(raw)
    check(all(actual[k] == expected[k] for k in ['bytes','sha256']), 'exact bytes or SHA256 differ')
    check('git_blob' not in expected or actual['git_blob'] == expected['git_blob'], 'Git blob identity differs')
    return raw


def read(path):
    check(path.is_file() and not path.is_symlink(), 'required regular input missing: '+str(path))
    return path.read_bytes()


def decode(row):
    return verify(base64.b64decode(row['base64'], validate=True), row)


def source_amendment(old, new, contract):
    verify(old, OLD_SOURCE_PIN);verify(new, NEW_SOURCE_PIN)
    lines = old.splitlines(keepends=True)
    check(lines[139] == b'          apply prod_le_prod\n', 'original diagnostic line differs')
    amended = list(lines);amended[139] = b'          apply Finset.prod_le_prod\n'
    check(b''.join(amended) == new and len(new)-len(old) == 7, 'source delta is not the exact one-token qualification')
    imports = lambda b: re.findall(rb'^import\s+(\S+)', b, re.M)
    check(imports(old) == imports(new) == [s.encode() for s in contract['target']['direct_imports']], 'source imports changed')
    return {'schema':'p29_exact_target_name_qualification_amendment_v1','historical_dependency_contract_sha256':CONTRACT_SHA,'original_failed_job':JOB,'module':TARGET,'original_source':OLD_SOURCE_PIN,'repaired_source':{**NEW_SOURCE_PIN,'base64':base64.b64encode(new).decode()},'exact_line':140,'original_line':lines[139].decode(),'repaired_line':amended[139].decode(),'inserted_bytes':'Finset.','all_other_source_bytes_identical':True,'direct_imports_unchanged':contract['target']['direct_imports'],'historical_dependency_contract_not_rewritten':True,'source_only_until_actual_new_normal_kernel_owned_results':True,'new_formal_credit':0}


def source_rows(raw):
    check(raw.endswith(b'\n'), 'guard prefix must contain complete JSONL rows')
    rows = [json.loads(line) for line in raw.splitlines() if line]
    return [r for r in rows if r.get('tool') == 'lean' and any(str(a).endswith('.lean') for a in r.get('input_args', []))]


def validate_guard(original, live, records):
    check(live.startswith(original) and not source_rows(original), 'v5 historical prefix changed or contains an old source call')
    pos = len(original)
    for label, rec in zip(STAGES, records, strict=True):
        check(rec['stage'] == label and rec['forbidden_source_calls'] == [] and rec['exit_code'] == (1 if label == 'normal-build' else 0), 'v5 stage boundary differs')
        a, b = rec['guard_log_start'], rec['guard_log_end']
        check(a == pos and a <= b <= len(live), 'v5 guard slices have a gap or overlap')
        check([json.loads(line) for line in live[a:b].splitlines() if line] == rec['guarded_commands'], 'v5 raw guard slice differs from process record')
        pos = b
    check(pos == len(live), 'unattributed live guard tail')
    failed = [r for r in records[-1]['guarded_commands'] if r.get('tool') == 'lean' and any(str(a).endswith('.lean') for a in r.get('input_args', []))]
    check(len(failed) == 1 and source_rows(live) == failed, 'exactly the one failed v5 target source invocation is required')
    check([str(a) for a in failed[0]['input_args'] if str(a).endswith('.lean')] == [str(ROOT/(REL+'.lean'))], 'historical source invocation is not the target')
    return failed[0]


def validate_main_only(old, new):
    old_tree, new_tree = ast.parse(old), ast.parse(new)
    old_functions = {n.name:n for n in old_tree.body if isinstance(n,ast.FunctionDef)}
    new_functions = {n.name:n for n in new_tree.body if isinstance(n,ast.FunctionDef)}
    check(old_functions.keys() == new_functions.keys(), 'function inventory changed')
    names = sorted(set(old_functions)-{'main'})
    for name in names:
        check(ast.get_source_segment(old,old_functions[name]) == ast.get_source_segment(new,new_functions[name]), 'helper bytes changed: '+name)
    rest = lambda tree: ast.Module(body=[n for n in tree.body if not(isinstance(n,ast.FunctionDef) and n.name=='main')],type_ignores=[])
    check(ast.dump(rest(old_tree),include_attributes=False) == ast.dump(rest(new_tree),include_attributes=False), 'non-main AST changed')
    start = " normal_cmd=viewprefix+['lean'"
    end = " stable();assert source_outputs()==produced and sha(src)==source_sha\n"
    extract = lambda text: text[text.index(start):text.index(end,text.index(start))+len(end)]
    check(extract(old) == extract(new), 'normal/post-import/kernel/owned/final-audit sequence changed')
    new_main = new_functions['main']
    stages = [n.args[0].value for n in ast.walk(new_main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='stage' and n.args and isinstance(n.args[0],ast.Constant)]
    check(stages == ['normal-build','runtime-final-audit'], 'main would rerun an old successful stage or add a stage')
    calls = [n for n in ast.walk(new_main) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='actual_inputs']
    check(len(calls) == 1 and calls[0].args[0].value == 'consumer-actual-imports', 'successful direct import would be replayed')
    def source_stamps(main):
        found=[]
        for node in ast.walk(main):
            if not isinstance(node,ast.Assign):continue
            for target in node.targets:
                if not(isinstance(target,ast.Subscript) and isinstance(target.value,ast.Name) and target.value.id=='cache_before'):continue
                key=target.slice
                if isinstance(key,ast.Call) and isinstance(key.func,ast.Name) and key.func.id=='str' and len(key.args)==1 and isinstance(key.args[0],ast.Name) and key.args[0].id=='src':found.append(node)
        return sorted(found,key=lambda node:node.lineno)
    old_stamps,new_stamps=source_stamps(old_functions['main']),source_stamps(new_main)
    check(len(old_stamps)==1 and len(new_stamps)==2 and ast.dump(old_stamps[0],include_attributes=False)==ast.dump(new_stamps[0],include_attributes=False), 'original target stamp binding changed or additional target transitions appeared')
    check(ast.get_source_segment(new,new_stamps[1])=='cache_before[str(src)]=new_source_stat','authorized target stamp transition differs')
    return names


def load_context(probe_path):
    probe_raw = verify(read(probe_path), PROBE_PIN);report = json.loads(probe_raw)
    check(report['schema']=='p29_v5_completed_failure_readonly_probe_v1' and report['v5_job_id']==JOB and report['root']==str(V5), 'actual v5 probe identity differs')
    check(report['new_Lean_calls']==report['writes_to_remote_workspace']==report['new_formal_credit']==0, 'probe effects differ')
    source_raw = verify(read(V5_LOCAL/'postimage.py'),DRIVER_PIN)
    check(set(report['files'])==set(FILES), 'probe file inventory differs')
    bodies = {}
    for name,row in report['files'].items():
        check(row['exists'] is True and row['path']==str(V5/name) and len(row['stat'])==5 and row['stat'][2]==row['bytes'], 'v5 file path/stat differs: '+name)
        if 'base64' in row:bodies[name]=decode(row)
    check(bodies['driver.py']==source_raw, 'actual v5 driver differs from reviewed source')
    contract_raw=bodies['INPUT_CONTRACT.json'];check(pin(contract_raw)['sha256']==CONTRACT_SHA,'historical contract changed');contract=json.loads(contract_raw)
    old_source=decode(report['old_target_source']);new_source=read(NEW_SOURCE)
    amendment=source_amendment(old_source,new_source,contract)
    for suffix,row in report['target_outputs'].items():
        check(row=={'path':str(ROOT/'.lake/build/lib/lean'/(REL+suffix)),'exists':False,'is_symlink':False}, 'existing target output prevents resume')
    check(set(report['target_outputs'])=={'.olean','.ilean','.trace','.setup.json'},'output absence inventory differs')
    metadata=report['actual_used_part_current_metadata']
    check(metadata['module_count']==6342 and metadata['parts']==metadata['part_count']==31074 and metadata['mismatches']==[] and metadata['fresh_part_hashes_claimed'] is False and metadata['roots']==contract['target']['direct_imports'],'prior actual-input metadata differs')
    check(report['Batteries_view']=={'path':str(BASE/'batteries-native-cache-view-v5/lib'),'symlink_count':960}, 'Batteries view changed')
    for name,count in [('COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json',569),('COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json',960)]:
        check(report['current_namespace_links'][name]=={'facets_checked':count,'mismatches':[]},'namespace link view changed')
    package=json.loads(bodies['REUSED_V4_PACKAGE_VIEW.json']);view=report['package_view']
    check(view['link']==str(ROOT/'.lake/packages') and view['link_target']==str(BASE/'packages-mathlib-resume-v4') and view['entries']==package['selected_package_paths'] and view['matches_saved_selected_package_paths'] is True,'package view changed')
    receipts={name:read(PACKET/'original-v5-submission'/name) for name in RECEIPTS}
    verify(receipts['ACTUAL_REQUEST.json'],REQUEST_PIN)
    request=json.loads(receipts['ACTUAL_REQUEST.json']);join=json.loads(receipts['ACTUAL_TASK_JOIN.json']);terminal=json.loads(receipts['ACTUAL_TERMINAL_TASK.json']);observation=json.loads(receipts['FRESH_SERVICE_OBSERVATION.json'])
    check(terminal['job_id']==terminal['task_id']==join['job_id']==JOB and terminal['status']=='failed' and terminal['exit_code']==1,'actual v5 terminal differs')
    check(terminal['log_bytes']==len(receipts['ACTUAL_STDOUT.log'])==2467 and terminal['log_discarded_bytes']==0 and terminal['log_truncated'] is False,'v5 stdout incomplete')
    check({k:request[k] for k in LIMITS}=={k:terminal[k] for k in LIMITS}==join['actual_limits']==LIMITS,'v5 task limits differ')
    check(bodies['SERVICE_OBSERVATION.json']==receipts['FRESH_SERVICE_OBSERVATION.json'] and pin(bodies['SERVICE_OBSERVATION.json'])['sha256']==join['observation_sha256'],'v5 observation differs')
    after=datetime.datetime.strptime(observation['clock_after']['current_time'],'%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=datetime.timezone.utc).timestamp()
    check(terminal['submitted_at']==join['actual_submitted_at'] and 0<=terminal['submitted_at']-after==join['submission_seconds_after_observation']<=join['submission_window_max_seconds']==300,'v5 actual submission freshness differs')
    check(observation['requested_MCP_limits']==contract['MCP_limits'] and observation['submission_observation_max_age_seconds']==300,'v5 requested observation envelope differs')
    failure=json.loads(bodies['FAILURE.json'])
    check([json.loads(l[len(b'P29_FAILURE '):]) for l in receipts['ACTUAL_STDOUT.log'].splitlines() if l.startswith(b'P29_FAILURE ')]==[failure],'v5 failure differs from actual stdout')
    check(failure['error']=='Gate failed: normal-build' and failure['completed_stages']==STAGES and failure['supplier_source_kernel_owned_replays']==0 and failure['partial_target_outputs_preserved']=={str(ROOT/(REL+'.lean')):{k:OLD_SOURCE_PIN[k] for k in ['bytes','sha256']}},'v5 failed-normal boundary differs')
    live=decode(report['live_guard_log']);prefix=bodies['ORIGINAL_V3_V4_GUARD_PREFIX.jsonl'];records=[json.loads(bodies[n+'-process.json']) for n in STAGES]
    failed_source=validate_guard(prefix,live,records)
    paths=json.loads(bodies['ACTUAL_FIRST_NAMESPACE_PATHS.json']);composed=json.loads(bodies['batteries-composed-view-observation.log'])
    check(composed=={'cwd':str(ROOT),'LEAN_PATH':':'.join(paths['actual_LEAN_PATH'])},'composed path observation differs')
    prefix_cmd=['python3',str(BASE/'original-tools/run_guarded.py'),'--state',str(V5/'runtime-evidence/state.json'),'lake','env','env','LEAN_PATH='+composed['LEAN_PATH']]
    tails=[['python3','-c','import json,os; print(json.dumps({"cwd":os.getcwd(),"LEAN_PATH":os.environ["LEAN_PATH"]}))'],['lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],['lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(ROOT/'.lake/build/lib/lean'/(REL+'.olean')),'-i',str(ROOT/'.lake/build/lib/lean'/(REL+'.ilean')),str(ROOT/(REL+'.lean'))]]
    for label,rec,tail in zip(STAGES,records,tails,strict=True):
        check(rec['command']==prefix_cmd+tail and rec['cwd']==str(ROOT) and rec['log_path']==str(V5/(label+'.log')) and rec['log_sha256']==report['files'][label+'.log']['sha256'],'v5 exact process/log binding differs: '+label)
    check(records[1]['stdin_sha256']==report['files']['omitted-direct-imports.lean']['sha256'],'v5 import stdin hash differs')
    origin=json.loads(bodies['CURRENT_INPUT_ORIGIN_BINDING.json'])
    check(origin['status']=='PASS_CURRENT_HEADER_FACET_IMPORT_UNION' and origin['module_count']==6342 and origin['part_count']==31074 and origin['actual_bindings_sha256']==report['files']['omitted-direct-imports-bindings.json']['sha256'] and len(origin['project_modules'])==58 and origin['formal_credit']==origin['supplier_source_kernel_owned_replays']==0,'original actual qualification differs')
    return {'source':source_raw.decode(),'probe_raw':probe_raw,'probe':report,'bodies':bodies,'contract_raw':contract_raw,'contract':contract,'old_source':old_source,'new_source':new_source,'amendment':amendment,'receipts':receipts,'records':records,'failed_source':failed_source,'prefix':prefix,'live':live,'composed':composed}


def bootstrap(changes, output_sha):
    return ("import pathlib,hashlib\np=pathlib.Path("+repr(str(V5))+")\nsource=(p/'driver.py').read_text()\nassert hashlib.sha256(source.encode()).hexdigest()=="+repr(DRIVER_PIN['sha256'])+"\nchanges="+repr([(a,b) for _,a,b in changes])+"\nfor before,after in changes:\n assert source.count(before)==1\n source=source.replace(before,after)\nassert hashlib.sha256(source.encode()).hexdigest()=="+repr(output_sha)+"\ncontract=(p/'INPUT_CONTRACT.json').read_text()\nassert hashlib.sha256(contract.encode()).hexdigest()=="+repr(CONTRACT_SHA)+"\ncache=(p/'READ_ONLY_CACHE_PROBE.json').read_text()\nassert len(cache.encode())==2729017 and hashlib.sha256(cache.encode()).hexdigest()=='58688582f77ce9fad0536e4e2077725e9d9b80c238b38d22b686ab377798ff74'\nexec(compile(source,'omitted-prime-wall-P2-finset-prod-resume-v6.py','exec'),{'__name__':'__main__','SOURCE_TEXT':source,'SOURCE_SHA256':"+repr(output_sha)+",'INPUT_CONTRACT_TEXT':contract,'CACHE_PROBE_TEXT':cache,'V5_PROBE_TEXT':globals()['V5_PROBE_TEXT'],'SERVICE_OBSERVATION_JSON':globals()['SERVICE_OBSERVATION_JSON'],'SERVICE_OBSERVATION_SHA256':globals()['SERVICE_OBSERVATION_SHA256']})\n").encode()


def build(probe_path, output):
    check(probe_path.is_file(),'actual v5 PROBE_RESULT.json is required')
    check(output.resolve().is_relative_to(HERE) and not output.exists() and not output.is_symlink(),'output must be a new directory within the authorized v6 builder')
    context=load_context(probe_path)
    from main_delta import make_changes
    changes=make_changes(context);source=context['source'];post=source
    for label,before,after in changes:
        check(post.count(before)==1,'replacement not unique: '+label);post=post.replace(before,after)
    helpers=validate_main_only(source,post)
    inverse=post
    for label,before,after in reversed(changes):
        check(inverse.count(after)==1,'inverse not unique: '+label);inverse=inverse.replace(after,before)
    check(inverse==source,'whole-file inverse differs');compile(post,'syntax-only-v6','exec')
    post_raw=post.encode();boot=bootstrap(changes,pin(post_raw)['sha256']);compile(boot,'syntax-only-v6-bootstrap','exec')
    patch=''.join(difflib.unified_diff(source.splitlines(keepends=True),post.splitlines(keepends=True),fromfile='v5/postimage.py',tofile='v6/postimage.py')).encode()
    amend=(json.dumps(context['amendment'],indent=2)+'\n').encode()
    binding={'schema':'p29_v6_exact_failed_normal_continuation_static_binding_v1','status':'STATIC_ONLY_NOT_SUBMITTED_OR_QUALIFIED','baseline_postimage':pin(source.encode()),'postimage':pin(post_raw),'bootstrap':pin(boot),'patch':pin(patch),'target_source_amendment':pin(amend),'unchanged_historical_contract_sha256':CONTRACT_SHA,'old_target_source':OLD_SOURCE_PIN,'repaired_target_source':NEW_SOURCE_PIN,'actual_probe':pin(context['probe_raw']),'required_probe_global':'V5_PROBE_TEXT','prior_job':JOB,'prior_receipts':{n:pin(b) for n,b in context['receipts'].items()},'all_non_main_helper_bytes_and_AST_unchanged':helpers,'unchanged_normal_post_import_kernel_owned_final_audit_sequence':True,'sole_explicit_target_stamp_rebinding_after_preserved_exact_source_amendment':True,'whole_file_inverse_exact':True,'replacement_labels':[label for label,_,_ in changes],'historical_actual_dependency_modules':6342,'historical_actual_dependency_parts':31074,'old_successful_stage_reinvocations':0,'supplier_replays':0,'historical_failed_target_source_invocations':1,'new_target_normal_invocations_authorized':1,'guard_prefix':pin(context['live']),'original_v3_v4_guard_prefix':pin(context['prefix']),'existing_Batteries_native_package_views_reused':True,'new_owned_output':str(V6),'local_controller_Lean_cloud_Git_execution':False,'new_formal_credit':0}
    artifacts={'postimage.py':post_raw,'bootstrap.py':boot,'V5_TO_V6.patch':patch,'TARGET_SOURCE_AMENDMENT.json':amend,'STATIC_BINDING.json':(json.dumps(binding,indent=2)+'\n').encode()}
    output.mkdir()
    for name,data in artifacts.items():
        with (output/name).open('xb') as stream:stream.write(data)
    return binding


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--probe',type=Path,default=PACKET/'PROBE_RESULT.json');parser.add_argument('--output',type=Path,default=HERE/'generated');args=parser.parse_args()
    try:result=build(args.probe,args.output)
    except (BuildError,KeyError,TypeError,ValueError) as error:print('V6_BUILD_BLOCKED: '+str(error),file=sys.stderr);raise SystemExit(2)
    print(json.dumps({k:result[k] for k in ['postimage','bootstrap','patch','target_source_amendment']},indent=2))
