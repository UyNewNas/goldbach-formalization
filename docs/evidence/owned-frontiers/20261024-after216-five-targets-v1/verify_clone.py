"""SOURCEONLY V4. Prepare one archive after real ROOT admission; no Git/process calls.

The embedded clone verifier uses this same bundle validation code with an archived
payload loader. It never reads .lake, imports repository code or executes evidence.
Only future prepare writes the new PACKAGE; all inputs and inherited216 are read-only.
"""

import argparse, gzip, hashlib, io, json

from collections import Counter

from pathlib import Path, PurePosixPath

PACKAGE = 'docs/evidence/owned-frontiers/20261024-after216-five-targets-v1'

BASE = 'docs/evidence/owned-frontiers/20261023-next-seven-targets-v1'

STATE = '.lake/proof-continuation/'

ORIGINAL_ROOT = '/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'

ORIGINAL_WINDOWS_ROOT = 'E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation'

BASE_MANIFEST_SHA = 'f73db134a34d61e77a684aa8f33fe3096e79aca8e113ba5d3c91df6732f67bd5'

BASE_PLAN_SHA = '80e56452f7fdfc0e6a381e699fd242b5561c3a8e5dd81d4904d90cf40a9c2e82'

INTAKE = STATE + 'rounds/20261023-root-next-five-after216-complete-original-evidence-intake-v1.json'

INTAKE_SHA = '0b60c45d54d8f481e9c47d47df1383b66fde68a4244944eeba00e89f452d9125'

BASE_COUNTS = {'owned_modules':216, 'complete_serialized_declarations':5962,
               'distinct_constant_fullnames':5943, 'original_owned_receipts_rehashed':154}

TARGETS = ('ImbalancedChen.Part4ActualThirdFiniteDensityReserve', 'ImbalancedChen.Part3ActualModeJointBetaPositiveCount',
           'ImbalancedChen.Part4ActualThirdOriginalCompactDomain', 'ImbalancedChen.Part3ActualClosedTCountLicense',
           'ImbalancedChen.Part3ActualRestrictedChartWeightCount')

AUDITS = {'finite_density_reserve':TARGETS[:1], 'positive_count':TARGETS[1:2],
          'original_compact_domain':TARGETS[2:3], 'closed_and_restricted':TARGETS[3:]}

ROOT_BINDING_FIELDS = ('terminal_independent_review','terminal_independent_execution_cp','root_protocol_verification','collector_execution_witness',
    'fresh_capture_refs','previous_root_acceptance','current_census','complete_declarations','formal_authority',
    'candidate_manifest','complete_original_evidence_intake','source_freeze','compiler_cachelib_freeze',
    'collector_source','collector_source_peer','collector_acceptance_proposal')

ROLES = {'root_acceptance', *ROOT_BINDING_FIELDS}

ROOT_STATUS = 'ROOT_NEXT_FIVE_AFTER216_ACTUAL221_TERMINAL_ACCEPTED'

ROOT_ACCEPTANCE = {'path':STATE+'source-reviews/20261024-root-next-five-after216-221-terminal-acceptance.json',
                   'sha256':'59a715d3e6f288d7042288e7a595c9103468348aefe387b705ac4e1456f5d59b'}

PROTOCOL_STATUS = 'ROOT_NEXT_FIVE_AFTER216_INDEPENDENT_TERMINAL_PROTOCOL_PASS_PENDING_FINAL_ACCEPTANCE'

PROTOCOL_FIELDS = {'status','created_utc','owned_modules','declaration_records','distinct_fullnames','original_owned_receipts',
    'derived_counts','added_modules','added_records','baseline_counts_recomputed','old216_entries_deep_equal',
    'old5962_records_deep_equal','all_complete_types_safety_std3_and_original_stock_logs_verified',
    'all_current_source_freeze_entries','graph_modules','native_graph_basis','verified_inputs',
    'actual_new_module_record_counts','new_fullname_collisions','external_closure_replayed',
    'project_import_closure_replayed','unconditional_main_proved','scope','trust_mode','census','complete_records','proposal','verifier'}

SCOPE = {'trust_mode':'NORMAL_IMPORTED_ENVIRONMENT_TRUST','main_1_plus_1_75':'OPEN','weighted_estimate':30,
         'external_closure_replayed':False,'project_import_closure_replayed':False,'unconditional_main_proved':False}

MAX_FILE = 64*1024*1024

MAX_TOTAL = 192*1024*1024

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def jsonbytes(value):
    return (json.dumps(value, indent=2, ensure_ascii=False)+'\n').encode('utf-8')

def relpath(value, state=False):
    need(isinstance(value, str) and value and '\x00' not in value, 'Invalid path')
    value = value.replace('\\', '/')
    for prefix in (ORIGINAL_ROOT, ORIGINAL_WINDOWS_ROOT):
        if value.lower().startswith(prefix.lower()+'/'):
            value = value[len(prefix)+1:]
            break
    if state and value.startswith(('rounds/','source-reviews/','publication-integrity/','audits/','cache/','runs/','lib/')):
        value = STATE+value
    p = PurePosixPath(value)
    need(not p.is_absolute() and ':' not in value and '\\' not in value and
         all(x not in ('','.','..') for x in value.split('/')), 'Unsafe relative path: '+value)
    return p.as_posix()

def reference(value, state=False):
    need(isinstance(value, dict) and set(value)=={'path','sha256'}, 'Exact path/SHA ref required')
    h = value['sha256']
    need(isinstance(h, str) and len(h)==64 and all(c in '0123456789abcdef' for c in h), 'Invalid SHA256')
    return {'path':relpath(value['path'], state), 'sha256':h}

def refmatch(left, right):
    return reference(left, True)==reference(right, True)

def member(root, rel, directory=False):
    rel = relpath(rel)
    p = root.joinpath(*PurePosixPath(rel).parts).resolve()
    need(p.is_relative_to(root.resolve()) and (p.is_dir() if directory else p.is_file()), 'Missing/unsafe member: '+rel)
    return p

def restore(package, row):
    need(set(row)=={'original_path','source_sha256','source_bytes','stored_path','stored_sha256','encoding'}, 'Payload row schema')
    need(type(row['source_bytes']) is int and 0<=row['source_bytes']<=MAX_FILE, 'Payload source size')
    raw = member(package, row['stored_path']).read_bytes()
    need(sha(raw)==row['stored_sha256'], 'Stored payload SHA')
    if row['encoding']=='gzip-mtime0-empty-filename':
        need(raw[:10]==b'\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff', 'Canonical gzip header')
        with gzip.GzipFile(fileobj=io.BytesIO(raw), mode='rb') as f:
            raw = f.read(row['source_bytes']+1)
    else:
        need(row['encoding']=='raw', 'Unknown payload encoding')
    need(len(raw)==row['source_bytes'] and sha(raw)==row['source_sha256'], 'Recovered source bytes/SHA')
    return raw

def identity(rows, label):
    need(isinstance(rows,list), label+' records list')
    result = {}
    for row in rows:
        key = (row['module'],row['name'])
        need(key not in result, 'Duplicate module/name: '+label)
        result[key] = row
    return result

def derived(census, rows):
    return {'owned_modules':len(census['modules']), 'complete_serialized_declarations':len(rows),
            'distinct_constant_fullnames':len({r['name'] for r in rows}),
            'original_owned_receipts_rehashed':len({relpath(e['owned_receipt'],True).lower() for e in census['modules'].values()})}

def scope(doc, keys=SCOPE):
    for key, value in keys.items():
        need(type(doc.get(key)) is type(value) and doc[key]==value, 'Scope: '+key)

def baseline(root):
    package = member(root,BASE,directory=True)
    bmraw = member(package,'archive-manifest.json').read_bytes()
    bpraw = member(package,'source-plan.json').read_bytes()
    need(sha(bmraw)==BASE_MANIFEST_SHA and sha(bpraw)==BASE_PLAN_SHA, 'Immutable actual216 manifest/plan')
    bm, bp = json.loads(bmraw), json.loads(bpraw)
    actual = {p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}
    need(actual==set(bm['files'])|{'archive-manifest.json'}, 'Actual216 package member set')
    for name, digest in bm['files'].items():
        need(sha(member(package,name).read_bytes())==digest, 'Actual216 member SHA: '+name)
    for row in bm['source_refs'].values():
        restore(package,row)
    need(bm['source_plan_sha256']==BASE_PLAN_SHA and bm['source_refs']['source_plan']['source_sha256']==BASE_PLAN_SHA,
         'Actual216 source-plan chain')
    oldc = json.loads(restore(package,bm['source_refs']['candidate_census']))
    oldr = json.loads(restore(package,bm['source_refs']['complete_records']))
    need(derived(oldc,oldr)==BASE_COUNTS and bm['measured_counts']==bp['accepted_counts'], 'Measured actual216 baseline')
    need(all(oldc[k]==v for k,v in BASE_COUNTS.items()), 'Actual216 primary census totals')
    return bm, oldc, oldr

def guarded(process, exit_key):
    need(process['status']=='PASS' and process[exit_key]==0 and process['guard_error'] is None, 'Original process status')
    need(process['rss_guard']['limit_mib']==6656 and not process['rss_guard']['signals'] and
         0<=process['max_rss_kib']<=6656*1024 and isinstance(process['resource_reason'],str) and
         process['resource_reason'].strip(), 'Original process RSS/resource reason')

def validate_bundle(refs, load, bm, oldc, oldr):
    need(set(refs)==ROLES and all(reference(v)==v and (k=='root_acceptance' or v['path'].startswith(STATE)) for k,v in refs.items()),
         'Exact repository-relative ROOT evidence roles')
    inputs = {}
    def raw(role, ref):
        ref = reference(ref,True)
        need(role not in inputs or inputs[role]==ref, 'Conflicting evidence role: '+role)
        inputs[role] = ref
        data = load(ref)
        need(sha(data)==ref['sha256'], 'Input SHA: '+role)
        return data
    def doc(role, ref):
        return json.loads(raw(role,ref))
    docs = {k:doc(k,v) for k,v in refs.items() if k!='collector_source'}
    raw('collector_source',refs['collector_source'])
    acc, peer, proto = docs['root_acceptance'], docs['terminal_independent_review'], docs['root_protocol_verification']
    need(refs['root_acceptance']==ROOT_ACCEPTANCE and acc['status']==ROOT_STATUS, 'Exact final ROOT221 acceptance bytes/status')
    for role in ROOT_BINDING_FIELDS:
        need(acc[role]==refs[role], 'Exact ROOT repo-relative binding: '+role)
    scope(acc)
    need(acc.get('scope') and acc['current_census_sha256']==refs['current_census']['sha256'], 'ROOT scope/census SHA')
    need(refs['previous_root_acceptance']['sha256']==bm['source_refs']['root_final_acceptance']['source_sha256'], 'Actual216 acceptance pin')
    oldacc = docs['previous_root_acceptance']
    need(oldacc['status']=='ROOT_NEXT_SEVEN_ACTUAL216_TERMINAL_ACCEPTED' and
         oldacc['current_census']['sha256']==bm['source_refs']['candidate_census']['source_sha256'] and
         oldacc['complete_declarations']['sha256']==bm['source_refs']['complete_records']['source_sha256'], 'Actual216 accepted records/census')
    intake = docs['complete_original_evidence_intake']
    need(refs['complete_original_evidence_intake']=={'path':INTAKE,'sha256':INTAKE_SHA} and
         intake['status']=='ROOT_COMPLETE_AFTER216_FIVE_TARGET_ORIGINAL_EVIDENCE_INTAKE_V1' and
         set(intake)=={'status','targets','strict_producers','audit_receipts'} and
         set(intake['targets'])==set(intake['strict_producers'])==set(TARGETS) and set(intake['audit_receipts'])==set(AUDITS), 'Pinned five-target/four-audit intake')
    prop, authority = docs['collector_acceptance_proposal'], docs['formal_authority']
    need(prop['status']=='PROPOSAL_ONLY_ROOT_ACCEPTANCE_REQUIRED' and prop['root_acceptance'] is None and
         prop['compiler_or_checker_started_by_collector']==0 and refmatch(prop['candidate_census'],refs['current_census']) and
         refmatch(prop['complete_declarations'],refs['complete_declarations']), 'True proposal output fields')
    need(prop['main_1_plus_1_75']=='OPEN' and prop['external_closure_replayed'] is False and
         prop['project_import_closure_replayed'] is False, 'Proposal trust/main scope')
    for field, role in (('authority','formal_authority'),('candidate_manifest','candidate_manifest'),
        ('complete_original_evidence_intake','complete_original_evidence_intake'),('baseline_acceptance','previous_root_acceptance'),
        ('fresh_all_current_source_freeze','source_freeze'),('compiler_cachelib_freeze','compiler_cachelib_freeze')):
        need(refmatch(prop[field],refs[role]), 'Proposal binding: '+field)
    need(authority['status']=='ROOT_AUTHORIZED_NEXT_FIVE_AFTER216_TERMINAL_PROPOSAL_V1' and
         authority['no_compiler_or_audit_invocation'] is True and authority['proposal_output_authorized'] is True and
         authority['targets']==intake['targets'] and authority['strict_producers']==intake['strict_producers'] and
         authority['audit_receipts']==intake['audit_receipts']==prop['actual_audits'], 'Original authority/intake scope')
    for field, role in (('collector','collector_source'),('collector_independent_peer','collector_source_peer'),
        ('complete_original_evidence_intake','complete_original_evidence_intake'),('candidate_manifest','candidate_manifest'),
        ('fresh_all_current_source_freeze','source_freeze'),('compiler_cachelib_freeze','compiler_cachelib_freeze'),('fresh_capture_refs','fresh_capture_refs')):
        need(refmatch(authority[field],refs[role]), 'Authority binding: '+field)
    collector_peer = docs['collector_source_peer']
    need(collector_peer['status'].startswith('PASS_SOURCEONLY_') and
         refmatch({'path':collector_peer['reviewed_collector'],'sha256':collector_peer['reviewed_collector_sha256']},refs['collector_source']), 'Reviewed collector source/peer')
    manifest = docs['candidate_manifest']
    need(manifest['status']=='SOURCEONLY_NEXT_FIVE_AFTER216_TERMINAL_MANIFEST_V1' and manifest['targets']==intake['targets'] and
         refmatch(manifest['baseline_acceptance'],refs['previous_root_acceptance']) and
         manifest['baseline_census']['sha256']==bm['source_refs']['candidate_census']['source_sha256'] and
         manifest['complete_records']['sha256']==bm['source_refs']['complete_records']['source_sha256'], 'Candidate manifest/baseline')
    capture, freeze, sources = docs['fresh_capture_refs'], docs['compiler_cachelib_freeze'], docs['source_freeze']
    need(capture['status']=='ROOT_NEXT_FIVE_AFTER216_V1_FRESH_INPUTS_CAPTURED_NOT_ACCEPTED', 'Capture status')
    for field, role in (('source_freeze','source_freeze'),('compiler_cachelib_freeze','compiler_cachelib_freeze'),
                        ('complete_original_evidence_intake','complete_original_evidence_intake'),('baseline_acceptance','previous_root_acceptance')):
        need(refmatch(capture[field],refs[role]), 'Capture binding: '+field)
    raw('capture_source',capture['capture_script'])
    need(collector_peer['reviewed_capture_sha256']==reference(capture['capture_script'])['sha256'] and
         relpath(collector_peer['reviewed_capture'],True)==reference(capture['capture_script'])['path'], 'Reviewed capture source/peer')
    need(freeze['status']=='ROOT_FROZEN_COMPILER_CACHELIB_INPUTS' and freeze['targets']==intake['targets'] and
         refmatch(freeze['complete_original_evidence_intake'],refs['complete_original_evidence_intake']) and
         freeze['normal_import_trust'] is True and freeze['external_closure_replayed'] is False and freeze['main_proved'] is False,
         'Original ROOT full freeze scope')
    need(capture['source_count']==freeze['source_count']==len(sources) and capture['graph_modules']==freeze['graph_modules']==len(freeze['graph_stable']['graph']), 'Capture/source/graph totals')
    witness = docs['collector_execution_witness']
    need(witness['status']=='ROOT_OBSERVED_ACTUAL_NEXT_FIVE_AFTER216_COLLECTOR_EXECUTION_EXIT0' and
         witness['observed_exit_code']==0 and witness['compiler_checker_started_by_collector'] is False and
         witness['root_terminal_acceptance_created_by_collector'] is False and
         witness['observed_stdout_json']['status']=='SOURCEONLY_PROPOSAL_WRITTEN_PENDING_ROOT_ACCEPTANCE', 'Observed collector witness')
    need(refmatch(witness['observed_stdout_json']['acceptance_proposal'],refs['collector_acceptance_proposal']) and
         refmatch(witness['observed_stdout_json']['candidate_census'],refs['current_census']), 'Observed exact output refs')
    cmd = witness['command']
    need(len(cmd)==9 and cmd[:2]==['/usr/bin/python3','-B'] and relpath(cmd[2],True)==refs['collector_source']['path'] and
         cmd[3]=='--root' and cmd[4]==ORIGINAL_ROOT and cmd[5]=='--authority' and
         relpath(cmd[6],True)==refs['formal_authority']['path'] and cmd[7:]==['--authority-sha256',refs['formal_authority']['sha256']], 'Observed collector command')
    census, records = docs['current_census'], docs['complete_declarations']
    oldmap, curmap = identity(oldr,'actual216'), identity(records,'candidate')
    new = [r for r in records if r['module'] in TARGETS]
    need(not set(TARGETS)&set(oldc['modules']) and set(census['modules'])==set(oldc['modules'])|set(TARGETS) and
         all(census['modules'][m]==e for m,e in oldc['modules'].items()) and all(curmap.get(k)==v for k,v in oldmap.items()) and
         len(records)==len(oldr)+len(new) and {r['module'] for r in new}==set(TARGETS), 'Exact additive whole-entry/full-record union')
    for key in ('historical_duplicate_groups','historical_duplicate_map','duplicate_metadata_evidence','duplicate_metadata_operator_peer',
                'historical_distinct_constant_fullnames','duplicate_constant_fullnames','duplicate_record_excess'):
        need(census[key]==oldc[key], 'Inherited duplicate metadata: '+key)
    duplicates = {k:v for k,v in Counter(r['name'] for r in records).items() if v>1}
    olddups = {k:v for k,v in Counter(r['name'] for r in oldr).items() if v>1}
    need(duplicates==olddups and len(duplicates)==11 and sum(v-1 for v in duplicates.values())==19 and
         census['historical_duplicate_names']==11 and census['historical_duplicate_record_excess']==19 and
         census['supplemental_metadata_counted_as_owned_receipt'] is False, 'Unchanged historical duplicates/no new metadata receipt')
    names = [r['name'] for r in new]
    need(len(names)==len(set(names)) and not set(names)&{r['name'] for r in oldr}, 'New fullname collisions')
    need(all(isinstance(r['type'],str) and r['type'] and '⋯' not in r['type'] and not(r['unsafe'] or r['partial'] or r['axiom']) and
         set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in records), 'Full safe/nonpartial/nonaxiom std3 types')
    scope(census,{k:v for k,v in SCOPE.items() if k not in ('main_1_plus_1_75','weighted_estimate')})
    need(census['status']=='CANDIDATE_CENSUS_PROPOSAL_PENDING_ROOT_ACCEPTANCE', 'Candidate census status')
    counts = derived(census,records)
    per = {m:sum(r['module']==m for r in new) for m in TARGETS}
    counts.update(added_modules=len(TARGETS),added_complete_serialized_declarations=len(new),added_distinct_constant_fullnames=len(set(names)),
                  added_original_receipts=len({relpath(census['modules'][m]['owned_receipt'],True).lower() for m in TARGETS}),actual_new_module_record_counts=per)
    need(all(census[k]==counts[k] for k in BASE_COUNTS) and counts['owned_modules']==BASE_COUNTS['owned_modules']+len(TARGETS) and
         counts['added_original_receipts']==len(AUDITS) and prop['complete_counts_computed_from_actual_records']==per, 'Derived census/per-module/receipt counts')
    amap = {'declarations':'complete_serialized_declarations','original_receipts':'original_owned_receipts_rehashed'}
    for k in counts:
        key = next((a for a,b in amap.items() if b==k),k)
        need(acc[key]==counts[k], 'ROOT measured count: '+key)
    need(acc['old216_whole_entries_deep_equal'] is True and acc['old5962_complete_records_deep_equal'] is True and
         acc['new_fullname_collisions']==census['new_fullname_collisions']==0 and
         acc['historical_duplicate_names']==11 and acc['historical_duplicate_record_excess']==19, 'ROOT baseline/collision/duplicate facts')
    measured = {k:counts[k] for k in BASE_COUNTS}
    need(peer['status']=='PASS_TERMINAL_EVIDENCE_PENDING_ROOT_SIGNATURE' and peer['blockers']==[] and
         peer['derived_counts']==measured and peer['derived_new_module_records']==per and
         peer['historical_entries_deep_equal']==len(oldc['modules']) and peer['historical_records_deep_equal']==len(oldr), 'Actual terminal peer counts/status')
    scope(peer)
    need(peer['explicit_protocol_version']=='AFTER216_FIVE_V1' and
         refmatch(peer['exact_reviewed_collector'],refs['collector_source']) and
         refmatch(peer['root_protocol'],refs['root_protocol_verification']) and
         refmatch(peer['root_protocol_verifier'],proto['verifier']), 'Peer exact collector/protocol bindings')
    for role in ('collector_execution_witness','collector_acceptance_proposal','current_census','complete_declarations','formal_authority',
                 'candidate_manifest','complete_original_evidence_intake','source_freeze','compiler_cachelib_freeze','collector_source','root_protocol_verification','fresh_capture_refs'):
        need(peer['verified_inputs'].get(ORIGINAL_ROOT+'/'+refs[role]['path'])==refs[role]['sha256'], 'Peer verified binding: '+role)
    execution = docs['terminal_independent_execution_cp']
    need(execution['status']=='INDEPENDENT_REVIEWER_OBSERVED_ACTUAL_READONLY_TERMINAL_VERIFIER_EXIT0' and
         execution['observed_verifier_exit_code']==execution['actual_tool_transcript']['exit_code']==0 and
         execution['observed_stdout_status']==peer['status'] and execution['peer_result_equals_original_stdout_bytes'] is True and
         refmatch(execution['peer_result'],refs['terminal_independent_review']) and
         execution['derived_counts']==measured and execution['derived_new_module_records']==per, 'Actual independent execution CP/result/counts')
    scope(execution)
    stdout = raw('terminal_peer_stdout',execution['stdout_log'])
    stderr = raw('terminal_peer_stderr',execution['stderr_log'])
    need(stdout==raw('terminal_independent_review',refs['terminal_independent_review']) and
         len(stdout)==execution['stdout_bytes'] and len(stderr)==execution['stderr_bytes']==0, 'Original terminal peer raw stdout/stderr')
    verifier = reference(execution['exact_verifier'],True)
    raw('terminal_peer_verifier',verifier)
    doc('terminal_peer_execution_authority',execution['ROOT_explicit_execution_authority'])
    need(verifier['sha256']==execution['self_verifier_sha256']==peer['self_verifier_sha256'], 'Independent verifier source pin')
    need(set(proto)==PROTOCOL_FIELDS and proto['status']==PROTOCOL_STATUS and proto['derived_counts']==measured and
         proto['owned_modules']==counts['owned_modules'] and proto['declaration_records']==len(records) and
         proto['distinct_fullnames']==counts['distinct_constant_fullnames'] and proto['original_owned_receipts']==counts['original_owned_receipts_rehashed'] and
         proto['added_modules']==len(TARGETS) and proto['added_records']==len(new) and proto['actual_new_module_record_counts']==per and
         proto['old216_entries_deep_equal'] is True and proto['old5962_records_deep_equal'] is True and
         proto['all_complete_types_safety_std3_and_original_stock_logs_verified'] is True and proto['new_fullname_collisions']==0 and
         proto['baseline_counts_recomputed']=={'owned_modules':216,'declarations':5962,'original_receipts':154,'distinct_constant_fullnames':5943}, 'Actual protocol complete schema/counts')
    scope(proto,{k:v for k,v in SCOPE.items() if k not in ('main_1_plus_1_75','weighted_estimate')})
    need(refmatch(proto['census'],refs['current_census']) and refmatch(proto['complete_records'],refs['complete_declarations']) and
         refmatch(proto['proposal'],refs['collector_acceptance_proposal']) and proto['all_current_source_freeze_entries']==len(sources) and
         proto['graph_modules']==freeze['graph_modules'], 'Actual protocol outputs/freeze')
    raw('root_protocol_source',proto['verifier'])
    verified = {relpath(p,True):h for p,h in proto['verified_inputs'].items()}
    for role in ('collector_execution_witness','collector_acceptance_proposal','current_census','complete_declarations','formal_authority',
                 'candidate_manifest','complete_original_evidence_intake','source_freeze','compiler_cachelib_freeze','collector_source','collector_source_peer','previous_root_acceptance'):
        need(verified.get(refs[role]['path'])==refs[role]['sha256'], 'Protocol verified binding: '+role)
    stable = freeze['graph_stable']
    for m in TARGETS:
        source = {'path':m.replace('.','/')+'.lean','sha256':intake['targets'][m]}
        raw('target_source.'+m,source)
        entry = census['modules'][m]
        need(entry['source_sha256']==source['sha256']==sources[source['path']] and
             entry['complete_serialized_declarations']==per[m], 'Five literal source bindings: '+m)
        spec = intake['strict_producers'][m]
        need(set(spec)=={'cache','receipt','stdout','resource_policy'} and spec['resource_policy']=={'memory_mib':6144,'rss_limit_mib':6656}, 'Original strict schema/resource policy')
        strict = {k:reference(spec[k],True) for k in ('cache','receipt','stdout')}
        need(strict['cache']['path']==STATE+'cache/'+m+'.json' and strict['receipt']['path'].startswith(STATE+'runs/') and
             PurePosixPath(strict['receipt']['path']).name=='receipt.json' and
             PurePosixPath(strict['stdout']['path'])==PurePosixPath(strict['receipt']['path']).with_name('stdout.log'), 'Original strict paths')
        cache = doc('strict.'+m+'.cache',strict['cache'])
        original = doc('strict.'+m+'.receipt',strict['receipt'])
        stdout = raw('strict.'+m+'.stdout',strict['stdout'])
        need(cache==original and original['module']==m and original['warnings_as_errors'] is True and original['lean_memory_mib']==6144, 'Original strict cache/receipt')
        guarded(original,'exit_code')
        need(original['binding']==original['binding_after'] and original['binding']['source_sha256']==source['sha256'] and
             original['binding']['pins']==stable['pins'] and original['runtime_sha256']==original['runtime_sha256_after'], 'Strict immutable source/pins/runtime')
        need(original['binding']['lean_wrapper_sha256']==stable['native_bins']['lean'] and
             original['binding']['lean_real_sha256']==stable['native_bins']['lean.real'] and original['object_parts']==entry['object_parts'], 'Strict binaries/owned slots')
        command = original['command']
        need(len(command)==7 and command[:5]==['/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/bin/lean','-j2','-M6144','-DwarningAsError=true','-o'] and
             relpath(command[5])==STATE+'lib/lean/'+m.replace('.','/')+'.olean' and command[6]==source['path'] and
             original['cwd']==ORIGINAL_ROOT and original['shared_lock']==ORIGINAL_ROOT.rsplit('/',1)[0]+'/goldbach-integration/.lake/takeover-p0/locks/compiler-0.lock', 'Exact original strict command/cwd/lock')
        checked = prop['strict_producers_verified'][m]
        need(checked['resource_policy']==spec['resource_policy'] and all(refmatch(checked[k],strict[k]) for k in strict), 'Proposal strict evidence bindings')
    covered, audit_refs = set(), set()
    for group, mods in AUDITS.items():
        spec = intake['audit_receipts'][group]
        need(set(spec)=={'ref','targets','sidecars'} and spec['targets']=={m:intake['targets'][m] for m in mods}, 'Exact four audit grouping')
        ar = reference(spec['ref'],True)
        need(ar['path'].startswith(STATE+'audits/') and PurePosixPath(ar['path']).name=='receipt.json' and ar['path'] not in audit_refs, 'Original unique audit path')
        audit_refs.add(ar['path'])
        need(acc['actual_audits'][group]==ar, 'ROOT exact audit binding')
        audit = doc('audit.'+group,ar)
        side = {'OwnedAudit.lean','declarations.json','declarations.log','audit-process.json'}|{'replay-'+m+'.'+e for m in mods for e in ('json','log')}
        need(set(spec['sidecars'])==side, 'Exact all original sidecars')
        data = {n:raw('audit_sidecar.'+group+'.'+n,{'path':str(PurePosixPath(ar['path']).with_name(n)),'sha256':h}) for n,h in spec['sidecars'].items()}
        need(audit['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and audit['targets']==spec['targets'] and
             audit['inputs_before']==audit['inputs_after'] and audit['inputs_after']['sources']==spec['targets'] and
             sha(data['OwnedAudit.lean'])==audit['generated_audit_sha256'], 'Original audit source/immutable input status')
        emitted = json.loads(data['declarations.json'])
        need(identity(emitted,group)==identity([r for r in new if r['module'] in mods],group+' candidate') and
             audit['declaration_counts']=={m:per[m] for m in mods}, 'Complete original audit records/counts')
        process = json.loads(data['audit-process.json'])
        guarded(process,'returncode')
        full = [s for s in audit['stages'] if s['kind']=='full_inventory_type_axioms']
        need(len(full)==1 and full[0]['exit_code']==0 and full[0]['command']==process['command'] and
             sha(data['declarations.log'])==full[0]['log_sha256'], 'Original inventory command/log')
        stocks = [s for s in audit['stages'] if s['kind']=='stock_replay']
        need(len(stocks)==len(mods) and {s['module'] for s in stocks}==set(mods), 'Exact stock replay coverage')
        for stage in stocks:
            m, result = stage['module'], stage['result']
            need(m not in covered, 'Duplicate audited module')
            covered.add(m)
            need(result==json.loads(data['replay-'+m+'.json']) and sha(data['replay-'+m+'.log'])==result['log_sha256'], 'Original stock JSON/log')
            guarded(result,'returncode')
            e = census['modules'][m]
            need(refmatch({'path':e['owned_receipt'],'sha256':e['owned_receipt_sha256']},ar), 'Census original audit receipt')
    need(covered==set(TARGETS) and len(audit_refs)==4, 'Exactly four audits cover all five targets')
    return counts, inputs

def clone_main(root):
    root = root.resolve()
    package = member(root,PACKAGE,directory=True)
    m = json.loads(member(package,'archive-manifest.json').read_bytes())
    need(m['schema']=='after216-five-target-original-evidence-archive-v3' and m['targets']==list(TARGETS), 'V3 archive identity')
    declared = set(m['files'])
    actual = {p.relative_to(package).as_posix() for p in package.rglob('*') if p.is_file()}
    need(actual==declared|{'archive-manifest.json'}, 'Exact archive members')
    for name, digest in m['files'].items():
        need(sha(member(package,name).read_bytes())==digest, 'Archive member SHA: '+name)
    source_rows = m['source_refs']
    lookup = {}
    for role, row in source_rows.items():
        ref = {'path':relpath(row['original_path']),'sha256':row['source_sha256']}
        key = (ref['path'],ref['sha256'])
        if key in lookup:
            need(lookup[key]['source_bytes']==row['source_bytes'], 'Conflicting duplicate source ref')
        lookup[key] = row
        restore(package,row)
    def load(ref):
        ref = reference(ref)
        need((ref['path'],ref['sha256']) in lookup, 'Archived original ref missing: '+ref['path'])
        return restore(package,lookup[(ref['path'],ref['sha256'])])
    planraw = member(package,'source-plan.json').read_bytes()
    plan = json.loads(planraw)
    need(sha(planraw)==m['source_plan_sha256'] and sha(member(package,'verify_clone.py').read_bytes())==m['verify_clone_sha256'], 'Plan/verifier manifest pins')
    bm, oldc, oldr = baseline(root)
    counts, inputs = validate_bundle(plan['refs'],load,bm,oldc,oldr)
    need(set(inputs)==set(source_rows) and all(source_rows[k]['original_path']==v['path'] and
         source_rows[k]['source_sha256']==v['sha256'] for k,v in inputs.items()), 'Exact archived evidence roles/bindings')
    need(plan['schema']=='after216-five-target-additive-original-evidence-input-plan-v3' and plan['package_path']==PACKAGE and
         plan['measured_counts']==m['measured_counts']==counts and plan['inherited_archive']==m['inherited_archive']==
         {'path':BASE,'archive_manifest_sha256':BASE_MANIFEST_SHA,'source_plan_sha256':BASE_PLAN_SHA,'counts':BASE_COUNTS}, 'Plan/counts/inherited pins')
    scope(m)
    need(plan['scope']==SCOPE and plan['targets']=={m:source_rows['target_source.'+m]['source_sha256'] for m in TARGETS}, 'Plan source/scope bindings')
    sources = m['publication_source_sha256']
    need(sources=={mod.replace('.','/')+'.lean':plan['targets'][mod] for mod in TARGETS}, 'Exact five published source paths')
    for path, digest in sources.items():
        need(sha(member(root,path).read_bytes())==digest, 'Published source raw bytes')
    saved_census = json.loads(load(plan['refs']['current_census']))
    for mod, entry in saved_census['modules'].items():
        need(sha(member(root,mod.replace('.','/')+'.lean').read_bytes())==entry['source_sha256'], 'Accepted221 source bytes: '+mod)
    required = [m.replace('.','/')+'.lean -text' for m in TARGETS]+[PACKAGE+'/** -text']
    need(member(package,'root-gitattributes-required.raw').read_bytes()==('\n'.join(required)+'\n').encode(), 'Exact root attributes rules')
    attrs = member(root,'.gitattributes').read_bytes().splitlines()
    need(all(attrs.count(line.encode())==1 for line in required), 'Root attributes exact additions')
    rawstage = member(package,'stage-paths.nul').read_bytes()
    need(rawstage.endswith(b'\0'), 'NUL stage terminator')
    stage = [p.decode('utf-8') for p in rawstage.split(b'\0')[:-1]]
    expected = sorted({'.gitattributes',*sources,*(PACKAGE+'/'+p for p in declared|{'archive-manifest.json'})})
    need(stage==expected and m['stage_path_count']==len(stage), 'Exact sorted unique stage scope/count')
    print('PASS: archived original bytes and complete ROOT/peer/protocol/witness/intake/four-audit/five-source bindings; actual216 deep equality; derived counts; stage scope; OPEN30')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description='Read-only clone verification; no .lake access')
    ap.add_argument('--root',required=True)
    clone_main(Path(ap.parse_args().root).resolve())
