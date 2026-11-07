#!/usr/bin/env python3
"""Read-only P0 receipt reception; this program never starts Lean, Lake, or CI."""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import base64, gzip, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parent
REPO = Path('/workspace/scratch/535d89efd063/goldbach-formalization')
FIXED = '7b1283e4a70874e4fb7004bafad0793069bdea71'
OLD = 'bf54caeb5e708474cacefac13a171d307b4c64f2'
BASE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
P0 = '28fd630ef7cc38eba86beb6c0ba123336b5d05f2'
PREFIX = 'verification/parts/p5/round4/s1lowerrosser'
B = ROOT / 'fixed-source' / PREFIX
TARGET = 'MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser'
SOURCE = 'c07c0704c975bef4d772090ce03d7536f28edd319c700c4d9feb27c9f111ef62'
OBJECT = '005d9ac78bbd5e65386511bd975758f4fa8ed955e327c794569ab4a538be4988'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
checks = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read(name):
    return json.loads((B / name).read_text())

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def check(name, condition, detail=None):
    checks.append({'name': name, 'passed': bool(condition), 'detail': detail})

manifest = json.loads((ROOT / 'EXTRACTION_MANIFEST.json').read_text())
receipt = read('receipt.json')
commands = read('commands-and-results.json')
pre = read('preflight.json')
decls = read('declarations.json')
public = read('public-theorem-types.json')

check('fixed_commit_parent', git('rev-parse', FIXED+'^').decode().strip() == OLD)
check('173_new_evidence_files_no_production_change', manifest['changed_files'] == 173 and not manifest['production_source_changes'])
file_checks = []
for item in manifest['files']:
    data = (ROOT/'fixed-source'/item['path']).read_bytes()
    exact = git('show', FIXED+':'+item['path'])
    file_checks.append(data == exact and sha(data) == item['sha256'])
check('all_extracted_files_equal_fixed_git_blobs', all(file_checks), {'count': len(file_checks)})
check('proof_source_snapshot_matches_declared_sha', sha((B/'source/upstream-LiLiuGoldbachS1LowerRosser.lean.txt').read_bytes()) == SOURCE)
check('proof_source_contains_no_forbidden_token', re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', (B/'source/upstream-LiLiuGoldbachS1LowerRosser.lean.txt').read_text()) is None)

upstream_checks = []
expected = {x['module'].split('.')[-1]: x['source']['sha256'] for x in read('context.json')['supplier_graph']}
for name in ['LiLiuGoldbachS1LowerRosser','LiLiuGoldbachS1Carrier','LiLiuGoldbachS1MainMass','LiLiuGoldbachS1BetaPaidLower']:
    body = (ROOT/'upstream-api'/(name+'.lean')).read_bytes()
    record = json.loads((ROOT/'upstream-api'/(name+'.response.json')).read_text())
    ok = sha(body) == expected[name] and 'ref=09b97db5764ade1246bfb77206baa1b124760958' in record['url']
    upstream_checks.append({'module': name, 'sha256': sha(body), 'matches': ok, 'url': record['url']})
check('independent_fixed_upstream_source_matches', all(x['matches'] for x in upstream_checks), upstream_checks)

pin_files = ['lean-toolchain','lakefile.toml','lake-manifest.json']
check('pin_files_equal_common_and_current_integration', all(git('show',FIXED+':'+p) == git('show',BASE+':'+p) == git('show',P0+':'+p) for p in pin_files))
pins = {x['name']:x['rev'] for x in json.loads(git('show',FIXED+':lake-manifest.json'))['packages']}
check('all_11_dependency_pins_match_receipt', len(pins) == 11 and {x['package']:x['revision'] for x in receipt['dependencies']} == pins and all(x['tracked_changes']==[] for x in receipt['dependencies']))
check('protected_source_identity', all(sha(git('show',FIXED+':'+x['path'])) == x['sha256'] and git('show',FIXED+':'+x['path']) == git('show',BASE+':'+x['path']) for x in receipt['protected_files']))

archive = read('objects/manifest.json')
transport = (B/archive['path']).read_bytes()
compressed = base64.b64decode(transport)
decoded = gzip.decompress(compressed)
check('object_transport_three_hashes', sha(transport)==archive['transport_sha256'] and sha(compressed)==archive['gzip_sha256'] and sha(decoded)==archive['decoded_object_sha256']==OBJECT and len(decoded)==archive['decoded_object_bytes']==145336)
(ROOT/'decoded-objects').mkdir(exist_ok=True)
(ROOT/'decoded-objects/LiLiuGoldbachS1LowerRosser.olean').write_bytes(decoded)

gate_rows=[]
for idx,c in enumerate(commands):
    log = B/'raw'/Path(c['log']).name
    data = log.read_bytes()
    lines = data.decode().splitlines()
    header = json.loads(lines[0])
    header_exact = all(c[k] == v for k,v in header.items())
    same = c['source_sha256_before']==c['source_sha256_after'] and c['imports_before']==c['imports_after']
    elapsed = (datetime.fromisoformat(c['completed_utc'])-datetime.fromisoformat(c['started_utc'])).total_seconds()
    check('raw_command_'+str(idx)+'_binding', sha(data)==c['raw_log_sha256'] and header_exact and same and c['source_unchanged'] and c['imports_unchanged'] and c['guards_unchanged'] and abs(elapsed-c['elapsed_seconds'])<0.02)
    if c['action']=='replay':
        check('stock_checker_target_actual_log', c['command'][1:]==['--verbose',TARGET] and 'replaying '+TARGET in lines and c['returncode']==0)
    elif c['returncode']==0:
        check('strict_frontend_'+str(idx), c['trustLevel']==0 and c['warningAsError'] is True and c['metadata_adapter'] is False and 'FRONTEND_OK module='+c['module']+' trustLevel=0' in lines)
    gate_rows.append({k:c[k] for k in ['action','module','returncode','elapsed_seconds','started_utc','completed_utc','raw_log_sha256']})
check('gate_counts', [x['returncode'] for x in commands] == [0,0,1,0] and [x['action'] for x in commands] == ['compile','replay','audit','audit'])
compile, replay, failed_audit, audit = commands
check('compile_replay_audit_same_target_object', compile['objects_after']==replay['objects_before']==replay['objects_after']==audit['imports_before'][0]['objects']==audit['imports_after'][0]['objects'] and compile['objects_after'][0]['sha256']==OBJECT)
check('source_binding_all_successful_stages', compile['source_sha256_before']==replay['source_sha256_before']==audit['imports_before'][0]['source']['sha256']==SOURCE)
check('final_preflight_actual_digest', sha((B/'preflight.json').read_bytes())==audit['preflight_sha256'])
check('audit_source_binding', sha((ROOT/'fixed-source/verification/parts/p5/S1LowerRosserAudit.lean').read_bytes())==audit['source_sha256_before']==receipt['audit']['source_sha256'])
check('no_stale_success_for_failed_audit', failed_audit['returncode']==1 and failed_audit['source_sha256_before']==sha((B/'source/S1LowerRosserAudit.before-options-fix.lean.txt').read_bytes()) and failed_audit['source_sha256_before']!=audit['source_sha256_before'])
check('receipt_gate_entries_match_original_records', all(receipt['gates'][c['action']]['returncode']==c['returncode'] and receipt['gates'][c['action']]['elapsed_seconds']==c['elapsed_seconds'] and receipt['gates'][c['action']]['log_sha256']==c['raw_log_sha256'] for c in [compile,replay,audit]))

audit_lines=(B/'raw'/Path(audit['log']).name).read_text().splitlines()
marker='CHEN_P5_S1LOWERROSSER_AUDIT_DECL '
raw_decls=[json.loads(l[len(marker):]) for l in audit_lines if l.startswith(marker)]
byname=lambda seq:{x['name']:x for x in seq}
check('all_declarations_equal_original_compiler_log', len(raw_decls)==len(decls)==8 and byname(raw_decls)==byname(decls))
check('actual_complete_inventory_footer', 'CHEN_P5_S1LOWERROSSER_AUDIT_COUNT 8' in audit_lines)
check('full_owned_axiom_audit', all(not d['is_axiom'] and not d['is_unsafe'] and set(d['axioms'])<=ALLOW for d in decls) and set().union(*(set(d['axioms']) for d in decls))==ALLOW and Counter(d['kind'] for d in decls)=={'theorem':7,'definition':1})
check('public_types_are_actual_same_run_records', len(public)==2 and all(d==byname(decls)[d['name']] for d in public))
type_formats=[]
for d in decls:
    elided=lambda s:any(t in s for t in ['⋯','...','<truncated>','<max recursion depth>'])
    type_formats.append({'name':d['name'],'readable_elided':elided(d['type']),'explicit_elided':elided(d['type_explicit']),'expr_repr_elided':elided(d['type_expr_repr']),'actual_format':'PP_EXPLICIT_UNIVERSES_FULLNAMES_PROOFS_AND_RAW_EXPR_NOT_PP_ALL'})
check('all_8_explicit_and_raw_types_unelided', all(not x['explicit_elided'] and not x['expr_repr_elided'] for x in type_formats))

previous = json.loads((ROOT/'context/verification/parts/p5/round3/s1carrier/receipt.json').read_text())
check('accepted_carrier_source_object_reused', previous['source_sha256']==pre['reused_S1Carrier']['source']['sha256']==receipt['direct_imports'][0]['source']['sha256'] and previous['compiled_objects']==pre['reused_S1Carrier']['objects']==receipt['direct_imports'][0]['objects'])
prior_refs=[]
def walk(obj):
    if isinstance(obj,dict):
        if set(['path','commit','sha256']) <= set(obj):
            prior_refs.append(obj)
        for v in obj.values():walk(v)
    elif isinstance(obj,list):
        for v in obj:walk(v)
walk(pre);walk(receipt['reuse'])
seen={}
for r in prior_refs:
    seen[(r['commit'],r['path'])]=r
check('all_reused_fixed_log_and_receipt_references', all(sha(git('show',r['commit']+':'+r['path']))==r['sha256'] for r in seen.values()), {'unique_count':len(seen)})
check('final_preflight_closure_accounting', pre['direct_import_closure_source_modules']==8776 and len(pre['local_compiled_imports_rechecked'])==96 and pre['official_cache_source_module_count']==8679 and pre['missing_import_objects']==[])
restored=[json.loads(l) for l in (B/'restoration/results.jsonl').read_text().splitlines() if l.strip()]
check('restored_objects_exact_producer_bindings',len(restored)==62 and all(x['historical_object_sha256_reproduced'] and x['source_unchanged'] and x['imports_unchanged'] and x['guards_unchanged'] for x in restored))

runtime=[]
for name,x in receipt['toolchain']['binaries'].items():
    p=Path(x['path']); present=p.is_file(); actual=sha(p.read_bytes()) if present else None
    runtime.append({'tool':name,'path':str(p),'present':present,'sha256':actual,'matches':actual==x['sha256']})
check('current_surviving_runtime_binaries_match',all(x['matches'] for x in runtime))
driver=(B/'runtime/frontend-driver.lakefile.lean.txt').read_bytes()
prior_pre=json.loads((ROOT/'context/verification/parts/p5/round3/s1carrier/preflight.json').read_text())
check('frontend_driver_unchanged_from_accepted_carrier',sha(driver)==pre['guards']['frontend_driver_sha256']==prior_pre['guards']['frontend_driver_sha256'])
result={'status':'PASS_REUSED_FIXED_PRODUCER_GATES' if all(x['passed'] for x in checks) else 'FAIL_INTAKE_CONSISTENCY',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'fixed_commit':FIXED,'tree':manifest['tree'],'parent':OLD,'integration_baseline':P0,
 'scope':'New independent acceptance of existing pinned dependency S1LowerRosser; no new ImbalancedChen production source; no P0 Lean/Lake/CI rerun.',
 'module':TARGET,'source_sha256':SOURCE,'object_sha256':OBJECT,'checks':checks,'gate_records':gate_rows,
 'declaration_count':len(decls),'public_theorem_count':len(public),'type_formats':type_formats,
 'axiom_union':sorted(ALLOW),'current_runtime':runtime,'current_target_original_path_exists':Path(compile['objects_after'][0]['path']).exists(),
 'runtime_note':'The unchanged existing Lake driver enables initializers with unsafe Lean.enableInitializersExecution, then calls official runFrontend at trustLevel=0. No unsafe theorem/definition is accepted; stock checker replay is separately recorded. This is not claimed as a new proof-source unsafe bypass.',
 'preflight_note':receipt['preflight_version_note'],
 'import_replay_scope':'Producer stock replay is target-only over existing imports, without --fresh. Historical closure restoration does not claim fresh whole-closure strict/replay/axiom checks.',
 'receiving_parts':['P5 first-mean supplier chain','P0 integration validation'],
 'remaining_inputs':['AP prefix error payment at normalized scale','S1 beta geometry/main mass/density/main scale and fixed normalized lower acceptance','CurrentChenInitialSource same-object audit binding','CurrentChenInitialMean strict/replay/audit','full eleven-term Chen mean and analytic c/hLower','P1/P2/P3/P4-A actual suppliers; P4-B not needed by P5'],
 'next_target':receipt['next_small_target'],'production_changes':[],
 'actions_note':'No Actions started or retried here; receipt reports older bf54cae parent root CI failure separately. Its aggregate root omits the new target; those runs are not target verification.'}
(ROOT/'P5_FIXED_INTAKE.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
(ROOT/'COMPILER_TYPES_8.json').write_text(json.dumps(decls,ensure_ascii=False,indent=2)+'\n')
(ROOT/'TYPE_FORMATS_8.json').write_text(json.dumps(type_formats,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':result['status'],'checks':len(checks),'failures':[x for x in checks if not x['passed']],'gate_records':gate_rows,'declarations':8,'public':2,'runtime':runtime},ensure_ascii=False,indent=2))
raise SystemExit(0 if all(x['passed'] for x in checks) else 2)
