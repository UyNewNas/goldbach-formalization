from pathlib import Path
import ast
import base64
import difflib
import hashlib
import json

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/p24-recursion-repairs-20261126/scope-candidates/p2-encloser-array-natrec-03.sh')
raw = BASE.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'aa253c97ccd7bd0f7da3b2c287e4d48ffcfa52a5b88910116b170e47684e4708'
shell = raw.decode()
prefix, body = shell.split("python3 -B - <<'P24_SCOPE_NATREC_PY'\n", 1)
body, suffix = body.rsplit('\nP24_SCOPE_NATREC_PY', 1)
original_body = body
candidate = (HERE / 'P2HistoricLogPointInterpreter-contains-change-01.lean').read_bytes()
assert hashlib.sha256(candidate).hexdigest() == 'ec8550365f6f47c8354c9b31d9c156a7f82280335a72abc6c70b024414fded58'
target = 'P24ContainsEquationRepair20261126.Attempt001.LogPoint'
spec = {
    'label': 'LogPoint',
    'target': target,
    'original_module': 'ImbalancedChen.P2HistoricLogPointInterpreter',
    'original_sha256': '07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552',
    'candidate_sha256': hashlib.sha256(candidate).hexdigest(),
    'candidate_base64': base64.b64encode(candidate).decode(),
}

def replace(old, new):
    global body
    assert body.count(old) == 1, old[:150]
    body = body.replace(old, new, 1)

replace("OUT=Path('/workspace/P24RecursionRepairs20261126/ScopeAttempt003')",
        "OUT=Path('/workspace/P24ContainsEquationRepair20261126/Attempt001')")
replace("PIN='6e616f4e0372555f7a78bcdba3e198d0e277eec8'",
        "PIN='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'")
spec_line = next(line for line in body.splitlines() if line.startswith('SPECS='))
replace(spec_line, 'SPECS=' + repr([spec]) + "\nDUPLICATE_NAME='ImbalancedChen.Certificates.P2HistoricQ80DefectLookup.I80.Contains.eq_1'")
replace("require(os.statvfs(ROOT).f_bavail*os.statvfs(ROOT).f_frsize>=16*1024*1024,'Insufficient free disk for isolated small artifacts')",
        "require(os.statvfs(ROOT).f_bavail*os.statvfs(ROOT).f_frsize>=64*1024*1024,'Insufficient free disk for isolated small artifacts plus the unchanged 32 MiB reserve')")
replace("registry=ROOT/'.lake/p2-private/records.json';registry_before=digest(registry)",
        "registry=ROOT/'.lake/p2-private/records.json';registry_before=digest(registry)\n"
        "AUDIT_MODULES=['ImbalancedChen.P2HistoricLogPointInterpreter','ImbalancedChen.P2HistoricSieveTableSemantics']\n"
        "def original_audit_files():\n"
        " result={}\n"
        " for module in AUDIT_MODULES:\n"
        "  directory=ROOT/'.lake/p2-private/audit'/module\n"
        "  require(directory.is_dir(),'Missing original selected-owner audit directory '+module)\n"
        "  for p in sorted(directory.rglob('*')):\n"
        "   if p.is_file():result[str(p.relative_to(ROOT))]={'bytes':p.stat().st_size,'sha256':digest(p)}\n"
        " return result\n"
        "audit_files_before=original_audit_files()")
replace("'finite_A_credit':False,'finite_B_credit':False,", "'finite_A_credit':False,'finite_B_credit':False,'original_selected_owner_audit_files_before':audit_files_before,'scope':'Only isolated LogPoint contains_iff proof; compile/replay/original full-owned and actual duplicate-name absence; no source promotion',")
replace("'candidate_sha256','equations_sha256','frozen_project_imports'", "'candidate_sha256','frozen_project_imports'")
replace("  equations=base64.b64decode(s['equations_base64'],validate=True);require(hashlib.sha256(equations).hexdigest()==s['equations_sha256'],'Equations bytes mismatch')\n  eqfile=OUT/(s['label']+'Equations.lean');eqfile.write_bytes(equations)\n", '')
replace("   stage(row,'equations',[LEAN,*FLAGS,str(eqfile)])\n", '')
replace("   row['owned_count']=parsed['declaration_count'];row['axiom_counts']=parsed['axiom_counts']",
        "   row['owned_count']=parsed['declaration_count'];row['axiom_counts']=parsed['axiom_counts']\n"
        "   inventories=parsed['inventory']\n"
        "   row['duplicate_name']=DUPLICATE_NAME\n"
        "   row['duplicate_name_absent_from_all_owned_records']=all(DUPLICATE_NAME not in inventories[key] for key in ('serialized','environment')) and all(d['name']!=DUPLICATE_NAME for d in parsed['declarations'])\n"
        "   require(row['duplicate_name_absent_from_all_owned_records'],'Original duplicate equation is still owned by the isolated candidate')")
replace("  finally:\n   require(source.read_bytes()==data and eqfile.read_bytes()==equations and auditfile.read_bytes()==auditbytes,'Isolated input changed')",
        "  finally:\n   require(source.read_bytes()==data and auditfile.read_bytes()==auditbytes,'Isolated input changed')")
replace("   write_json(OUT/(s['label']+'-owned.json'),parsed)",
        "   write_json(OUT/(s['label']+'-owned.json'),parsed)\n"
        "   with (OUT/(s['label']+'-types.txt')).open('x') as f:\n"
        "    f.write('\\n\\n'.join(d['name']+'\\n'+d['type'] for d in parsed['declarations'])+'\\n')")
assert body.count('isolated_compile_equations_replay_original_owned_passed') == 3
body = body.replace('isolated_compile_equations_replay_original_owned_passed', 'isolated_compile_replay_original_owned_and_duplicate_absence_passed')
replace("  require(native_after==native_before,'Qualified native environment changed')",
        "  require(native_after==native_before,'Qualified native environment changed')\n"
        "  audit_files_after=original_audit_files();receipt['original_selected_owner_audit_files_after']=audit_files_after\n"
        "  require(audit_files_after==audit_files_before,'Original selected-owner audit artifacts changed')\n"
        "  require(os.statvfs(ROOT).f_bavail*os.statvfs(ROOT).f_frsize>=32*1024*1024,'Persistent 32 MiB reserve breached')")
replace("'phase':'isolated_recursion_candidate_diagnostic_complete'", "'phase':'isolated_contains_equation_repair_diagnostic_complete'")
body = body.replace('import base64,hashlib,json,os,subprocess,sys,time', 'import base64,hashlib,json,os,subprocess,sys,time,traceback')
replace("receipt['execution_error']=type(e).__name__+': '+str(e)", "receipt['execution_error']=type(e).__name__+': '+str(e);receipt['execution_traceback']=traceback.format_exc()")
replace("row['error']=type(e).__name__+': '+str(e);", "row['error']=type(e).__name__+': '+str(e);row['traceback']=traceback.format_exc();")
ast.parse(body)
script = prefix.replace('P24_SCOPE_NATREC_PY', 'P24_CONTAINS_REPAIR_PY') + "python3 -B - <<'P24_CONTAINS_REPAIR_PY'\n" + body + '\nP24_CONTAINS_REPAIR_PY' + suffix
(HERE / 'p2-logpoint-contains-change-01.sh').write_text(script)
(HERE / 'p2-logpoint-contains-change-01.py').write_text(body + '\n')
patch = ''.join(difflib.unified_diff(original_body.splitlines(True), body.splitlines(True), fromfile=str(BASE), tofile='p2-logpoint-contains-change-01.py'))
(HERE / 'scope-natrec-to-contains-wrapper.patch').write_text(patch)
names_before = {n.name:ast.get_source_segment(original_body,n) for n in ast.walk(ast.parse(original_body)) if isinstance(n,ast.FunctionDef)}
names_after = {n.name:ast.get_source_segment(body,n) for n in ast.walk(ast.parse(body)) if isinstance(n,ast.FunctionDef)}
assert all(names_before[k] == names_after[k] for k in names_before)
manifest = {
    'source_pin': 'b55fa93d39e6a4ddf2abd37b9b8481078e329f70',
    'base_actual_wrapper': {'path': str(BASE), 'sha256': hashlib.sha256(raw).hexdigest()},
    'existing_python_functions_byte_identical': sorted(names_before),
    'new_python_functions': sorted(set(names_after)-set(names_before)),
    'candidate': {k:v for k,v in spec.items() if k!='candidate_base64'},
    'remote_output': '/workspace/P24ContainsEquationRepair20261126/Attempt001',
    'target_module_raw_and_lean': target,
    'outer_resources': {'timeout_seconds': 900, 'memory_mb': 13107, 'cpu_threads': 1},
    'child_timeout_seconds_each':300,
    'flags_unchanged': ['-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000'],
    'original_template_sha256':'2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'original_parse_audit_sha256':'571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'diagnostic_only':True,
    'executed':False,
    'canonical_credit':False,
    'files':{}
}
for n in ['P2HistoricLogPointInterpreter-contains-change-01.lean','contains-change-01.patch','exact-proof-replacement.json','p2-logpoint-contains-change-01.sh','p2-logpoint-contains-change-01.py','scope-natrec-to-contains-wrapper.patch']:
    b=(HERE/n).read_bytes();manifest['files'][n]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(HERE/'isolated-diagnostic-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(manifest,ensure_ascii=False))
