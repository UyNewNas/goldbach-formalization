from pathlib import Path
import ast,difflib,hashlib,json,subprocess
out=Path('/tmp/p24-integration-repairs-20261126/a-canonical-owned')
base_path=Path('/tmp/p24-integration-repairs-20261126/p2-canonical-owned-eleven-b55-draft02.py')
base=base_path.read_text(); s=base

def replace_once(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a))
 s=s.replace(a,b)

replace_once('# The owner requires the original strict321 gate to pass at this eleven-source commit.', '# The original strict321 and current finite A compile records must be valid at b55.')
replace_once(']\nfull_nodes = project_nodes(root, W)', '    A,\n]\nfull_nodes = project_nodes(root, W)')
replace_once('assert len(prereq_nodes) == 321','assert len(prereq_nodes) == 322')
replace_once('assert set(full) - set(prereq_nodes) == {A, B, W}', 'assert set(full) - set(prereq_nodes) == {B, W}')
replace_once('assert A not in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes', 'assert A in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes')
a=s.index('requested_targets = ['); b=s.index('\ndef run_gate',a)
s=s[:a]+'requested_targets = [A]\nrepaired_source_paths = ["ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean"]\n\n'+(out/'capacity-binding-draft01.py').read_text()+s[b:]
replace_once('# No receipt selector or exporter package is run: these eleven changed sources\n# are explicitly selected for the original complete owned-declaration audit.', '# No selector/exporter package is run. Only canonical A is passed to the unchanged\n# original replay/full-owned CLI. The capacity diagnostic supplies no audit credit.')
s=s.replace('canonical_owned_eleven','canonical_owned_A').replace('CANONICAL_OWNED_ELEVEN','CANONICAL_OWNED_A')
replace_once('summary_name = "p24-owned-b55-eleven-repairs-001.json"','summary_name = "p24-owned-b55-canonical-A-001.json"')
replace_once('out = Path("/workspace/p24-eleven-source-canonical-owned-20261126/attempt-001")','out = Path("/workspace/p24-canonical-A-original-owned-20261126/attempt-001")')
replace_once('assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 256 * 1024 * 1024','assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= minimum_free_reserve + 8 * 1024 * 1024')
replace_once('assert len(requested_targets) == len(set(requested_targets)) == 11','assert len(requested_targets) == len(set(requested_targets)) == 1')
replace_once('assert len(targets) == 11 and set(targets) == set(requested_targets)','assert targets == [A] and len(targets) == 1')
replace_once('assert not set(targets).intersection({A, B, W})','assert set(targets).isdisjoint({B, W})')
s=s.replace('"prerequisite_scope": 321','"prerequisite_scope": 322')
replace_once('"requested": 11,','"requested": 1,')
replace_once('collect_postchecks(pre_summary, pre_rc, roots, 321, 0)','collect_postchecks(pre_summary, pre_rc, roots, 322, 0)')
s=s.replace('binds_current_321','binds_current_322').replace('still_binds_current_321','still_binds_current_322')
replace_once('    pre_perform("original_verify_compilation_binds_current_322", bind_current_prerequisites)','    pre_perform("original_verify_compilation_binds_current_322", bind_current_prerequisites)\n    if not pre_errors:\n        pre_perform("actual_capacity_binding_and_original_plaintext_space_guard", bind_capacity_and_check_original_audit_space)')
replace_once('Original zero-budget strict321 gate or current compilation binding failed','Original zero-budget 322 gate, current compilation binding, or measured space guard failed')
replace_once('assert original_summary["requested"] == len(targets) == 11','assert original_summary["requested"] == len(targets) == 1')
replace_once('write_evidence("original-artifact-index.json", captured_modules)\npassed =', '''write_evidence("original-artifact-index.json", captured_modules)
if audit_rc == 0 and not errors:
    perform("original_full_plaintext_artifacts_exactly_match_actual_capacity", verify_original_plaintext_sizes)

def check_capacity_reference_and_free_reserve():
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    disk = os.statvfs(root)
    assert disk.f_bavail * disk.f_frsize >= minimum_free_reserve

perform("capacity_reference_unchanged_and_32MiB_reserve_preserved", check_capacity_reference_and_free_reserve)
passed =''')
s=s.replace('"A_credit": False','"A_owned_audit_credit": False')
replace_once('    "canonical_owned_A_passed": passed,\n    "original_summary_file"', '    "canonical_owned_A_passed": passed,\n    "capacity_binding": capacity_binding,\n    "independent_replay_and_original_full_owned_CLI_preserved": True,\n    "capacity_diagnostic_credit_transferred": False,\n    "separate_shape_checker_credit_transferred": False,\n    "shape_checker_run": False,\n    "all_original_plaintext_artifacts_retained": True,\n    "original_summary_file"')
# Only the final two records grant this original owned-audit component on success.
marker='    "A_owned_audit_credit": False, "B_credit": False, "W_credit": False, "full324_credit": False,'
assert s.count(marker)==2
positions=[];off=0
while (x:=s.find(marker,off))!=-1: positions.append(x);off=x+len(marker)
for x in reversed(positions[-2:]): s=s[:x]+s[x:].replace('"A_owned_audit_credit": False','"A_owned_audit_credit": passed',1)
py=out/'p2-canonical-A-original-owned-b55-draft01.py'; sh=out/'p2-canonical-A-original-owned-b55-draft01.sh'
assert not py.exists() and not sh.exists();py.write_text(s)
header='''#!/usr/bin/env bash
# Local prepared draft only; submit only after independent review and available space.
# Original CLI full replay/audit artifacts remain plaintext at their original paths.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_CANONICAL_OWNED_A'
'''
sh.write_text(header+s+'P24_CANONICAL_OWNED_A\n')
ast.parse(s);compile(s,str(py),'exec');subprocess.run(['bash','-n',str(sh)],check=True)
patch=out/'owned11-gzip-to-canonical-A-original-audit-draft01.patch';patch.write_text(''.join(difflib.unified_diff(base.splitlines(keepends=True),s.splitlines(keepends=True),fromfile=str(base_path),tofile=str(py))))
def funcs(text):
 return {n.name:ast.get_source_segment(text,n) for n in ast.walk(ast.parse(text)) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
bf,cf=funcs(base),funcs(s)
unchanged=[n for n,v in bf.items() if cf.get(n)==v];changed=[n for n,v in bf.items() if cf.get(n)!=v]
info=lambda p:{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
m={'status':'LOCAL_PREPARED_NOT_SUBMITTED','source_pin':'b55fa93d39e6a4ddf2abd37b9b8481078e329f70','base':info(base_path),'python':info(py),'shell':info(sh),'patch':info(patch),'capacity_helper':info(out/'capacity-binding-draft01.py'),'original_functions_byte_identical':unchanged,'original_functions_changed':changed,'changes':'Original target eleven repairs to A alone; zero-budget322 includes A; actual bound capacity and space guard before original CLI; complete plaintext size/SHA postcheck. No original tool/template/resources modified. Shape check independently bound, not substituted.','local_validation':{'python_ast':True,'python_compile_only':True,'bash_n':True,'remote_execution':False},'raw_three_file_actual_bytes':485251971,'capacity_receipt_sha256':'47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9','minimum_free_reserve_bytes':33554432,'publication_or_credit':False}
f=out/'canonical-A-original-audit-draft01-manifest.json';f.write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'python':info(py),'shell':info(sh),'manifest':info(f),'original_functions_changed':changed,'unchanged_function_count':len(unchanged)},ensure_ascii=False))
