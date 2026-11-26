from pathlib import Path
import ast,hashlib,json,subprocess
out=Path('/tmp/p24-integration-repairs-20261126/a-canonical-owned')
capacity=Path('/tmp/p24-integration-repairs-20261126/a-capacity-diagnostic/p2-a-owned-capacity-b55-draft01.py')
capacity_tail=Path('/tmp/p24-integration-repairs-20261126/a-capacity-diagnostic/capacity-tail-draft01.py')
prefix=capacity.read_text().split('# Capacity diagnosis only.')[0]
src=capacity_tail.read_text();tree=ast.parse(src)
selected=['available_bytes','need_free','encoded_json','write_derived','audit_directory_fingerprint','stop_only_this_child','capture_complete_stdout','fingerprint_gzip_payload','CompleteGzipAuditText']
source_by_name={n.name:ast.get_source_segment(src,n) for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
helpers='\n\n\n'.join(source_by_name[name] for name in selected)+'\n'
helpers=helpers.replace('"capacity_capture_progress"','"canonical_A_shape_capture_progress"')
shape=(out/'InspectCanonicalABlocks-bindings-draft01.lean').read_text()
assert hashlib.sha256(shape.encode()).hexdigest()=='b54a2c1ae01c1ebfbcb83bb63a9e09f7275ef818eb368e683d615deca1196734'
tail=(out/'canonical-shape-tail-draft01.py').read_text()
assert tail.count('# EXACT_CAPACITY_CAPTURE_HELPERS_INSERTION_POINT')==1
tail=tail.replace('# EXACT_CAPACITY_CAPTURE_HELPERS_INSERTION_POINT',helpers)
s=prefix+'SHAPE_SOURCE = '+repr(shape)+'\n\n'+tail
p=out/'p2-canonical-A-shape-b55-draft01.py';sh=out/'p2-canonical-A-shape-b55-draft01.sh'
assert not p.exists() and not sh.exists();p.write_text(s)
header='''#!/usr/bin/env bash
# Prepared local draft. Canonical A block shape only: no original full-owned/replay credit.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_CANONICAL_A_SHAPE'
'''
sh.write_text(header+s+'P24_CANONICAL_A_SHAPE\n')
ast.parse(s);compile(s,str(p),'exec');subprocess.run(['bash','-n',str(sh)],check=True)
program=ast.parse(s)
constant=next(ast.literal_eval(n.value) for n in program.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='SHAPE_SOURCE' for t in n.targets))
assert constant==shape
new_functions={n.name:ast.get_source_segment(s,n) for n in program.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
unchanged=[n for n in selected if source_by_name[n]==new_functions[n]]
assert unchanged==[n for n in selected if n!='capture_complete_stdout']
assert new_functions['capture_complete_stdout'].replace('"canonical_A_shape_capture_progress"','"capacity_capture_progress"')==source_by_name['capture_complete_stdout']
info=lambda x:{'path':str(x),'bytes':x.stat().st_size,'sha256':hashlib.sha256(x.read_bytes()).hexdigest()}
m={'status':'LOCAL_PREPARED_NOT_SUBMITTED','source_pin':'b55fa93d39e6a4ddf2abd37b9b8481078e329f70','shell':info(sh),'python':info(p),'tail':info(out/'canonical-shape-tail-draft01.py'),'exact_checker':info(out/'InspectCanonicalABlocks-bindings-draft01.lean'),'executed_original_checker_sha256':'c190906df505fbe101f0aca84f46a7ba3252ad75b7ab6bb07ffa2ae3fb950d48','unchanged_shape_core_sha256':'a8db2e02200ea9d21063fbb8e451feebedcb851be3ae53ff7f58c61a313061d3','setup_prefix_exactly_reused_from':info(capacity),'capture_helpers_byte_identical':unchanged,'capture_helper_only_delta':'progress phase label capacity_capture_progress to canonical_A_shape_capture_progress','original_python_shape_checks_preserved':'Same 2048/64/depth6/global131072 checks and each block membership/type-byte/axiom cross-link. Records are the complete unchanged original parser output from actual bound capacity stdout; no canonical audit credit.','input_checks':'All324 source/object/runtime/tools/qualifiednative/registry before-after; original verify_compilation for 321 plus A102; canonical A audit directory unchanged.','output_checks':'Entire stdout gzip read to EOF with raw and compressed bytes/SHA; allblock JSON rows and fullsummary preserved; no original output removed.','resources':{'outer_timeout_seconds':3600,'job_memory_mb':13107,'cpu_threads':1,'lean_memory_mb':11264,'lean_threads':1,'maxRecDepth':50000,'maxHeartbeats':40000000,'minimum_free_bytes':33554432},'local_validation':{'python_AST':True,'python_compile_only':True,'bash_n':True,'embedded_checker_exact':True,'remote_execution':False},'independent_replay_performed':False,'canonical_owned_audit_credit':False,'full324_credit':False}
f=out/'canonical-A-shape-wrapper-draft01-manifest.json';f.write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'shell':info(sh),'python':info(p),'manifest':info(f),'tail':info(out/'canonical-shape-tail-draft01.py')},ensure_ascii=False))
