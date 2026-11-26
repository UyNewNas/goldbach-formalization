import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
base_path = HERE / 'p2-B-raw-defeq-b55-draft01.py'
base = base_path.read_text()
assert hashlib.sha256(base.encode()).hexdigest() == '0f02f259c1ee1432ce7c8b8191f315109cdf8aa14097880fb6f18b8ca18752a4'
source = (HERE/'P24CachedEndpointWhnfDiagnostic.lean').read_bytes()
assert len(source) == 3744
assert hashlib.sha256(source).hexdigest() == 'befc8ca245300f6692f26020f107c6f27895f3fdde5e25a9f60065648f100d20'
tree = ast.parse(base)
assignment = next(n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='DIAGNOSTIC_SOURCE' for t in n.targets))
old_assignment = ast.get_source_segment(base, assignment)
script = base.replace(old_assignment, 'DIAGNOSTIC_SOURCE = '+repr(source.decode()), 1)
script = script.replace('2eb7dc403ee25098cfe711ab887d3988fe6c87a8872cca758d49ed36dd06cf4e',
                        'befc8ca245300f6692f26020f107c6f27895f3fdde5e25a9f60065648f100d20')
replacements = {
    '.lake/p24-B-raw-defeq/b55-attempt-001':'.lake/p24-B-whnf/b55-attempt-001',
    'RawDefEq.lean':'WhnfDiagnostic.lean',
    'B_raw_defeq_capture_progress':'B_whnf_capture_progress',
    'raw-defeq.stdout.log.gz':'whnf.stdout.log.gz',
    'raw-defeq-diagnostic.json':'whnf-diagnostic.json',
    'P24_B_RAW_DEFEQ_BEGIN':'P24_B_WHNF_DIAGNOSTIC_BEGIN',
    'P24_B_RAW_DEFEQ_DONE':'P24_B_WHNF_DIAGNOSTIC_DONE',
    'complete_raw_precheck_observation':'complete_whnf_observation',
    'raw_precheck_capture_or_parse':'whnf_capture_or_parse',
    'Report one original B raw Meta isDefEq result or exception, without isDefEqGuarded':
      'Report one default-transparency Meta WHNF of the unchanged original B Bool target',
}
for old,new in replacements.items():
    assert old in script, old
    script = script.replace(old,new)
anchor = 'original_audit_before = audit_directory_fingerprint()\n'
assert script.count(anchor)==1
prior = '''prior_receipt_path = root / ".lake/p24-B-raw-defeq/b55-attempt-001/raw-defeq-diagnostic.json"
prior_receipt_sha256 = "79df14cf3f564c25fbfd444e7091cbee772212f2687eceb6774c658223bd329a"
assert prior_receipt_path.is_file() and not prior_receipt_path.is_symlink()
assert digest(prior_receipt_path) == prior_receipt_sha256
prior = json.loads(prior_receipt_path.read_text())
assert prior["source_pin"] == pin and prior["target"] == B
assert prior["complete_raw_precheck_observation"] is True
assert prior["diagnostic_preservation_checks_passed"] is True and prior["wrapper_exit_code"] == 0
assert prior["postchecks"] and all(value is True for value in prior["postchecks"].values())
assert not prior["errors"] and prior["registry_before"] == prior["registry_after"] == registry_before
assert prior["pinned_file_sha256"] == expected and prior["runtime_sha256"] == runtime_expected
assert prior["native_binding"] == native_before
assert prior["observations"][-1]["phase"] == "returned" and prior["observations"][-1]["isDefEq"] is False
prior_receipt_binding = {"path":str(prior_receipt_path), "bytes":prior_receipt_path.stat().st_size,
    "sha256":prior_receipt_sha256}
'''
script=script.replace(anchor,anchor+prior,1)
anchor='    "diagnostic_source":source_binding, "command":command, "lean_path":environment.get("LEAN_PATH", ""),\n'
assert script.count(anchor)==1
script=script.replace(anchor,anchor+'    "prior_actual_raw_false_receipt":prior_receipt_binding, "isDefEq_called":False, "whnf_calls":1,\n',1)
begin=script.index('    with gzip.open(gzip_path, "rt") as stream:\n')
end=script.index('    complete_observation = True\n',begin)
parse='''    with gzip.open(gzip_path, "rt") as stream:
        for line in stream:
            if line.startswith("P24_B_WHNF "):
                observations.append(json.loads(line[len("P24_B_WHNF "):]))
    assert len(observations) in (2,3)
    begin = observations[0]
    assert begin["phase"] == "begin" and begin["default_transparency"] is True
    assert begin["maxRecDepth_option"] == 0 and begin["effective_maxRecDepth"] == 0
    assert begin["maxHeartbeats_option"] == 0
    assert all(row["original_B_compile_credit"] is False for row in observations)
    outcome = observations[-1]
    assert outcome["kernel_replay_credit"] is False and outcome["owned_audit_credit"] is False
    if outcome["phase"] == "complete":
        assert len(observations) == 3 and capture["lean_exit_code"] == 0
        head = observations[1]
        assert head["phase"] == "whnf_returned" and isinstance(head["head"],dict)
        assert isinstance(head["is_Bool_true"],bool) and isinstance(head["is_Bool_false"],bool)
        assert not (head["is_Bool_true"] and head["is_Bool_false"])
        assert isinstance(head["direct_argument_heads"],list)
        assert isinstance(outcome["pretty_default_options"],str)
        assert isinstance(outcome["pretty_contains_ellipsis"],bool)
    else:
        assert outcome["phase"] == "exception" and outcome["kind"] in ("error","internal")
        assert isinstance(outcome["message"],str)
        assert isinstance(capture["lean_exit_code"],int) and capture["lean_exit_code"] != 0
        if len(observations) == 3:
            assert observations[1]["phase"] == "whnf_returned"
'''
script=script[:begin]+parse+script[end:]
anchor='def check_derived_inputs_after():\n'
assert script.count(anchor)==1
script=script.replace(anchor,anchor+'    assert digest(prior_receipt_path) == prior_receipt_sha256\n',1)
ast.parse(script)
compile(script, 'prepared-whnf-diagnostic', 'exec')
py=HERE/'p2-B-whnf-b55-draft01.py'
py.write_text(script)
shell='''#!/usr/bin/env bash
# Prepared read-only B WHNF diagnostic; no original B/replay/audit credit.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_B_WHNF_DIAGNOSTIC'
'''+script+'\nP24_B_WHNF_DIAGNOSTIC\n'
sh=HERE/'p2-B-whnf-b55-draft01.sh'
sh.write_text(shell)
newtree=ast.parse(script)
unchanged=[]
deltas=[]
for node in tree.body:
    if isinstance(node,ast.FunctionDef):
        newer=next(n for n in newtree.body if isinstance(n,ast.FunctionDef) and n.name==node.name)
        if ast.get_source_segment(base,node)==ast.get_source_segment(script,newer):
            unchanged.append(node.name)
        else:deltas.append(node.name)
assert set(deltas)=={'capture_complete_stdout','check_derived_inputs_after'}
manifest={'schema':1,'prepared_only':True,'executed':False,'original_definitions_options_and_numbers_unchanged':True,
    'prior_actual_raw_false_task':'c2a5bb582a5c4830a408ad9ca5b06f3c',
    'prior_actual_receipt_sha256':'79df14cf3f564c25fbfd444e7091cbee772212f2687eceb6774c658223bd329a',
    'base_wrapper_python_sha256':hashlib.sha256(base.encode()).hexdigest(),
    'unchanged_top_level_functions':unchanged,
    'changed_functions':{'capture_complete_stdout':'progress label only','check_derived_inputs_after':'add prior exact receipt SHA protection'},
    'single_whnf_no_isDefEq_retry':True,'canonical_credit':False,'files':{}}
for path in [HERE/'P24CachedEndpointWhnfDiagnostic.lean',py,sh,Path(__file__)]:
    b=path.read_bytes();manifest['files'][path.name]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(HERE/'whnf-wrapper-draft01-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
for path in [py,sh,HERE/'whnf-wrapper-draft01-manifest.json']:
    b=path.read_bytes();print(path.name,len(b),hashlib.sha256(b).hexdigest())
