import hashlib
import base64
import gzip
import importlib.util
import traceback
import json
import os
from pathlib import Path
import re
import selectors
import subprocess
import sys
import time

root = Path.cwd()
pin = "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
# The owner submits only after the b55 original strict321 gate succeeds; all eleven repaired source hashes are fixed.
assert re.fullmatch(r"[0-9a-f]{40}", pin), "NEW_COMMIT has not been finalized"
A = "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate"
B = "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate"
W = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
ordered_expected = "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
snapshot_path = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected = "71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected = {
    "verification/part2/run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "verification/part2/run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "verification/part2/winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "verification/part2/inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
    "ImbalancedChen/P2HistoricLogPointInterpreter.lean": "07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552",
    "ImbalancedChen/P2OriginalCompactCachedRun.lean": "61ea2a921d3b754feb82b507a7b632c8570cc6a0b35d3d3ebca0c02936553ce9",
    "ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean": "03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd",
    "ImbalancedChen/P2OriginalCompactCachedEndpointCandidate.lean": "3f84c653e57cf48266a4160477c94112acbad086028c75652892fb9ab04aecb6",
    "verification/part2/export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "ImbalancedChen/P2OriginalCompactWholeFunctionalEndpoint.lean": "606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185",
    "ImbalancedChen/ActualThirdOriginalP4AOrdinaryFiniteSelector.lean": "bc50bc05f214ff8c9716000558c170fb8a92334ff7bd32465616507107f81547",
    "ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean": "048eda0f169f5842cf3a969e0c05eb1192222ac920e71153b4cecd5e564990a6",
    "ImbalancedChen/P2OriginalAdaptiveForestSourceIdentity.lean": "e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6",
    "ImbalancedChen/P2OriginalCompactConcreteLoop.lean": "04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0",
    "ImbalancedChen/P2OriginalCompactConcreteRun.lean": "18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2",
    "ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean": "b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d",
    "ImbalancedChen/P2OriginalCompactQ80Encloser.lean": "139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058",
    "ImbalancedChen/P2OriginalPriorityForestLedger.lean": "11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c",
    "ImbalancedChen/P2OriginalCompactQ80Reachability.lean": "6f78f1f03b58666d7c968bbcebd6d7c72a680ed8340a685c67404ea2a873c5fb",
    "ImbalancedChen/P2OriginalCompactQ80FixedBindings.lean": "ba24af1a733626cafc3d53d5fc5294c021879b7503c639f4ef97b937cbd00cc9"
}

def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def json_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def check_source():
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == pin
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    actual = {name: digest(root / name) for name in expected}
    assert actual == expected, "Pinned source or original verifier bytes changed"

check_source()
sys.path.insert(0, str(root / "verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes

assert PIN == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected = {
    LEAN: "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    LEANCHECKER: "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
}
assert {name: digest(name) for name in runtime_expected} == runtime_expected
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
assert digest(snapshot_path) == snapshot_expected
roots = [
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness",
    "ImbalancedChen.P2OriginalCompactCachedRun",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve",
]
full_nodes = project_nodes(root, W)
full = list(full_nodes)
assert len(full) == 324 and len(set(full)) == 324
assert hashlib.sha256(("\n".join(full) + "\n").encode()).hexdigest() == ordered_expected
prereq_nodes = {}
for name in roots:
    prereq_nodes.update(project_nodes(root, name))
assert len(prereq_nodes) == 321
assert set(full) - set(prereq_nodes) == {A, B, W}
assert A not in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes
a_nodes = project_nodes(root, A)
assert len(a_nodes) == 102 and A in a_nodes
assert set(a_nodes) - {A} <= set(prereq_nodes)
assert len(project_nodes(root, B)) == 103
sources_before = {name: digest(node["source"]) for name, node in full_nodes.items()}
lib = root / ".lake/p2-private/lib"
registry = root / ".lake/p2-private/records.json"
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
native_before = external.binding()
assert native_before["snapshot_sha256"] == snapshot_expected
assert native_before["context_signature"] == native_context_expected
assert native_before["verification_helper_sha256"] == expected["verification/part2/winner9_external_snapshot.py"]
assert Path(external.value["runtime"]["leanchecker"]).resolve() == Path(LEANCHECKER).resolve()
assert external.files[external.value["runtime"]["leanchecker"]]["sha256"] == runtime_expected[LEANCHECKER]
mark_project_nodes(full_nodes, set(external.modules))
toolchain = {
    "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
    "lean_binary_sha256": runtime_expected[LEAN],
    "mathlib_commit": PIN,
}

SERIALIZED_NAMES_TEMPLATE_BASE64 = 'aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0UTgwQ29tcGxldGVTb3VuZG5lc3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxDb21wYWN0Q2FjaGVkUnVuCmltcG9ydCBJbWJhbGFuY2VkQ2hlbi5QMk9yaWdpbmFsQ29tcGFjdFE4MEZpeGVkQmluZGluZ3MKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlA0QU9yZGluYXJ5Um9vdEZpcnN0SW50ZWdyYWwKaW1wb3J0IEltYmFsYW5jZWRDaGVuLlBhcnQ0QWN0dWFsVGhpcmRGaW5pdGVEZW5zaXR5UmVzZXJ2ZQppbXBvcnQgSW1iYWxhbmNlZENoZW4uUDJPcmlnaW5hbENvbXBhY3RBcmNoaXZlZFRvdGFsQ2FuZGlkYXRlCmltcG9ydCBMZWFuLkVsYWIuQ29tbWFuZAoKLy0gRGlhZ25vc3RpYyBvbmx5OiByZXBvcnQgZWFjaCBpbXBvcnRlZCBsZWdhY3kgbW9kdWxlJ3Mgb3JpZ2luYWwgc2VyaWFsaXplZAogICBjb25zdE5hbWVzLCB3aXRob3V0IGZpbHRlcmluZyB0aHJvdWdoIHRoZSBtZXJnZWQgZW52aXJvbm1lbnQncyBzaW5nbGUgb3duZXIuCiAgIFRoaXMgbmVpdGhlciBjaGVja3MgZnVsbCB0eXBlcy9heGlvbXMgbm9yIHJlcGxhY2VzIHRoZSBvcmlnaW5hbCBvd25lZCBhdWRpdC4gLS8Kb3BlbiBMZWFuIEVsYWIgQ29tbWFuZCBpbgpydW5fY21kIGRvCiAgbGV0IGVudiDihpAgZ2V0RW52CiAgbGV0IGV4cGVjdGVkTW9kdWxlcyA6IEFycmF5IE5hbWUgOj0gI1sKX19QMjRfRVhQRUNURURfTU9EVUxFX05BTUVTX18KICBdCiAgdW5sZXNzIGV4cGVjdGVkTW9kdWxlcy5zaXplID09IDMyMiBkbyB0aHJvd0Vycm9yICJXcm9uZyBjdXJyZW50IGNvbXBpbGVkIHNjb3BlIgogIGxldCBhY3R1YWxQcm9qZWN0IDo9IGVudi5oZWFkZXIubW9kdWxlTmFtZXMuZmlsdGVyIGZ1biBuID0+CiAgICBuLnRvU3RyaW5nLnN0YXJ0c1dpdGggIkltYmFsYW5jZWRDaGVuLiIKICB1bmxlc3MgYWN0dWFsUHJvamVjdC5xc29ydCBOYW1lLmx0ID09IGV4cGVjdGVkTW9kdWxlcy5xc29ydCBOYW1lLmx0IGRvCiAgICB0aHJvd0Vycm9yICJMb2FkZWQgcHJvamVjdCBtb2R1bGVzIGRpZmZlciBmcm9tIGN1cnJlbnQzMjI7IEIgYW5kIFcgbXVzdCBub3QgYmUgaW1wb3J0ZWQiCiAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1NFUklBTElaRURfSU1QT1JUUyB7KHRvSnNvbiAoZW52LmhlYWRlci5tb2R1bGVOYW1lcy5tYXAgTmFtZS50b1N0cmluZykpLmNvbXByZXNzfSIKICBsZXQgbXV0IHRvdGFsT2NjdXJyZW5jZXMgOiBOYXQgOj0gMAogIGZvciBtb2R1bGVOYW1lIGluIGV4cGVjdGVkTW9kdWxlcyBkbwogICAgbGV0IG11dCBzZXJpYWxpemVkIDogQXJyYXkgTmFtZSA6PSAjW10KICAgIGxldCBtdXQgZm91bmQgOj0gZmFsc2UKICAgIGxldCBtdXQgaGVhZGVySW5kZXggOiBOYXQgOj0gMAogICAgZm9yIGkgaW4gTGlzdC5yYW5nZSBlbnYuaGVhZGVyLm1vZHVsZXMuc2l6ZSBkbwogICAgICBsZXQgaW1wb3J0ZWQgOj0gZW52LmhlYWRlci5tb2R1bGVzW2ldIQogICAgICBpZiBpbXBvcnRlZC5tb2R1bGUgPT0gbW9kdWxlTmFtZSB0aGVuCiAgICAgICAgaWYgZm91bmQgdGhlbiB0aHJvd0Vycm9yICJEdXBsaWNhdGUgbW9kdWxlIGhlYWRlciB7bW9kdWxlTmFtZX0iCiAgICAgICAgZm91bmQgOj0gdHJ1ZQogICAgICAgIGhlYWRlckluZGV4IDo9IGkKICAgICAgICBsZXQgZGF0YSA6PSBlbnYuaGVhZGVyLm1vZHVsZURhdGFbaV0hCiAgICAgICAgaWYgZGF0YS5pc01vZHVsZSB8fCAhaW1wb3J0ZWQuaW1wb3J0QWxsIHx8ICFpbXBvcnRlZC5oYXNEYXRhIHRoZW4KICAgICAgICAgIHRocm93RXJyb3IgIkluY29tcGxldGUgaW1wb3J0ZWQgbGVnYWN5IGRhdGEge21vZHVsZU5hbWV9IgogICAgICAgIHNlcmlhbGl6ZWQgOj0gZGF0YS5jb25zdE5hbWVzCiAgICB1bmxlc3MgZm91bmQgJiYgc2VyaWFsaXplZC5zaXplID4gMCBkbwogICAgICB0aHJvd0Vycm9yICJNaXNzaW5nIG9yIGVtcHR5IHNlcmlhbGl6ZWQgbW9kdWxlIHttb2R1bGVOYW1lfSIKICAgIHRvdGFsT2NjdXJyZW5jZXMgOj0gdG90YWxPY2N1cnJlbmNlcyArIHNlcmlhbGl6ZWQuc2l6ZQogICAgbGlmdElPIDx8IElPLnByaW50bG4gcyEiUDI0X1NFUklBTElaRURfTU9EVUxFIHsoSnNvbi5ta09iaiBbKCJtb2R1bGUiLCB0b0pzb24gbW9kdWxlTmFtZS50b1N0cmluZyksICgiaGVhZGVyX2luZGV4IiwgdG9Kc29uIGhlYWRlckluZGV4KSwgKCJsZWdhY3lfZGF0YV9jb21wbGV0ZSIsIHRvSnNvbiB0cnVlKSwgKCJjb3VudCIsIHRvSnNvbiBzZXJpYWxpemVkLnNpemUpLCAoInNlcmlhbGl6ZWQiLCB0b0pzb24gKHNlcmlhbGl6ZWQubWFwIE5hbWUudG9TdHJpbmcpKV0pLmNvbXByZXNzfSIKICBsaWZ0SU8gPHwgSU8ucHJpbnRsbiBzISJQMjRfU0VSSUFMSVpFRF9DT01QTEVURSB7KEpzb24ubWtPYmogWygibW9kdWxlcyIsIHRvSnNvbiBleHBlY3RlZE1vZHVsZXMuc2l6ZSksICgic2VyaWFsaXplZF9vY2N1cnJlbmNlcyIsIHRvSnNvbiB0b3RhbE9jY3VycmVuY2VzKSwgKCJkaWFnbm9zdGljX29ubHkiLCB0b0pzb24gdHJ1ZSksICgibWVyZ2VkX293bmVyX2ZpbHRlcl91c2VkIiwgdG9Kc29uIGZhbHNlKSwgKCJpbmRlcGVuZGVudF9yZXBsYXkiLCB0b0pzb24gZmFsc2UpLCAoImZ1bGxfdHlwZXNfb3JfYXhpb21zX2F1ZGl0ZWQiLCB0b0pzb24gZmFsc2UpLCAoIm9yaWdpbmFsX293bmVkX2NyZWRpdCIsIHRvSnNvbiBmYWxzZSldKS5jb21wcmVzc30iCg=='
SERIALIZED_NAMES_TEMPLATE_SHA256 = '7bf314dade91aa255dcc013198fea70c2d791b8a50f0869d9b8d173470abf854'

# Only inspect existing olean module inventories. No -o, production compiler,
# audit runner, selector, registry writer, package exporter, or source edit.
out = Path('/workspace/p24-current322-serialized-names-b55-20261126/attempt-001')
scan_nodes = dict(prereq_nodes)
scan_nodes.update(a_nodes)
scan_order = [name for name in full if name in scan_nodes]
assert len(scan_order) == len(scan_nodes) == 322
assert set(full) - set(scan_order) == {B, W}
assert A in scan_nodes and B not in scan_nodes and W not in scan_nodes
scan_fingerprint = hashlib.sha256(('\n'.join(scan_order) + '\n').encode()).hexdigest()
registry_raw_before = registry.read_bytes()
records_before = json.loads(registry_raw_before)
registry_before_sha = hashlib.sha256(registry_raw_before).hexdigest()
assert external.verify() == native_before
before_frozen = snapshot(root, lib, full_nodes, toolchain, external)
assert before_frozen['external_snapshot'] == native_before
verify_compilation(records_before, scan_nodes, before_frozen)
assert not out.exists(), 'Do not overwrite an earlier diagnostic'
assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 64 * 1024 * 1024
out.mkdir(parents=True, exist_ok=False)

def file_info(path):
    path = Path(path)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest(path)}

def write_new_json(name, value):
    path = out / name
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= len(raw) + 32 * 1024 * 1024
    with path.open('xb') as stream:
        stream.write(raw)
    assert path.read_bytes() == raw
    return file_info(path)

def write_new_gzip_json(name, value):
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
    encoded = gzip.compress(raw, compresslevel=9, mtime=0)
    assert gzip.decompress(encoded) == raw
    path = out / name
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= len(encoded) + 32 * 1024 * 1024
    with path.open('xb') as stream:
        stream.write(encoded)
    actual = path.read_bytes()
    assert actual == encoded and gzip.decompress(actual) == raw
    return {'gzip': file_info(path), 'uncompressed_bytes': len(raw),
            'uncompressed_sha256': hashlib.sha256(raw).hexdigest(), 'exact_roundtrip_verified': True}

artifacts = {}
checks = {}
errors = []
stage = None
report = None
child = None
scan_source = None
rendered = None
raw_template = base64.b64decode(SERIALIZED_NAMES_TEMPLATE_BASE64, validate=True)
assert hashlib.sha256(raw_template).hexdigest() == SERIALIZED_NAMES_TEMPLATE_SHA256

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({'check': name, 'type': type(error).__name__, 'error': str(error),
                       'traceback': traceback.format_exc()})

def check_runtime_and_native():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected
    assert external.verify() == native_before

def check_registry():
    assert registry.read_bytes() == registry_raw_before, 'Current canonical registry bytes changed'

def current_frozen():
    nodes = project_nodes(root, W)
    assert list(nodes) == full
    assert {name: digest(node['source']) for name, node in nodes.items()} == sources_before
    mark_project_nodes(nodes, set(external.modules))
    return snapshot(root, lib, nodes, toolchain, external)

def check_all_sources_objects():
    current = current_frozen()
    artifacts['inputs_after'] = write_new_json('inputs-after.json', current)
    assert current == before_frozen, 'Full324 source/object/tool/native snapshot changed'
    verify_compilation(json.loads(registry_raw_before), scan_nodes, current)

def check_isolated_source():
    if scan_source is not None:
        assert scan_source.read_bytes() == rendered, 'Diagnostic source changed'
        assert not scan_source.with_suffix('.olean').exists(), 'Diagnostic unexpectedly wrote an object'

try:
    artifacts['inputs_before'] = write_new_json('inputs-before.json', before_frozen)
    artifacts['scope'] = write_new_json('scope.json', {
        'source_pin': pin, 'full324_ordered_fingerprint': ordered_expected,
        'current322_ordered_fingerprint': scan_fingerprint, 'current322': scan_order,
        'excluded': [B, W], 'registry_bytes': len(registry_raw_before),
        'registry_sha256': registry_before_sha,
        'current322_source_object_bindings': {n: before_frozen['project'][n] for n in scan_order},
        'diagnostic_only': True, 'canonical_credit': False,
    })
    rendered = raw_template.replace(b'__P24_EXPECTED_MODULE_NAMES__',
        ',\n'.join('    `' + name for name in scan_order).encode())
    assert raw_template.count(b'__P24_EXPECTED_MODULE_NAMES__') == 1
    assert b'__P24_EXPECTED_MODULE_NAMES__' not in rendered
    scan_source = out / 'SerializedNames.lean'
    with scan_source.open('xb') as stream:
        stream.write(rendered)
    artifacts['source'] = file_info(scan_source)
    env = external.environment(dict(os.environ))
    flags = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
             '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000']
    command = [LEAN, *flags, str(scan_source)]
    log = out / 'serialized-names.log'
    print('P24_SERIALIZED_322_BEGIN ' + json.dumps({'source_pin': pin, 'module_count': 322,
        'source_sha256': artifacts['source']['sha256'], 'output': str(out),
        'no_production_compile': True, 'canonical_credit': False}), flush=True)
    started = time.monotonic()
    timed_out = False
    with log.open('xb') as stream:
        child = subprocess.Popen(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        try:
            code = child.wait(timeout=300)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.kill()
            code = child.wait()
    stage = {'command': command, 'exit_code': code, 'timed_out': timed_out,
             'elapsed_seconds': time.monotonic() - started, 'log': file_info(log)}
    if code != 0:
        if log.stat().st_size <= 20 * 1024:
            print('COMPLETE_LEAN_ERROR_LOG_BEGIN', flush=True)
            sys.stdout.buffer.write(log.read_bytes())
            sys.stdout.buffer.flush()
            print('COMPLETE_LEAN_ERROR_LOG_END', flush=True)
        else:
            print('Complete Lean output retained at ' + str(log) + '; not truncated.', flush=True)
    assert code == 0 and not timed_out, 'Serialized-name child did not finish successfully'
    imports, inventories, complete = [], [], []
    for line in log.read_text().splitlines():
        for prefix, records in [('P24_SERIALIZED_IMPORTS ', imports),
                                ('P24_SERIALIZED_MODULE ', inventories),
                                ('P24_SERIALIZED_COMPLETE ', complete)]:
            if line.startswith(prefix):
                records.append(json.loads(line[len(prefix):]))
                break
    assert len(imports) == 1 and len(complete) == 1
    assert [row['module'] for row in inventories] == scan_order
    assert len(inventories) == len({row['module'] for row in inventories}) == 322
    assert {n for n in imports[0] if n.startswith('ImbalancedChen.')} == set(scan_order)
    owners = {}
    within_module_duplicates = {}
    for row in inventories:
        assert row['legacy_data_complete'] is True
        assert isinstance(row['header_index'], int) and row['header_index'] >= 0
        names = row['serialized']
        assert isinstance(names, list) and names and len(names) == row['count']
        assert all(isinstance(n, str) and n for n in names)
        counts = {}
        for name in names:
            counts[name] = counts.get(name, 0) + 1
        repeated = {n: count for n, count in counts.items() if count > 1}
        if repeated:
            within_module_duplicates[row['module']] = repeated
        for name in counts:
            owners.setdefault(name, []).append(row['module'])
    total = sum(row['count'] for row in inventories)
    assert complete[0]['modules'] == 322 and complete[0]['serialized_occurrences'] == total
    assert complete[0]['merged_owner_filter_used'] is False
    assert complete[0]['diagnostic_only'] is True and complete[0]['original_owned_credit'] is False
    assert complete[0]['independent_replay'] is False and complete[0]['full_types_or_axioms_audited'] is False
    duplicates = {n: v for n, v in sorted(owners.items()) if len(v) > 1}
    report = {'source_pin': pin, 'registry_sha256': registry_before_sha,
              'full324_ordered_fingerprint': ordered_expected,
              'current322_ordered_fingerprint': scan_fingerprint,
              'modules': 322, 'serialized_occurrences': total, 'unique_names': len(owners),
              'module_counts': {r['module']: r['count'] for r in inventories},
              'duplicate_names': duplicates, 'within_module_duplicate_names': within_module_duplicates,
              'inventories': inventories,
              'source_object_bindings': {n: before_frozen['project'][n] for n in scan_order},
              'diagnostic_only': True, 'full_types_audited': False, 'axioms_audited': False,
              'independent_replay': False, 'original_owned_credit': False,
              'full324_credit': False, 'B_or_W_imported': False}
    artifacts['full_inventories'] = write_new_gzip_json('current322-serialized-inventories.json.gz', report)
    duplicate_report = {k: report[k] for k in ('source_pin','registry_sha256','modules',
        'serialized_occurrences','unique_names','duplicate_names','within_module_duplicate_names',
        'diagnostic_only','original_owned_credit','full324_credit')}
    artifacts['duplicates'] = write_new_gzip_json('current322-duplicate-names.json.gz', duplicate_report)
    small = json.dumps(duplicate_report, ensure_ascii=False)
    if len(small.encode()) <= 200 * 1024:
        print('P24_SERIALIZED_DUPLICATES ' + small, flush=True)
    else:
        print('Complete duplicates exceed 200 KiB stdout budget; lossless gzip retained, no records truncated.', flush=True)
    for module in scan_order:
        print('P24_SERIALIZED_MODULE_COUNT ' + json.dumps({'module':module, 'count':report['module_counts'][module]}), flush=True)
except Exception as error:
    errors.append({'check': 'diagnostic', 'type': type(error).__name__, 'error': str(error),
                   'traceback': traceback.format_exc()})
finally:
    if child is not None and child.poll() is None:
        child.kill()
        child.wait()
    perform('tracked_pin_sources_and_original_tools_unchanged', check_source)
    perform('runtime_and_qualified_native_unchanged', check_runtime_and_native)
    perform('complete_registry_bytes_unchanged', check_registry)
    perform('complete_full324_snapshot_and_current322_compilation_valid', check_all_sources_objects)
    perform('isolated_source_unchanged_and_no_diagnostic_object', check_isolated_source)
    scan_complete = report is not None and not errors and all(checks.values())
    return_code = 0 if scan_complete else (stage['exit_code'] if stage and stage['exit_code'] != 0 else 125)
    receipt = {'source_pin': pin, 'diagnostic_completed': scan_complete, 'exit_code': return_code,
        'current_compiled_scope': 322, 'full_scope': 324, 'full324_ordered_fingerprint': ordered_expected,
        'current322_ordered_fingerprint': scan_fingerprint, 'registry_before_sha256':registry_before_sha,
        'registry_after_sha256':digest(registry), 'stage':stage, 'postchecks':checks, 'errors':errors,
        'artifacts':artifacts, 'duplicate_count': len(report['duplicate_names']) if report else None,
        'duplicate_owner_modules':sorted({m for ms in report['duplicate_names'].values() for m in ms}) if report else None,
        'original_template_unchanged':True,'selector_unchanged_and_not_run':True,
        'no_production_source_or_object_written':True,'zero_budget_not_repeated':True,
        'canonical_credit':False,'original_owned_credit':False,'finite_credit':False,'full324_credit':False}
    receipt_info = write_new_json('receipt.json', receipt)
    print('P24_SERIALIZED_322_RESULT ' + json.dumps({'receipt':receipt_info,
        **{k:v for k,v in receipt.items() if k not in ('artifacts','stage')}}), flush=True)
    assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 32 * 1024 * 1024
raise SystemExit(return_code)
