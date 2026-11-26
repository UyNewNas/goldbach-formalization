import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/p24-integration-repairs-20261126/a-canonical-owned/p2-canonical-A-shape-b55-draft01.py')
source = (HERE / 'P24CachedEndpointRawDefEqDiagnostic.lean').read_bytes()
assert len(source) == 2863
assert hashlib.sha256(source).hexdigest() == '2eb7dc403ee25098cfe711ab887d3988fe6c87a8872cca758d49ed36dd06cf4e'
base = BASE.read_text()
assert hashlib.sha256(base.encode()).hexdigest() == '0075c5e925ba17bba1f9def58cc93a124a91ab82fd52525493f6bd95f83b2b2a'
prefix = base[:base.index('SHAPE_SOURCE = ')]
tree = ast.parse(base)
helper_names = ['available_bytes', 'need_free', 'encoded_json', 'write_derived',
    'audit_directory_fingerprint', 'stop_only_this_child', 'capture_complete_stdout',
    'fingerprint_gzip_payload']
helper_text = []
for name in helper_names:
    node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
    text = ast.get_source_segment(base, node)
    if name == 'capture_complete_stdout':
        assert text.count('canonical_A_shape_capture_progress') == 1
        text = text.replace('canonical_A_shape_capture_progress', 'B_raw_defeq_capture_progress')
    helper_text.append(text)
settings = '''
# Only a new diagnostic input and lossless output are written. Original B is not compiled.
MINIMUM_FREE_BYTES = 32 * 1024 * 1024
METADATA_ALLOWANCE = 2 * 1024 * 1024
CAPTURE_DRAIN_ALLOWANCE = 4 * 1024 * 1024
CHUNK_BYTES = 65536
out = root / ".lake/p24-B-raw-defeq/b55-attempt-001"
assert not out.exists() and not out.is_symlink(), "Preserve prior diagnostic evidence"
assert out.resolve().is_relative_to(root.resolve())
diagnostic_source_sha256 = "2eb7dc403ee25098cfe711ab887d3988fe6c87a8872cca758d49ed36dd06cf4e"
actual_B_failure_registry_sha256 = "3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445"
failure_log = root / ".lake/p2-private/logs/ImbalancedChen.P2OriginalCompactCachedEndpointCandidate.attempt1.log"
'''
tail = (HERE / 'raw-defeq-execution-tail-draft01.py').read_text()
script = prefix + 'DIAGNOSTIC_SOURCE = ' + repr(source.decode()) + '\n' + settings + '\n\n' + '\n\n\n'.join(helper_text) + '\n\n\n' + tail
ast.parse(script)
compile(script, 'prepared-raw-defeq-diagnostic', 'exec')
py = HERE / 'p2-B-raw-defeq-b55-draft01.py'
py.write_text(script)
shell = '''#!/usr/bin/env bash
# Prepared read-only B raw Meta precheck diagnostic; no original B/replay/audit credit.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_B_RAW_DEFEQ'
''' + script + '\nP24_B_RAW_DEFEQ\n'
sh = HERE / 'p2-B-raw-defeq-b55-draft01.sh'
sh.write_text(shell)
manifest = {
    'schema': 1, 'prepared_only': True, 'executed': False,
    'source_pin': 'b55fa93d39e6a4ddf2abd37b9b8481078e329f70',
    'basis': {'path': str(BASE), 'sha256': hashlib.sha256(base.encode()).hexdigest()},
    'setup_before_embedded_source_byte_identical': True,
    'helpers_copied_exactly': [n for n in helper_names if n != 'capture_complete_stdout'],
    'capture_helper_only_delta': 'progress label canonical_A_shape_capture_progress -> B_raw_defeq_capture_progress',
    'source_byte_identical_to_reviewed_2863_byte_probe': True,
    'original_B_source_changed': False, 'original_B_compiler_called': False,
    'second_guarded_defeq_probe': False, 'canonical_credit': False,
    'resource_contract': {'timeout_seconds':3600,'memory_mb':13107,'cpu_threads':1,'lean_memory_mb':11264,'lean_threads':1},
    'files': {},
}
for path in [HERE/'P24CachedEndpointRawDefEqDiagnostic.lean', py, sh, HERE/'raw-defeq-execution-tail-draft01.py', Path(__file__)]:
    data = path.read_bytes()
    manifest['files'][path.name] = {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
(HERE/'raw-defeq-wrapper-draft01-manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
for path in [py, sh, HERE/'raw-defeq-wrapper-draft01-manifest.json']:
    data = path.read_bytes()
    print(path.name, len(data), hashlib.sha256(data).hexdigest())
