from pathlib import Path
import ast
import datetime
from datetime import timezone
import hashlib
import json

ROOT = Path('/workspace/scratch/c397bfd2830f')
OUT = ROOT / 'p29-qualified-resume/docs/verification/20261127-p2-9-omitted-qualifier-resume'
raw = (OUT / 'FRESH_SERVICE_OBSERVATION.json').read_text()
digest = hashlib.sha256(raw.encode()).hexdigest()
document = json.loads(raw)
postimage = (OUT / 'v6-controller/postimage.py').read_text()
tree = ast.parse(postimage)
functions = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in {'require', 'service_observation'}]
assert {n.name for n in functions} == {'require', 'service_observation'}
space = {'hashlib': hashlib, 'json': json, 'datetime': datetime, 'timezone': timezone,
         'MCP_MEMORY_MB': 12800, 'MCP_CPU_THREADS': 2, 'MCP_TIMEOUT_SECONDS': 3600,
         'OBSERVED_MCP_MAX_MEMORY_MB': 13107, 'SERVICE_OBSERVATION_JSON': raw,
         'SERVICE_OBSERVATION_SHA256': digest}
exec(compile(ast.Module(body=functions, type_ignores=[]), '<isolated-original-service-observation>', 'exec'), space)
parsed = space['service_observation']()
loader = (OUT / 'transport/pinned_blob_loader.py').read_text()
compile(loader, '<reviewed-pinned-blob-loader>', 'exec')
prefix = 'SERVICE_OBSERVATION_JSON = ' + repr(raw) + '\nSERVICE_OBSERVATION_SHA256 = ' + repr(digest) + '\n'
body = prefix + loader
delimiter = 'P29_V6_PINNED_BLOB_LOADER'
assert delimiter not in body.splitlines()
command = "python3 - <<'" + delimiter + "'\n" + body + '\n' + delimiter
assert len(command.encode()) <= 65536
request = {'command': command, 'cwd': '/workspace', 'memory_mb': 12800, 'cpu_threads': 2, 'timeout_seconds': 3600}
assert {k: request[k] for k in ['memory_mb', 'cpu_threads', 'timeout_seconds']} == document['requested_MCP_limits']
assert 0 <= parsed['runtime_seconds_after_observation'] < 300
(OUT / 'ACTUAL_WRAPPER.py').write_text(body)
(OUT / 'ACTUAL_REQUEST.json').write_text(json.dumps(request, ensure_ascii=False, indent=2) + '\n')
preflight = {'schema': 'p29_omitted_qualifier_v6_actual_request_preflight_v1',
             'status': 'PASS_LOCAL_STRICT_ORIGINAL_PARSER_AND_REQUEST_BINDING',
             'observation_sha256': digest, 'observation_bytes': len(raw.encode()),
             'request_limits': {k:v for k,v in request.items() if k != 'command'},
             'clock_before': document['clock_before'], 'clock_after': document['clock_after'],
             'command_bytes': len(command.encode()), 'maximum_command_bytes': 65536,
             'command_sha256': hashlib.sha256(command.encode()).hexdigest(),
             'wrapper_bytes': len(body.encode()), 'wrapper_sha256': hashlib.sha256(body.encode()).hexdigest(),
             'loader_sha256': hashlib.sha256(loader.encode()).hexdigest(),
             'original_service_parser_reused_without_changes': True,
             'compiler_or_controller_main_executed_locally': False,
             'future_actual_submitted_at_join_still_required': True,
             'new_formal_credit': 0}
(OUT / 'PREFLIGHT.json').write_text(json.dumps(preflight, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'request': request, 'preflight': preflight}))
