"""Cloud execution of source bytes authored in the primary worktree only."""
from pathlib import Path
import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import time

payload = json.load(sys.stdin)
root = Path(payload['root'])
assert root == Path('/workspace/p2-1-original96-20261126')
assert re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', payload['round'])
for rel in [*(item['path'] for item in payload['files']), *payload['compile'],
            *payload['probe'], *payload.get('script', [])]:
    path = Path(rel)
    assert not path.is_absolute() and '..' not in path.parts
    assert re.fullmatch(r'[A-Za-z0-9_./-]+', rel)
root.mkdir(parents=True, exist_ok=True)
evidence = root / 'evidence' / payload['round']
evidence.mkdir(parents=True, exist_ok=False)
for item in payload['files']:
    path = (root / item['path']).resolve()
    assert path.is_relative_to(root.resolve())
    data = base64.b64decode(item['base64'])
    assert hashlib.sha256(data).hexdigest() == item['sha256']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
out = root / '.lake/build/lib/lean'
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env['LEAN_PATH'] = str(out) + ':' + env.get('LEAN_PATH', '')
records = []
def run(argv, label):
    started = time.monotonic()
    r = subprocess.run(argv, cwd=root, env=env, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    log = evidence / (label + '.log')
    log.write_bytes(r.stdout)
    records.append({'argv': argv, 'exit_code': r.returncode,
                    'elapsed_seconds': time.monotonic() - started,
                    'log': str(log), 'log_sha256': hashlib.sha256(r.stdout).hexdigest()})
    print(json.dumps(records[-1]), flush=True)
    print(r.stdout.decode(errors='replace'), end='', flush=True)
    return r.returncode

code = run(['lean', '--version'], 'version')
for rel in payload['compile']:
    if code:
        break
    path = Path(rel)
    target = out / path.with_suffix('.olean')
    assert target.resolve().is_relative_to(out.resolve())
    target.parent.mkdir(parents=True, exist_ok=True)
    code = run(['lean', '-DwarningAsError=true', '-DmaxRecDepth=10000',
                '-DmaxHeartbeats=4000000', '-o', str(target), rel],
               path.stem)
for rel in payload['probe']:
    if code:
        break
    code = run(['lean', '-DwarningAsError=true', '-DmaxRecDepth=10000',
                '-DmaxHeartbeats=4000000', rel], Path(rel).stem)
for rel in payload.get('script', []):
    if code:
        break
    code = run(['python3', '-B', rel], Path(rel).stem)
(evidence / 'execution.json').write_text(json.dumps({'inputs': payload, 'records': records,
    'exit_code': code, 'lean_path': env['LEAN_PATH']}, indent=2) + '\n')
raise SystemExit(code)
