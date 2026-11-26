#!/usr/bin/env python3
"""Create a byte-exact source upload and compile command in the primary workspace."""
from pathlib import Path
import argparse
import base64
import hashlib
import json
import re
import shlex

ROOT = Path(__file__).resolve().parents[3]
CLOUD_ROOT = '/workspace/p2-1-original96-20261126'

def checked_relative(value):
    path = Path(value)
    if (not value or path.is_absolute() or '..' in path.parts or
            not re.fullmatch(r'[A-Za-z0-9_./-]+', value)):
        raise ValueError('expected a scoped relative path')
    return value

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--round', required=True)
    p.add_argument('--file', action='append', default=[])
    p.add_argument('--compile', action='append', default=[])
    p.add_argument('--probe', action='append', default=[])
    p.add_argument('--script', action='append', default=[])
    a = p.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', a.round):
        raise ValueError('expected a round basename')
    for rel in [*a.file, *a.compile, *a.probe, *a.script]:
        checked_relative(rel)
    payload = {'round': a.round, 'root': CLOUD_ROOT, 'files': [],
               'compile': a.compile, 'probe': a.probe, 'script': a.script}
    for rel in a.file:
        f = (ROOT / rel).resolve()
        if not f.is_relative_to(ROOT):
            raise ValueError('file escapes primary worktree')
        data = f.read_bytes()
        payload['files'].append({'path': rel, 'sha256': hashlib.sha256(data).hexdigest(),
                                 'base64': base64.b64encode(data).decode()})
    runner = (Path(__file__).parent / 'compile_uploaded.py').read_bytes()
    entry = "import base64;exec(compile(base64.b64decode(" + repr(base64.b64encode(runner).decode()) + "), 'primary-authored-compile_uploaded.py', 'exec'))"
    command = ('python3 -c ' + shlex.quote(entry) + " <<'P21_ORIGINAL96_PAYLOAD'\n" +
               json.dumps(payload, separators=(',', ':')) + '\nP21_ORIGINAL96_PAYLOAD\n')
    if len(command.encode()) > 60000:
        raise ValueError('submission exceeds 60000 bytes; split uploads into smaller batches')
    submission = {'command': command, 'cwd': '/workspace', 'memory_mb': 8192,
                  'cpu_threads': 2, 'timeout_seconds': 600}
    evidence = ROOT / 'docs/verification/20261126-p2-1-original96/development' / a.round
    evidence.mkdir(parents=True, exist_ok=False)
    (evidence / 'submission.json').write_text(json.dumps(submission, indent=2) + '\n')
    (evidence / 'inputs.json').write_text(json.dumps({**payload, 'files': [
        {k: v for k, v in f.items() if k != 'base64'} for f in payload['files']]}, indent=2) + '\n')
    print(json.dumps(submission))

if __name__ == '__main__':
    main()
