#!/usr/bin/env python3
"""Read the first new Cell05 failed step and its unchanged receipt index only."""
from pathlib import Path
import hashlib
import json

stage = Path('/workspace/p26-cell05-connections14-stage-557a12f3bcd7')
attempt = stage / 'verification' / 'ready14-complete-v1'
target = 'P2OriginalSaving19Geometry05ScalableShapeArrays'
paths = [attempt / 'STOPPED.json', attempt / target / 'normal-command.json',
         attempt / target / 'normal-result.json', attempt / target / 'normal.log']

def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}

files = []
for path in paths:
    if not path.is_file() or path.is_symlink() or path.resolve() != path:
        raise RuntimeError('Missing or noncanonical original failure file: ' + str(path))
    data = path.read_bytes()
    files.append({**pin(path), 'text': data.decode('utf-8')})
run = attempt / 'RUN.json'
context = json.loads(run.read_text())['context']
obj = stage / 'objects' / 'ImbalancedChen' / (target + '.olean')
print(json.dumps({'schema': 'p26_cell05_first_failure_read_v1',
                  'files': files, 'original_run': pin(run),
                  'original_targets': [row['module'] for row in context['targets']],
                  'original_runtime_guard': context['runtime_guard'],
                  'failed_target_object_exists': obj.exists(),
                  'failed_target_object': pin(obj) if obj.is_file() else None,
                  'whole_attempt_success_exists': (attempt / 'SUCCESS.json').exists(),
                  'Lean_commands_executed': 0,
                  'existing_files_modified': False}), flush=True)
