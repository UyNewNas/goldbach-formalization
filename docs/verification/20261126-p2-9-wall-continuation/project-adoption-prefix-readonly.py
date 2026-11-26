from pathlib import Path
import os, json, hashlib, base64, sys

p = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/project-adoptions/attempt-001/PROJECT_CACHE_ADOPTION.json')
def identity(st):
    return {k: getattr(st, k) for k in ('st_dev', 'st_ino', 'st_mode', 'st_size', 'st_mtime_ns', 'st_ctime_ns')}
resolved = str(p.resolve(strict=True))
before = {'resolved_path': resolved, 'lstat': identity(p.lstat()), 'stat': identity(p.stat())}
with p.open('rb') as f:
    assert identity(os.fstat(f.fileno())) == before['stat']
    prefix = f.read(65536)
    assert identity(os.fstat(f.fileno())) == before['stat']
after = {'resolved_path': str(p.resolve(strict=True)), 'lstat': identity(p.lstat()), 'stat': identity(p.stat())}
assert before == after and len(prefix) == min(65536, before['stat']['st_size'])
meta = {'schema': 'p29_project_adoption_prefix_only_v1', 'path': str(p), 'before': before, 'after': after, 'stable_identity': True,
        'prefix_offset': 0, 'prefix_bytes': len(prefix), 'prefix_sha256': hashlib.sha256(prefix).hexdigest(),
        'expected_full_file_sha256_from_original_record': 'c481b63afedeb846f3a07371518c692b3ce71eeb2050fe48b9fc2b527a763269',
        'full_file_sha256_verified': False, 'whole_file_contents_read': len(prefix) == before['stat']['st_size'], 'registry_reads': 0, 'Lean_invocations': 0, 'filesystem_writes': 0}
output = 'P29_ADOPTION_PREFIX_META ' + json.dumps(meta, separators=(',', ':')) + '\nP29_ADOPTION_PREFIX_BASE64 ' + base64.b64encode(prefix).decode() + '\n'
assert len(output.encode()) < 90000
sys.stdout.write(output)
