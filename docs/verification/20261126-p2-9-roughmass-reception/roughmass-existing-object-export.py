import sys
sys.dont_write_bytecode = True
import os, stat, json, hashlib, base64, datetime
from pathlib import Path

MODULE = 'ImbalancedChen.P2FiniteMarkedGamma5RadialRoughMass'
OBJECT_PATH = Path('/workspace/p29-nonunit-quotient-20261126-0117dd4/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5RadialRoughMass.olean')
EXPECTED_BYTES = 498736
EXPECTED_SHA256 = '9c70ee9877b4b6158220d8b871cb8f240082958cc61f1770bb77a4fcbaa3486a'
MAX_STDOUT_BYTES = 700000


def stamp(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size,
            s.st_mtime_ns, s.st_ctime_ns]


def snapshot():
    resolved = OBJECT_PATH.resolve(strict=True)
    logical = OBJECT_PATH.lstat()
    target = OBJECT_PATH.stat()
    assert resolved.is_relative_to('/workspace')
    assert stat.S_ISREG(target.st_mode)
    assert target.st_size == EXPECTED_BYTES
    return {'resolved_path': str(resolved), 'logical_lstat': stamp(logical),
            'target_stat': stamp(target)}


source_text = globals().get('SOURCE_TEXT')
assert isinstance(source_text, str), 'Use the pinned in-memory launcher.'
exporter = source_text.encode('utf-8')
before = snapshot()
with OBJECT_PATH.open('rb') as stream:
    assert stamp(os.fstat(stream.fileno())) == before['target_stat']
    data = stream.read(EXPECTED_BYTES + 1)
    assert stamp(os.fstat(stream.fileno())) == before['target_stat']
assert len(data) == EXPECTED_BYTES
digest = hashlib.sha256(data).hexdigest()
assert digest == EXPECTED_SHA256
after = snapshot()
assert after == before, 'The exact old object path/stat changed during reception.'
encoded = base64.b64encode(data).decode('ascii')
assert len(encoded) == 4 * ((EXPECTED_BYTES + 2) // 3)
meta = {
    'schema': 'p29_roughmass_existing_exact_object_export_v1',
    'module': MODULE,
    'object_path': str(OBJECT_PATH),
    'bytes': len(data),
    'sha256': digest,
    'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest(),
    'before': before,
    'after': after,
    'source_already_recovered_locally': {
        'git_blob': 'aca4621da617c19221048a7d8d11f0b22694ee09',
        'bytes': 9367,
        'sha256': '7766fbca185e25e7380aee84e805cd3c35b94daaa8e6f7f98740ee3533fb67eb',
        'read_on_P1_by_this_exporter': False,
        'retransmitted': False,
    },
    'exporter': {
        'bytes': len(exporter),
        'sha256': hashlib.sha256(exporter).hexdigest(),
        'git_blob': hashlib.sha1(b'blob ' + str(len(exporter)).encode() + b'\0' + exporter).hexdigest(),
    },
    'old_acceptance_commit': '952caa6e5bb055bb5a4ed87d1d9855de36e4b35a',
    'scope': 'Only transfer the exact already accepted .olean bytes; no qualification replay.',
    'remote_files_written_by_exporter': 0,
    'directory_scans': 0,
    'Lean_processes': 0,
    'new_proof_credit': 0,
    'P3_full_native_reception_complete': False,
    'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'maximum_stdout_bytes': MAX_STDOUT_BYTES,
}
output = ('P29_ROUGHMASS_OBJECT_EXPORT_META ' + json.dumps(meta, sort_keys=True, separators=(',', ':'))
          + '\nP29_ROUGHMASS_OBJECT_BASE64 ' + encoded + '\n').encode('ascii')
assert len(output) <= MAX_STDOUT_BYTES
sys.stdout.buffer.write(output)
sys.stdout.buffer.flush()
