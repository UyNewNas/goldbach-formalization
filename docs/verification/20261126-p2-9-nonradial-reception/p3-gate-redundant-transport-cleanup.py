import sys
sys.dont_write_bytecode = True
from pathlib import Path, PurePosixPath
import base64, datetime, hashlib, json, os, stat, urllib.request

# Exactly one removable derived transport file. No fallback or directory scan.
BASE = Path('/workspace/p29-gate-affine-20261126-ba9b1989')
ARCHIVE = BASE / 'qualified-gate-affine.tar.xz'
ARCHIVE_BYTES = 3894004
ARCHIVE_SHA256 = 'eb39540322acb1fc4d19b7a126a80df5430fdaf81208438e6c6f1bcd1eceb99b'
MANIFEST_SHA256 = '83c6f183ad9b228961899a842ff5bddb29c4ebabf078d0fe9e079822fe9da106'
VALIDATION_SHA256 = '73e98b9d96f49f14435f41cf77f7798e9e326930163ae6de90d55d4f3fd47f43'
GIT_DIRECTORY = 'docs/verification/20261126-p2-9-gate-affine'
SEALED_COMMIT = 'bbd5dac6'
PARTS_BLOB = '05d41b0c5e4a94e5309f1ee1b3570cad0d8654da'
ACCEPTANCE_BLOB = 'a095d954717e09ea2b42e96ba31d581d585a6a42'
EXPECTED_PARTS = [
    {'index': 0, 'file': 'qualified-gate-affine.part00', 'bytes': 1350000,
     'sha256': '1989d388ba749583230dfbe0059b55becfe89a05e94baa0632497ee24a36aaec',
     'git_blob': '7e33e2b7da09abfab5f976f9cda35a8368c948b4'},
    {'index': 1, 'file': 'qualified-gate-affine.part01', 'bytes': 1350000,
     'sha256': 'a131eb581fa000221ad42a2f79d9d3e95f49e3fba5cc7a6ee6bd3003b6d39d35',
     'git_blob': '653d3ecf2fbfb9af106723ab538caa91b514b487'},
    {'index': 2, 'file': 'qualified-gate-affine.part02', 'bytes': 1194004,
     'sha256': '274a2700b15aa70c8b1d6d12b51a18a1b3a1888d2abf2de4c0232935c00db15d',
     'git_blob': 'f7b58192336202e3bcf2bfd3db4484f22f01ea90'},
]
API = 'https://api.github.com/repos/UyNewNas/goldbach-formalization/'


def snapshot(path):
    s = Path(path).lstat()
    assert stat.S_ISREG(s.st_mode), ('not an original regular file', str(path))
    return [s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_nlink]


def file_hash(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()


def git_json_blob(blob):
    response = json.load(urllib.request.urlopen(API + 'git/blobs/' + blob, timeout=45))
    assert response['encoding'] == 'base64' and response['sha'] == blob
    data = base64.b64decode(''.join(response['content'].split()), validate=True)
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
    return json.loads(data)


assert BASE.is_dir() and not BASE.is_symlink() and BASE.resolve() == BASE
archive_before = snapshot(ARCHIVE)
assert archive_before[3] == ARCHIVE_BYTES and archive_before[-1] == 1
assert ARCHIVE.resolve() == ARCHIVE and file_hash(ARCHIVE) == ARCHIVE_SHA256
assert snapshot(ARCHIVE) == archive_before

# Confirm the immutable committed directory contains every original binary
# part. Only small Git metadata/JSON is read; no archive is downloaded again.
listing = json.load(urllib.request.urlopen(API + 'contents/' + GIT_DIRECTORY + '?ref=' + SEALED_COMMIT, timeout=45))
assert isinstance(listing, list)
entries = {entry['name']: entry for entry in listing}
assert len(entries) == len(listing)
assert entries['PARTS.json']['type'] == 'file' and entries['PARTS.json']['sha'] == PARTS_BLOB
assert entries['ROOT_ACCEPTANCE.json']['type'] == 'file' and entries['ROOT_ACCEPTANCE.json']['sha'] == ACCEPTANCE_BLOB
for part in EXPECTED_PARTS:
    entry = entries[part['file']]
    assert entry['type'] == 'file' and entry['path'] == GIT_DIRECTORY + '/' + part['file']
    assert entry['sha'] == part['git_blob'] and entry['size'] == part['bytes']
parts = git_json_blob(PARTS_BLOB)
assert parts['schema'] == 'p29_gate_full_archive_git_parts_v1'
assert parts['parts'] == EXPECTED_PARTS and sum(p['bytes'] for p in EXPECTED_PARTS) == ARCHIVE_BYTES
assert parts['bytes'] == ARCHIVE_BYTES and parts['sha256'] == ARCHIVE_SHA256
assert parts['manifest_sha256'] == MANIFEST_SHA256 and parts['members'] == 76
acceptance = git_json_blob(ACCEPTANCE_BLOB)
assert acceptance['status'] == 'ROOT_ACCEPTED_EXACT_SOURCE_NORMAL_NAMED_KERNEL_COMPLETE_OWNED_AND_ARCHIVE'
assert acceptance['module'] == 'ImbalancedChen.P2FiniteMarkedGamma5GateAffine'
assert acceptance['archive_sha256'] == ARCHIVE_SHA256 and acceptance['complete_archive_members'] == 76
assert acceptance['owned'] == 81

# The original expanded evidence must still be complete. Following this exact
# already committed manifest is the only allowed local file inventory.
manifest_path = BASE / 'FILE_MANIFEST.json'
assert file_hash(manifest_path) == MANIFEST_SHA256
manifest = json.loads(manifest_path.read_bytes())
assert len(manifest['files']) == 75 and manifest['excludes'] == ['FILE_MANIFEST.json']
protected = {str(manifest_path): snapshot(manifest_path)}
for name, expected in manifest['files'].items():
    rel = PurePosixPath(name)
    assert not rel.is_absolute() and '..' not in rel.parts and str(rel) == name
    path = BASE / name
    assert path != ARCHIVE and path.resolve() == path and path.is_relative_to(BASE)
    before = snapshot(path)
    assert before[3] == expected['bytes'] and file_hash(path) == expected['sha256']
    assert snapshot(path) == before
    protected[str(path)] = before
validation_path = BASE / 'verification/VALIDATION_RESULTS.json'
assert file_hash(validation_path) == VALIDATION_SHA256
validation = json.loads(validation_path.read_bytes())
assert validation['result'] == 'PASS_ONE_NEW_TARGET_NORMAL_NAMED_KERNEL_FULL_OWNED'
assert validation['module'] == 'ImbalancedChen.P2FiniteMarkedGamma5GateAffine' and validation['owned_count'] == 81
assert file_hash(ARCHIVE) == ARCHIVE_SHA256 and snapshot(ARCHIVE) == archive_before
for path, before in protected.items():
    assert snapshot(path) == before

space = os.statvfs('/workspace')
free_before = space.f_bavail * space.f_frsize
print(json.dumps({'stage': 'verified_one_redundant_transport_for_removal', 'path': str(ARCHIVE),
                  'bytes': ARCHIVE_BYTES, 'sha256': ARCHIVE_SHA256,
                  'sealed_commit': SEALED_COMMIT, 'sealed_parts_blob': PARTS_BLOB,
                  'sealed_root_acceptance_blob': ACCEPTANCE_BLOB,
                  'all_76_expanded_members_preserved': True,
                  'free_bytes_before': free_before}), flush=True)

# The only filesystem mutation in this script.
ARCHIVE.unlink()
assert not ARCHIVE.exists() and not ARCHIVE.is_symlink()
for path, before in protected.items():
    assert snapshot(path) == before
assert file_hash(manifest_path) == MANIFEST_SHA256
space = os.statvfs('/workspace')
print(json.dumps({'schema': 'p29_single_redundant_gate_transport_cleanup_v1',
                  'status': 'REMOVED_ONLY_VERIFIED_REDUNDANT_GATE_TRANSPORT',
                  'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'removed_path': str(ARCHIVE), 'removed_bytes': ARCHIVE_BYTES,
                  'removed_sha256': ARCHIVE_SHA256, 'protected_expanded_files': len(protected),
                  'all_original_expanded_evidence_source_object_logs_unchanged': True,
                  'git_parts_unchanged': EXPECTED_PARTS,
                  'free_bytes_before': free_before,
                  'free_bytes_after': space.f_bavail * space.f_frsize,
                  'other_deletions': 0, 'Lean_invocations': 0,
                  'old_kernel_owned_replays': 0, 'new_proof_credit': 0,
                  'cleanup_script_sha256': hashlib.sha256(SOURCE_TEXT.encode()).hexdigest()}), flush=True)
