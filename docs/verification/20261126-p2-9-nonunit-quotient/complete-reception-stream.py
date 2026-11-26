from pathlib import Path, PurePosixPath
import hashlib, json, lzma, tarfile

B = Path('/dev/shm/p29-nonunit002-reception')
archive = B / 'nonunit-quotient-complete.tar.xz'
expanded = B / 'complete'
assert not archive.exists() and not expanded.exists()
part_receipts = [json.loads((B / f'PART0{i}_RECEPTION.json').read_text()) for i in [0, 1]]
expected_git = ['22d75e4be9b4cc6e952152d3a67df0ff1a2eb736', '619b78086a953ea6a10c9a202fb373e88fbd1e0d']
h = hashlib.sha256()
total = 0
with archive.open('xb') as dst:
    for i, rec in enumerate(part_receipts):
        assert rec['part_git_blob'] == expected_git[i]
        assert rec['metadata']['part_index'] == i
        assert rec['metadata']['offset'] == total
        ph = hashlib.sha256()
        size = 0
        with Path(rec['part_path']).open('rb') as src:
            while block := src.read(1048576):
                dst.write(block)
                h.update(block)
                ph.update(block)
                size += len(block)
        assert size == rec['part_bytes']
        assert ph.hexdigest() == rec['part_sha256']
        total += size
assert total == 7419000
assert h.hexdigest() == '9db6e95658f7be4377b04f5affa0687df88dce03552863389d8696c6d24641bc'

class CountingReader:
    def __init__(self, source):
        self.source = source
        self.digest = hashlib.sha256()
        self.bytes = 0
    def read(self, n=-1):
        data = self.source.read(n)
        self.digest.update(data)
        self.bytes += len(data)
        return data

expanded.mkdir()
members = []
member_results = {}
manifest = None
manifest_sha = None
with lzma.open(archive, 'rb') as decompressed:
    reader = CountingReader(decompressed)
    with tarfile.open(fileobj=reader, mode='r|') as tar:
        for member in tar:
            name = member.name
            posix = PurePosixPath(name)
            assert member.isfile() and not posix.is_absolute()
            assert '..' not in posix.parts and str(posix) == name
            assert name not in member_results
            destination = expanded / name
            assert destination.resolve().is_relative_to(expanded.resolve())
            destination.parent.mkdir(parents=True, exist_ok=True)
            fh = hashlib.sha256()
            size = 0
            with tar.extractfile(member) as src, destination.open('xb') as dst:
                while block := src.read(1048576):
                    dst.write(block)
                    fh.update(block)
                    size += len(block)
            assert size == member.size
            value = {'bytes': size, 'sha256': fh.hexdigest()}
            if name == 'COMPLETE_MEMBERS.json':
                assert manifest is None and not members
                assert size == 12608
                assert fh.hexdigest() == '9a0cf3eae96fb78bd63d46e4b9df6e68346c03ecaea50a498020ae11675e9de9'
                manifest = json.loads(destination.read_text())
                manifest_sha = fh.hexdigest()
                assert len(manifest) == 80
            else:
                assert manifest is not None and manifest[name] == value, (name, value)
            member_results[name] = value
            members.append(name)
    while reader.read(1048576):
        pass
    tar_bytes = reader.bytes
    tar_sha256 = reader.digest.hexdigest()
assert len(members) == len(set(members)) == 81
assert set(member_results) == set(manifest) | {'COMPLETE_MEMBERS.json'}

small = B / 'small'
small_matches = []
for path in sorted(small.rglob('*')):
    if not path.is_file():
        continue
    relative = str(path.relative_to(small))
    name = 'COMPLETE_MEMBERS.json' if relative == 'portable/COMPLETE_MEMBERS.json' else 'evidence/' + relative
    value = {'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    assert member_results[name] == value
    small_matches.append(relative)
assert len(small_matches) == 12

source = expanded / 'project/ImbalancedChen/P2FiniteMarkedGamma5NonunitQuotient.lean'
obj = expanded / 'project/.lake/build/lib/lean/ImbalancedChen/P2FiniteMarkedGamma5NonunitQuotient.olean'
def identity(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}
source_identity = identity(source)
object_identity = identity(obj)
assert source_identity['bytes'] == 3431
assert source_identity['git_blob'] == 'eeaf7a2c714da44928cc43e79780846e1e72d23b'
assert source_identity['sha256'] == '42de161d084cac904775203fb0188bcc7bc5459a9b230b53c5c405e692262d77'
assert object_identity['bytes'] == 210800
assert object_identity['sha256'] == '86ade819d9ae33358ea6ea00b419c4ddfb6727b28637145c45b1ca412a849eb8'
receipt = {
    'schema': 'p29_nonunit_quotient_002_complete_original_archive_reception_v1',
    'status': 'PASS_TRANSPORT_AND_ALL_81_MEMBER_HASHES_ROOT_QUALIFICATION_PENDING',
    'compile_job': 'job_7cf32d1b62054782911b4fc114699b7e',
    'compile_controller_blob': 'd99a7bf077d05c7c7b6b5205c1fa717edfd98642',
    'readonly_exporter_blob': 'e804e56c88058d60d82763e7286555c575100ba9',
    'source': source_identity,
    'object': object_identity,
    'archive': {'path': str(archive), 'bytes': total, 'sha256': h.hexdigest(), 'original_remote_archive_bytes_unchanged': True},
    'tar': {'bytes': tar_bytes, 'sha256': tar_sha256, 'repacked': False},
    'expanded_root': str(expanded),
    'members': 81,
    'manifest_entries': 80,
    'manifest_sha256': manifest_sha,
    'all_regular_safe_unique_members': True,
    'all_member_bytes_and_sha256_match_original_manifest': True,
    'small_original_files_exactly_match_complete_archive': small_matches,
    'parts': [{k: rec[k] for k in ['job_id', 'stdout_bytes', 'stdout_sha256', 'page_count', 'part_path', 'part_bytes', 'part_sha256', 'part_git_blob', 'all_ranges_contiguous_once']} for rec in part_receipts],
    'total_pages_received_once': 313,
    'all_pages_untruncated_contiguous_with_saved_hashes': True,
    'normal_warning_as_error_requested': False,
    'normal_warning_count_from_original_normal_log': 3,
    'old_Core_19_Upper_11_new_credit': 0,
    'Lean_calls_in_reception': 0,
    'proof_parser_reruns_in_reception': 0,
    'root_qualification_verifier_run_here': False,
    'member_hashes': member_results,
}
target = B / 'NONUNIT_QUOTIENT_002_COMPLETE_RECEPTION.json'
text = json.dumps(receipt, indent=2) + '\n'
target.write_text(text)
Path('/workspace/scratch/005887317b49/p29-current/NONUNIT_QUOTIENT_002_COMPLETE_RECEPTION.json').write_text(text)
print(json.dumps({k: v for k, v in receipt.items() if k != 'member_hashes'}, indent=2))
