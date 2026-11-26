#!/usr/bin/env python3
"""Rebuild and verify the exact full2048 diagnostic archive from three parts."""
from __future__ import annotations

import argparse
import hashlib
import json
import lzma
from pathlib import Path
import tarfile


def hashes(path: Path) -> tuple[int, str, str]:
    size = path.stat().st_size
    sha = hashlib.sha256()
    git = hashlib.sha1(f'blob {size}\0'.encode())
    actual_size = 0
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            actual_size += len(data)
            sha.update(data)
            git.update(data)
    assert actual_size == size
    return size, sha.hexdigest(), git.hexdigest()


class DigestReader:
    def __init__(self, source):
        self.source = source
        self.sha = hashlib.sha256()
        self.bytes = 0

    def read(self, size=-1):
        data = self.source.read(size)
        self.sha.update(data)
        self.bytes += len(data)
        return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=Path(__file__).with_name('archive-parts-manifest.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    manifest = json.loads(manifest_path.read_text())
    directory = manifest_path.parent
    output = args.output or directory / manifest['archive_file']
    parts = manifest['parts']
    assert manifest['part_count'] == len(parts) == 3
    assert [part['index'] for part in parts] == [1, 2, 3]
    paths = []
    offset = 0
    for part in parts:
        relative = Path(part['file'])
        assert not relative.is_absolute() and '..' not in relative.parts
        path = directory / relative
        assert part['offset'] == offset
        assert hashes(path) == (part['bytes'], part['sha256'], part['git_blob_sha'])
        paths.append(path)
        offset += part['bytes']
    assert offset == manifest['archive_bytes']
    if not output.exists():
        with output.open('xb') as destination:
            for path in paths:
                with path.open('rb') as source:
                    for data in iter(lambda: source.read(1048576), b''):
                        destination.write(data)
    size, sha, _ = hashes(output)
    assert size == manifest['archive_bytes'] and sha == manifest['archive_sha256']

    expected = manifest['raw_evidence_files']
    seen = {}
    internal_manifest = None
    with lzma.open(output, 'rb') as source:
        reader = DigestReader(source)
        with tarfile.open(fileobj=reader, mode='r|') as archive:
            for member in archive:
                assert member.isfile() and member.name not in seen
                assert member.name in set(expected) | {'manifest.json'}
                stream = archive.extractfile(member)
                assert stream is not None
                member_hash = hashlib.sha256()
                member_bytes = 0
                small_manifest = bytearray()
                with stream:
                    for data in iter(lambda: stream.read(1048576), b''):
                        member_hash.update(data)
                        member_bytes += len(data)
                        if member.name == 'manifest.json':
                            small_manifest.extend(data)
                assert member_bytes == member.size
                seen[member.name] = {'bytes': member_bytes, 'sha256': member_hash.hexdigest()}
                if member.name == 'manifest.json':
                    internal_manifest = json.loads(small_manifest)
        while reader.read(1048576):
            pass
        assert reader.bytes == manifest['uncompressed_tar_bytes']
        assert reader.sha.hexdigest() == manifest['uncompressed_tar_sha256']
    assert internal_manifest == expected
    assert len(seen) == 10 and set(seen) == set(expected) | {'manifest.json'}
    assert {name: seen[name] for name in expected} == expected
    print(json.dumps({
        'verified': True, 'diagnostic_only': True, 'finite_A_credit': False, 'full324_credit': False,
        'archive_path': str(output), 'archive_bytes': size, 'archive_sha256': sha,
        'uncompressed_tar_bytes': reader.bytes, 'uncompressed_tar_sha256': reader.sha.hexdigest(),
        'parts_verified': len(parts), 'raw_evidence_files_verified': len(expected), 'tar_members_verified': len(seen),
    }, sort_keys=True))


if __name__ == '__main__':
    main()
