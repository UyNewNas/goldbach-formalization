#!/usr/bin/env python3
"""Lossless carriers for three large evidence names; restore into a NEW directory.

No Lean, Lake, kernel, shell, network, source editing, or proof interpretation.
"""
import argparse
from contextlib import contextmanager
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import secrets
import stat

MIN_BYTES = 50 * 1024**2
MAX_CARRIER_BYTES = 100 * 1024**2
MAX_MANIFEST_BYTES = 1024**2
CHUNK = 1024**2
NAMES = frozenset({'OWNED_EXPORTS.json', 'PUBLIC_EXPORTS.json', 'types-axioms.log'})
SCHEMA = 'lossless_large_evidence_carriers_v1'
DIRECTORY_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def require(condition, message):
    if not condition:
        raise ValueError(message)


def relative_path(value):
    require(isinstance(value, str) and value and '\\' not in value
            and ':' not in value and '\0' not in value, 'Invalid relative artifact path')
    rel = PurePosixPath(value)
    require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == value
            and value != '.', 'Artifact path traversal or noncanonical spelling')
    return Path(*rel.parts)


def check_record(record):
    relative_path(record['path'])
    require(type(record['bytes']) is int and record['bytes'] >= 0, 'Invalid artifact byte count')
    digest = record['sha256']
    require(isinstance(digest, str) and len(digest) == 64
            and all(c in '0123456789abcdef' for c in digest), 'Invalid SHA256')


def is_large_evidence(record):
    check_record(record)
    return relative_path(record['path']).name in NAMES and record['bytes'] > MIN_BYTES


@contextmanager
def directory_fd(path, create=False):
    """Walk absolute directories through pinned descriptors, never symlinks."""
    path = Path(path)
    require('..' not in path.parts, 'Parent traversal in directory path')
    path = path.absolute()
    fd = os.open(path.anchor, DIRECTORY_FLAGS)
    try:
        for part in path.parts[1:]:
            try:
                nxt = os.open(part, DIRECTORY_FLAGS, dir_fd=fd)
            except FileNotFoundError:
                if not create:
                    raise
                try:
                    os.mkdir(part, mode=0o700, dir_fd=fd)
                except FileExistsError:
                    pass
                nxt = os.open(part, DIRECTORY_FLAGS, dir_fd=fd)
            os.close(fd)
            fd = nxt
        yield fd
    finally:
        os.close(fd)


@contextmanager
def regular_file(path):
    path = Path(path)
    with directory_fd(path.parent) as parent:
        fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
    try:
        require(stat.S_ISREG(os.fstat(fd).st_mode), 'Expected a regular file')
        with os.fdopen(fd, 'rb') as stream:
            fd = None
            yield stream
    finally:
        if fd is not None:
            os.close(fd)


def digest_stream(stream, max_bytes=None):
    total, h = 0, hashlib.sha256()
    while data := stream.read(CHUNK):
        total += len(data)
        require(max_bytes is None or total <= max_bytes, 'Compressed input exceeds expected maximum')
        h.update(data)
    return total, h.hexdigest()


def digest_file(path):
    with regular_file(path) as stream:
        return digest_stream(stream)


def validate_raw(source, record):
    require(is_large_evidence(record), 'Only the three >50MiB evidence names are supported')
    require(digest_file(Path(source) / relative_path(record['path']))
            == (record['bytes'], record['sha256']), 'Raw evidence size/SHA mismatch')


def atomic_new(path, writer):
    """Publish a complete verified file with link(O_EXCL semantics), no clobber."""
    path = Path(path)
    with directory_fd(path.parent, create=True) as parent:
        temporary = '.lossless-' + secrets.token_hex(16)
        fd = os.open(temporary, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     mode=0o600, dir_fd=parent)
        try:
            with os.fdopen(fd, 'w+b') as stream:
                result = writer(stream)
                stream.flush()
                os.fsync(stream.fileno())
            os.link(temporary, path.name, src_dir_fd=parent, dst_dir_fd=parent,
                    follow_symlinks=False)
            return result
        finally:
            os.unlink(temporary, dir_fd=parent)


def verify_gzip(stream, raw, output=None):
    """Bound expansion to the exact expected raw count and check full CRC/SHA."""
    stream.seek(0)
    require(stream.read(8) == b'\x1f\x8b\x08\x00\x00\x00\x00\x00',
            'Carrier must use gzip filename-empty/mtime-zero header')
    stream.seek(0)
    total, h = 0, hashlib.sha256()
    with gzip.GzipFile(fileobj=stream, mode='rb') as decoded:
        while data := decoded.read(min(CHUNK, raw['bytes'] - total + 1)):
            total += len(data)
            require(total <= raw['bytes'], 'Decompressed evidence exceeds expected byte limit')
            h.update(data)
            if output is not None:
                output.write(data)
    require((total, h.hexdigest()) == (raw['bytes'], raw['sha256']),
            'Decompressed evidence size/SHA mismatch')


def checked_carrier(path, raw, expected=None):
    with regular_file(path) as stream:
        require(os.fstat(stream.fileno()).st_size <= MAX_CARRIER_BYTES,
                'Carrier still exceeds the GitHub file limit')
        size, digest = digest_stream(stream, MAX_CARRIER_BYTES)
        require(size <= MAX_CARRIER_BYTES, 'Carrier still exceeds the GitHub file limit')
        if expected is not None:
            check_record(expected)
            require((size, digest) == (expected['bytes'], expected['sha256']),
                    'Compressed carrier size/SHA mismatch')
        verify_gzip(stream, raw)
    return {'path': raw['path'] + '.gz', 'bytes': size, 'sha256': digest}


def preflight_destination(destination, record):
    require(is_large_evidence(record), 'Unsupported evidence carrier')
    raw = Path(destination) / relative_path(record['path'])
    try:
        with regular_file(raw):
            pass
    except FileNotFoundError:
        pass
    else:
        raise ValueError('Large raw destination already exists; it is never deleted or replaced')
    try:
        return checked_carrier(raw.with_name(raw.name + '.gz'), record)
    except FileNotFoundError:
        return None


def create_carrier(source, destination, record):
    require(is_large_evidence(record), 'Unsupported evidence carrier')
    existing = preflight_destination(destination, record)
    if existing is not None:
        validate_raw(source, record)
        return {'raw': dict(record), 'carrier': existing, 'format': 'gzip',
                'gzip_filename': '', 'gzip_mtime': 0}
    carrier_path = Path(destination) / (record['path'] + '.gz')

    def compress(stream):
        total, h = 0, hashlib.sha256()
        with regular_file(Path(source) / relative_path(record['path'])) as original:
            with gzip.GzipFile(filename='', mode='wb', compresslevel=9,
                               fileobj=stream, mtime=0) as encoded:
                while data := original.read(CHUNK):
                    total += len(data)
                    require(total <= record['bytes'], 'Raw evidence grew during compression')
                    h.update(data)
                    encoded.write(data)
        require((total, h.hexdigest()) == (record['bytes'], record['sha256']),
                'Raw evidence changed or has wrong size/SHA')
        stream.flush()
        stream.seek(0)
        size, digest = digest_stream(stream)
        require(size <= MAX_CARRIER_BYTES, 'Compressed evidence exceeds GitHub file limit')
        verify_gzip(stream, record)  # Gzip writer is closed before this full independent decode.
        return {'path': record['path'] + '.gz', 'bytes': size, 'sha256': digest}

    carrier = atomic_new(carrier_path, compress)
    return {'raw': dict(record), 'carrier': carrier, 'format': 'gzip',
            'gzip_filename': '', 'gzip_mtime': 0}


def write_exact_new_or_identical(path, data):
    try:
        current = digest_file(path)
    except FileNotFoundError:
        atomic_new(path, lambda stream: stream.write(data))
    else:
        require(current == (len(data), hashlib.sha256(data).hexdigest()),
                'Existing publication metadata differs')


def finish_publication(destination, rows, publication_sha256, actual_small_files):
    require(rows, 'Lossless manifest requires actual carriers')
    helper_path = Path(__file__)
    with regular_file(helper_path) as stream:
        helper = stream.read()
    helper_record = {'path': 'restore_lossless_evidence.py', 'bytes': len(helper),
                     'sha256': hashlib.sha256(helper).hexdigest()}
    metadata = {'schema': SCHEMA, 'original_publication_manifest_sha256': publication_sha256,
                'artifacts': rows, 'restore_helper': helper_record,
                'raw_paths_in_original_manifest_require_restoration': True,
                'raw_files_are_not_published_at_their_original_repository_paths': True,
                'raw_evidence_unchanged_and_independent_gzip_roundtrip_verified': True}
    payload = (json.dumps(metadata, indent=2, ensure_ascii=False) + '\n').encode()
    ledger = {'path': 'LOSSLESS_ARTIFACTS.json', 'bytes': len(payload),
              'sha256': hashlib.sha256(payload).hexdigest()}
    write_exact_new_or_identical(Path(destination) / helper_record['path'], helper)
    write_exact_new_or_identical(Path(destination) / ledger['path'], payload)
    return {'lossless_artifacts': ledger,
            'original_manifest_paths_present_in_repository_destination': False,
            'original_manifest_identity_scope': 'Unchanged raw source evidence; compressed raw paths require restoration.',
            'raw_paths_requiring_restoration': [r['raw']['path'] for r in rows],
            'actual_repository_files': list(actual_small_files)
                + [r['carrier'] for r in rows] + [helper_record, ledger]}


def restore(manifest_path, output_dir, *, max_total_bytes=2 * 1024**3):
    require(type(max_total_bytes) is int and max_total_bytes > 0, 'Invalid maximum expected raw bytes')
    manifest_path = Path(manifest_path)
    with regular_file(manifest_path) as stream:
        require(os.fstat(stream.fileno()).st_size <= MAX_MANIFEST_BYTES,
                'Lossless mapping metadata is too large')
        payload = stream.read(MAX_MANIFEST_BYTES + 1)
        require(len(payload) <= MAX_MANIFEST_BYTES, 'Lossless metadata grew beyond its limit')
        metadata = json.loads(payload)
    require(metadata['schema'] == SCHEMA, 'Unsupported lossless artifact manifest')
    rows = metadata['artifacts']
    require(isinstance(rows, list) and rows, 'Missing lossless artifacts')
    seen, total = set(), 0
    for row in rows:
        raw, carrier = row['raw'], row['carrier']
        require(is_large_evidence(raw), 'Unsupported raw artifact name or size')
        check_record(carrier)
        require(carrier['path'] == raw['path'] + '.gz' and row['format'] == 'gzip'
                and row['gzip_filename'] == '' and row['gzip_mtime'] == 0,
                'Wrong carrier mapping or compression parameters')
        require(raw['path'] not in seen, 'Duplicate restored artifact')
        seen.add(raw['path'])
        total += raw['bytes']
        require(total <= max_total_bytes, 'Expected raw bytes exceed configured maximum')
        checked_carrier(manifest_path.parent / relative_path(carrier['path']), raw, carrier)
    output_dir = Path(output_dir)
    require('..' not in output_dir.parts, 'Restore output directory traversal')
    with directory_fd(output_dir.parent) as parent:
        os.mkdir(output_dir.name, mode=0o700, dir_fd=parent)  # NEW only, no existing dir/symlink.
    for row in rows:
        raw, carrier = row['raw'], row['carrier']

        def decode(output):
            with regular_file(manifest_path.parent / relative_path(carrier['path'])) as encoded:
                require(digest_stream(encoded, MAX_CARRIER_BYTES) == (carrier['bytes'], carrier['sha256']),
                        'Carrier changed after preflight')
                verify_gzip(encoded, raw, output)

        atomic_new(output_dir / relative_path(raw['path']), decode)
    return {'restored_files': len(rows), 'restored_bytes': total,
            'new_output_directory': str(output_dir), 'no_formal_tools_executed': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest', required=True)
    ap.add_argument('--output-dir', required=True, help='A NEW directory; never overwrite existing files')
    ap.add_argument('--max-total-bytes', type=int, default=2 * 1024**3)
    args = ap.parse_args()
    print(json.dumps(restore(args.manifest, args.output_dir, max_total_bytes=args.max_total_bytes)))


if __name__ == '__main__':
    main()
