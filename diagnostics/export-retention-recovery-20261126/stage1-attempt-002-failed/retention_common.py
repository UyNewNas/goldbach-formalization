from __future__ import annotations
import ast
import gzip
import hashlib
import io
import json
import math
import os
from pathlib import Path
import stat
import subprocess
import sys
import tarfile
import types
import zlib

WORKTREE = Path('/workspace/p2-4-compact-proof-20261125')
ORIGINAL = WORKTREE / '.lake/p24-audit-export/source6e-full324-preflight-001/all.tar.gz'
MANIFEST = ORIGINAL.with_name('manifest.json')
NATIVE = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169')
OUTPUT = Path('/workspace/p24-export-retention-20261126/attempt-001')
EXPORTER = WORKTREE / 'verification/part2/export_winner9_private_evidence.py'
EXPORTER_SHA = 'fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645'
ORIGINAL_SHA = '3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463'
ORIGINAL_BYTES = 581735403
MANIFEST_SHA = '7a99f246b4c8bc54bc55ce3497de1445a270d76a34ce6af0a2e1b8e1f5e1e934'
MANIFEST_BYTES = 11997843
SOURCE_PIN = '6e616f4e0372555f7a78bcdba3e198d0e277eec8'
REGISTRY_SHA = '64cb804725e2a497fbe11be56506fbf30cdf3be087f3bcdf2c51fe3935d6f0f6'
FILE_INDEX_COUNT = 13855
FILE_INDEX_BYTES = 4295883531
PACKAGE_MANIFEST_BYTES = 6767012
MEMBER_COUNT = FILE_INDEX_COUNT + 1
MEMBER_BYTES = FILE_INDEX_BYTES + PACKAGE_MANIFEST_BYTES
NATIVE_COUNT = 1752
NATIVE_BYTES = 4089256851
PRESERVED_COUNT = FILE_INDEX_COUNT - NATIVE_COUNT + 1
PRESERVED_BYTES = FILE_INDEX_BYTES - NATIVE_BYTES + PACKAGE_MANIFEST_BYTES
RESERVE = 32 * 1024 * 1024

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for data in iter(lambda: f.read(1048576), b''):
            h.update(data)
    return h.hexdigest()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()

def fsync_dir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)

def write_new(path, data):
    with Path(path).open('xb') as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())

def runtime():
    return {'python': sys.version, 'zlib_runtime': zlib.ZLIB_RUNTIME_VERSION,
            'zlib_compiled': zlib.ZLIB_VERSION, 'gzip_module_sha256': digest(gzip.__file__),
            'tarfile_module_sha256': digest(tarfile.__file__)}

def load_original_package(path):
    path = Path(path)
    require(digest(path) == EXPORTER_SHA, 'Original exporter hash changed')
    tree = ast.parse(path.read_text())
    selected = []
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.module == '__future__':
            selected.append(node)
        elif isinstance(node, ast.Assign) and any(isinstance(x, ast.Name) and x.id == 'TEXT_SUFFIXES' for x in node.targets):
            selected.append(node)
        elif isinstance(node, ast.FunctionDef) and node.name in {'encoded', 'sha_bytes', 'package'}:
            selected.append(node)
        elif isinstance(node, ast.ClassDef) and node.name == 'Evidence':
            selected.append(node)
    require(len(selected) == 6, 'Unexpected original exporter definitions')
    env = dict(Path=Path, hashlib=hashlib, gzip=gzip, io=io, json=json, math=math,
               tarfile=tarfile, require=require, digest=digest)
    # Exact original function/class AST; no exporter main/receipt selector runs.
    exec(compile(ast.Module(body=selected, type_ignores=[]), str(path), 'exec'), env)
    return types.SimpleNamespace(**{name: env[name] for name in ['encoded', 'Evidence', 'package']})

def native_members(index):
    native = {}
    real_root = NATIVE.resolve(strict=True)
    for name, record in index.items():
        origin = Path(record['origin'])
        if not origin.is_absolute() or not origin.is_relative_to(NATIVE):
            continue
        require(origin.resolve(strict=True).is_relative_to(real_root), 'Native origin escapes exact qualified root: ' + str(origin))
        require(stat.S_ISREG(origin.stat().st_mode), 'Native origin is not a regular file')
        native[name] = record
    require(len(native) == NATIVE_COUNT, 'Unexpected native member count')
    require(sum(x['bytes'] for x in native.values()) == NATIVE_BYTES, 'Unexpected native member bytes')
    return native

def verify_native(native):
    shared_links = []
    symlinks = []
    for name, record in native.items():
        p = Path(record['origin'])
        require(p.is_relative_to(NATIVE) and p.resolve(strict=True).is_relative_to(NATIVE.resolve(strict=True)), 'Native path containment changed')
        s = p.stat()
        require(stat.S_ISREG(s.st_mode) and s.st_size == record['bytes'] and digest(p) == record['sha256'], 'Native bytes changed: ' + str(p))
        if s.st_nlink > 1:
            shared_links.append(str(p))
        if p.is_symlink():
            symlinks.append(str(p))
    return {'count': len(native), 'bytes': sum(x['bytes'] for x in native.values()),
            'index_sha256': sha(encoded(native)), 'all_bytes_and_sha256_verified': True,
            'hardlink_count_greater_than_one': len(shared_links), 'symlink_origin_count': len(symlinks),
            'hardlink_paths': sorted(set(shared_links)), 'symlink_paths': sorted(set(symlinks))}

def current_inputs():
    return {'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=WORKTREE, text=True).strip(),
            'registry_sha256': digest(WORKTREE / '.lake/p2-private/records.json'),
            'original_archive_sha256': digest(ORIGINAL), 'original_archive_bytes': ORIGINAL.stat().st_size,
            'original_manifest_sha256': digest(MANIFEST), 'original_manifest_bytes': MANIFEST.stat().st_size,
            'exporter_sha256': digest(EXPORTER)}

def assert_original_bindings(state):
    require(state['git_head'] == SOURCE_PIN and state['registry_sha256'] == REGISTRY_SHA, 'Current source/registry differs from authorized snapshot')
    require(state['original_archive_sha256'] == ORIGINAL_SHA and state['original_archive_bytes'] == ORIGINAL_BYTES, 'Wrong original archive')
    require(state['original_manifest_sha256'] == MANIFEST_SHA and state['original_manifest_bytes'] == MANIFEST_BYTES, 'Wrong original manifest')
    require(state['exporter_sha256'] == EXPORTER_SHA, 'Wrong original exporter')

def check_outer(manifest):
    require(manifest['split'] == 'all' and len(manifest['packages']) == 1, 'Expected original all package')
    package = manifest['packages'][0]
    require(Path(package['path']) == ORIGINAL and package['sha256'] == ORIGINAL_SHA and package['bytes'] == ORIGINAL_BYTES, 'Outer package binding differs')
    require(len(manifest['files']) == FILE_INDEX_COUNT, 'Wrong original file index size')
    require(sum(x['bytes'] for x in manifest['files'].values()) == FILE_INDEX_BYTES, 'Wrong original file index bytes')
    require(package['uncompressed_payload_bytes'] == MEMBER_BYTES, 'Wrong full original package payload bytes')
    return package

def package_index(manifest):
    package = check_outer(manifest)
    return {'package': ORIGINAL.name, 'modules': package['modules'], 'files': manifest['files'],
            'no_olean_objects': True, 'diagnostic_files_grant_no_proof_credit': True}

def original_index(manifest, original_package_bytes):
    require(len(original_package_bytes) == PACKAGE_MANIFEST_BYTES, 'Original PACKAGE_MANIFEST byte count differs')
    require(json.loads(original_package_bytes) == package_index(manifest), 'Original PACKAGE_MANIFEST differs')
    require(original_package_bytes == encoded(package_index(manifest)), 'Original PACKAGE_MANIFEST bytes differ')
    result = dict(manifest['files'])
    result['PACKAGE_MANIFEST.json'] = {'bytes': len(original_package_bytes), 'sha256': sha(original_package_bytes),
                                      'origin': 'original generated package manifest', 'role': 'original package index'}
    require(len(result) == MEMBER_COUNT and sum(x['bytes'] for x in result.values()) == MEMBER_BYTES, 'Original member inventory/bytes differ')
    return result

def verify_tar(path, expected, keep=None):
    kept, seen = {}, set()
    with tarfile.open(path, mode='r|gz') as archive:
        for member in archive:
            require(member.isfile() and member.name in expected and member.name not in seen, 'Unexpected/duplicate tar member: ' + member.name)
            record = expected[member.name]
            require(member.size == record['bytes'], 'Tar member size differs')
            f = archive.extractfile(member)
            require(f is not None, 'Unreadable tar member')
            h = hashlib.sha256(); n = 0; chunks = []
            with f:
                for data in iter(lambda: f.read(1048576), b''):
                    h.update(data); n += len(data)
                    if keep is not None and member.name in keep:
                        chunks.append(data)
            require(n == record['bytes'] and h.hexdigest() == record['sha256'], 'Tar member SHA differs: ' + member.name)
            if keep is not None and member.name in keep:
                kept[member.name] = b''.join(chunks)
            seen.add(member.name)
    require(seen == set(expected), 'Tar member coverage incomplete')
    return kept

def read_bundle(path, expected_sha, keep_all=False):
    require(digest(path) == expected_sha, 'Persistent bundle digest differs')
    with tarfile.open(path, mode='r|gz') as archive:
        first = next(iter(archive))
        require(first.name == 'PACKAGE_MANIFEST.json' and first.isfile(), 'Missing bundle package index')
        f = archive.extractfile(first); require(f is not None, 'Missing bundle index data')
        raw = f.read(); index = json.loads(raw)
    expected = dict(index['files'])
    expected['PACKAGE_MANIFEST.json'] = {'bytes': len(raw), 'sha256': sha(raw)}
    keep = set(index['files']) if keep_all else {name for name in index['files'] if name.startswith('metadata/')}
    return index, verify_tar(path, expected, keep), expected
