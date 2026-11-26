set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
p24_retention_stage_dir=$(mktemp -d /tmp/p24-retention-inputs-XXXXXX)
cat > "$p24_retention_stage_dir/retention_common.py" <<'P24_RETENTION_SOURCE_0_EOF'
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
MEMBER_COUNT = 13855
MEMBER_BYTES = 4295883531
NATIVE_COUNT = 1752
NATIVE_BYTES = 4089256851
PRESERVED_COUNT = 12103
PRESERVED_BYTES = 206626680
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
    require(len(manifest['files']) + 1 == MEMBER_COUNT, 'Wrong original file index size')
    return package

def package_index(manifest):
    package = check_outer(manifest)
    return {'package': ORIGINAL.name, 'modules': package['modules'], 'files': manifest['files'],
            'no_olean_objects': True, 'diagnostic_files_grant_no_proof_credit': True}

def original_index(manifest, original_package_bytes):
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
P24_RETENTION_SOURCE_0_EOF
cat > "$p24_retention_stage_dir/stage1_preserve.py" <<'P24_RETENTION_SOURCE_1_EOF'
from __future__ import annotations
import json
import os
from pathlib import Path
import shutil
import tempfile
from retention_common import *

def main():
    require(not OUTPUT.exists(), 'Use a new persistent retention directory')
    before = current_inputs(); assert_original_bindings(before)
    manifest_raw = MANIFEST.read_bytes(); manifest = json.loads(manifest_raw)
    package = check_outer(manifest)
    exporter = load_original_package(EXPORTER)
    original_package_bytes = exporter.encoded(package_index(manifest))
    originals = original_index(manifest, original_package_bytes)
    native = native_members(manifest['files'])
    preserved = {name: row for name, row in originals.items() if name not in native}
    require(len(preserved) == PRESERVED_COUNT and sum(x['bytes'] for x in preserved.values()) == PRESERVED_BYTES, 'Wrong preserved member selection')
    print(json.dumps({'phase': 'original_archive_stream_verify', 'member_count': len(originals), 'preserved_members': len(preserved), 'native_members': len(native)}), flush=True)
    preserved_data = verify_tar(ORIGINAL, originals, set(preserved))
    native_before = verify_native(native)
    evidence = exporter.Evidence()
    for name, raw in preserved_data.items():
        evidence.add_bytes('members/' + name, raw, str(ORIGINAL) + '#' + name, 'lossless original non-native member; no new proof credit')
    inputs = {'schema': 1, 'diagnostic_only': True, 'no_new_acceptance_credit': True,
              'original_archive_path': str(ORIGINAL), 'original_archive_bytes': ORIGINAL_BYTES, 'original_archive_sha256': ORIGINAL_SHA,
              'original_manifest_path': str(MANIFEST), 'original_manifest_bytes': MANIFEST_BYTES, 'original_manifest_sha256': MANIFEST_SHA,
              'original_exporter_sha256': EXPORTER_SHA, 'immutable_native_root': str(NATIVE),
              'compression_runtime': runtime(), 'original_member_count': MEMBER_COUNT, 'original_member_bytes': MEMBER_BYTES,
              'native_members': native, 'preserved_members': preserved, 'native_verification_before': native_before,
              'original_modules': package['modules'], 'transfer_page_bytes': manifest['transfer_page_bytes']}
    evidence.add_bytes('metadata/original-export-manifest.json', manifest_raw, str(MANIFEST), 'exact original outer manifest')
    evidence.add_bytes('metadata/original-exporter.py', EXPORTER.read_bytes(), str(EXPORTER), 'exact original exporter source')
    evidence.add_bytes('metadata/reconstruction-inputs.json', exporter.encoded(inputs), 'generated retention index', 'reconstruction mapping only; no proof credit')
    temporary = Path(tempfile.mkdtemp(prefix='p24-retention-stage1-'))
    trial = temporary / 'preserved-members.tar.gz'
    info = exporter.package(trial, set(evidence.files), package['modules'], evidence, manifest['transfer_page_bytes'])
    expected_bundle = dict(evidence.file_index())
    expected_index_bytes = exporter.encoded({'package': trial.name, 'modules': package['modules'], 'files': evidence.file_index(),
                                            'no_olean_objects': True, 'diagnostic_files_grant_no_proof_credit': True})
    expected_bundle['PACKAGE_MANIFEST.json'] = {'bytes': len(expected_index_bytes), 'sha256': sha(expected_index_bytes)}
    verify_tar(trial, expected_bundle)
    recipe_names = ['retention_common.py', 'stage1_preserve.py', 'rebuild_original_export.py']
    metadata_budget = (sum(Path(__file__).with_name(name).stat().st_size for name in recipe_names)
                       + EXPORTER.stat().st_size + len(encoded(native_before))
                       + 2 * len(encoded(before)) + 65536)
    free = shutil.disk_usage('/workspace').free
    require(free >= info['bytes'] + metadata_budget + RESERVE, 'Trial bundle does not fit with 32 MiB persistent reserve')
    # No persistent outputs exist until exact trial size and full contents pass.
    OUTPUT.mkdir(parents=True, exist_ok=False)
    pending = OUTPUT / 'preserved-members.pending'
    with trial.open('rb') as source, pending.open('xb') as destination:
        shutil.copyfileobj(source, destination, 1048576)
        destination.flush(); os.fsync(destination.fileno())
    require(pending.stat().st_size == info['bytes'] and digest(pending) == info['sha256'], 'Persistent bundle copy differs')
    final = OUTPUT / trial.name
    pending.rename(final); fsync_dir(OUTPUT)
    verify_tar(final, expected_bundle)
    for name in recipe_names:
        write_new(OUTPUT / name, Path(__file__).with_name(name).read_bytes())
    write_new(OUTPUT / 'original-exporter.py', EXPORTER.read_bytes())
    native_after = verify_native(native)
    after = current_inputs(); require(after == before, 'Original inputs changed during preservation')
    require(native_after == native_before, 'Shared native input bindings changed')
    require(shutil.disk_usage('/workspace').free >= RESERVE, 'Persistent free space below 32 MiB reserve')
    receipt = {'schema': 1, 'stage1_passed': True, 'diagnostic_only': True, 'no_new_acceptance_credit': True,
               'original_archive_retained': True, 'no_source_object_registry_audit_native_changes': True,
               'before': before, 'after': after, 'compression_runtime': runtime(),
               'persistent_directory': str(OUTPUT), 'bundle_path': str(final), 'bundle_bytes': info['bytes'], 'bundle_sha256': info['sha256'],
               'bundle_package_index_sha256': sha(expected_index_bytes), 'bundle_total_member_count': len(expected_bundle),
               'preserved_original_members': PRESERVED_COUNT, 'preserved_original_member_bytes': PRESERVED_BYTES,
               'shared_native': native_after, 'original_total_members': MEMBER_COUNT, 'original_total_member_bytes': MEMBER_BYTES,
               'all_original_members_accounted_for': True, 'persistent_bundle_all_members_sha256_verified': True,
               'free_bytes_before_persistent_copy': free, 'free_bytes_after_persistent_copy': shutil.disk_usage('/workspace').free,
               'minimum_free_reserve_bytes': RESERVE,
               'recipe_files': {name: digest(OUTPUT / name) for name in ['retention_common.py', 'stage1_preserve.py', 'rebuild_original_export.py', 'original-exporter.py']},
               'second_stage_not_executed': True, 'original_gzip_not_removed': True}
    receipt_pending = OUTPUT / 'stage1-receipt.pending'
    write_new(receipt_pending, encoded(receipt))
    require(shutil.disk_usage('/workspace').free >= RESERVE, 'Free space below 32 MiB after writing receipt')
    receipt_pending.rename(OUTPUT / 'stage1-receipt.json'); fsync_dir(OUTPUT)
    print(json.dumps(receipt, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
P24_RETENTION_SOURCE_1_EOF
cat > "$p24_retention_stage_dir/rebuild_original_export.py" <<'P24_RETENTION_SOURCE_2_EOF'
from __future__ import annotations
import argparse
import json
from pathlib import Path
import tempfile
from retention_common import *

def rebuild(directory):
    directory = Path(directory).resolve()
    stage1 = json.loads((directory / 'stage1-receipt.json').read_text())
    require(stage1['stage1_passed'] is True and stage1['original_gzip_not_removed'] is True, 'Missing successful preservation receipt')
    for name, expected in stage1['recipe_files'].items():
        require(digest(directory / name) == expected, 'Frozen recipe source differs: ' + name)
    require(runtime() == stage1['compression_runtime'], 'Compression runtime differs from verified recipe')
    bundle = directory / 'preserved-members.tar.gz'
    require(bundle.stat().st_size == stage1['bundle_bytes'], 'Bundle size differs')
    bundle_index, data, _ = read_bundle(bundle, stage1['bundle_sha256'], keep_all=True)
    manifest_raw = data['metadata/original-export-manifest.json']
    require(sha(manifest_raw) == MANIFEST_SHA and len(manifest_raw) == MANIFEST_BYTES, 'Captured original manifest differs')
    manifest = json.loads(manifest_raw); package = check_outer(manifest)
    inputs = json.loads(data['metadata/reconstruction-inputs.json'])
    require(inputs['compression_runtime'] == runtime() and inputs['immutable_native_root'] == str(NATIVE), 'Reconstruction environment differs')
    exporter = load_original_package(directory / 'original-exporter.py')
    require(data['metadata/original-exporter.py'] == (directory / 'original-exporter.py').read_bytes(), 'Captured exporter differs')
    originals = original_index(manifest, data['members/PACKAGE_MANIFEST.json'])
    native = native_members(manifest['files'])
    preserved = {name: row for name, row in originals.items() if name not in native}
    require(native == inputs['native_members'] and preserved == inputs['preserved_members'], 'Retained/shared partition differs')
    require({name.removeprefix('members/') for name in data if name.startswith('members/')} == set(preserved), 'Preserved member coverage differs')
    for name, record in preserved.items():
        raw = data['members/' + name]
        require(len(raw) == record['bytes'] and sha(raw) == record['sha256'], 'Preserved member differs: ' + name)
    native_before = verify_native(native)
    evidence = exporter.Evidence()
    for name, record in manifest['files'].items():
        raw = Path(record['origin']).read_bytes() if name in native else data['members/' + name]
        require(len(raw) == record['bytes'] and sha(raw) == record['sha256'], 'Rebuild member differs: ' + name)
        evidence.add_bytes(name, raw, record['origin'], record['role'])
    require(evidence.file_index() == manifest['files'], 'Original file metadata changed')
    require(exporter.encoded(package_index(manifest)) == data['members/PACKAGE_MANIFEST.json'], 'Original package metadata changed')
    temporary = Path(tempfile.mkdtemp(prefix='p24-original-export-rebuild-'))
    archive = temporary / ORIGINAL.name
    result = exporter.package(archive, set(evidence.files), package['modules'], evidence, manifest['transfer_page_bytes'])
    del evidence
    require(result['bytes'] == ORIGINAL_BYTES and result['sha256'] == ORIGINAL_SHA, 'Reconstructed original gzip differs')
    verify_tar(archive, originals)
    native_after = verify_native(native)
    require(native_after == native_before, 'Shared native inputs changed during reconstruction')
    require(digest(bundle) == stage1['bundle_sha256'], 'Persistent bundle changed during reconstruction')
    return {'stage2_rebuild_passed': True, 'diagnostic_only': True, 'no_new_acceptance_credit': True,
            'retention_directory': str(directory), 'stage1_receipt_sha256': digest(directory / 'stage1-receipt.json'),
            'bundle_sha256': stage1['bundle_sha256'], 'bundle_bytes': stage1['bundle_bytes'],
            'original_manifest_sha256': MANIFEST_SHA, 'original_exporter_sha256': EXPORTER_SHA,
            'reconstructed_archive_path_job_private': str(archive), 'reconstructed_archive_bytes': result['bytes'],
            'reconstructed_archive_sha256': result['sha256'], 'all_original_members_verified': MEMBER_COUNT,
            'all_original_member_bytes_verified': MEMBER_BYTES, 'shared_native': native_after,
            'compression_runtime': runtime(), 'current_project_sources_not_used_for_reconstruction': True,
            'original_gzip_not_removed_by_this_script': True}

def main():
    parser = argparse.ArgumentParser(description='Rebuild and verify the old export from durable retained bytes plus exact qualified native inputs; no deletion.')
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    require(not args.receipt.exists(), 'Use a new verification receipt path')
    result = rebuild(args.directory)
    write_new(args.receipt, encoded(result)); fsync_dir(args.receipt.parent)
    print(json.dumps(dict(result, receipt_path=str(args.receipt)), sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
P24_RETENTION_SOURCE_2_EOF
python3 -B "$p24_retention_stage_dir/stage1_preserve.py"
