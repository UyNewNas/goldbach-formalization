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
