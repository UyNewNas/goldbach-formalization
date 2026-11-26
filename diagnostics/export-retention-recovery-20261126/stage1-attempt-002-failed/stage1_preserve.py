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
              'compression_runtime': runtime(), 'original_file_index_count': FILE_INDEX_COUNT, 'original_file_index_bytes': FILE_INDEX_BYTES,
              'original_member_count': MEMBER_COUNT, 'original_member_bytes': MEMBER_BYTES,
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
               'shared_native': native_after, 'original_file_index_count': FILE_INDEX_COUNT, 'original_file_index_bytes': FILE_INDEX_BYTES,
               'original_total_members': MEMBER_COUNT, 'original_total_member_bytes': MEMBER_BYTES,
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
