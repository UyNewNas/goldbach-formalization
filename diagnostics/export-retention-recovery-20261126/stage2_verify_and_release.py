"""Review-only handoff: rebuild first; optional removal of one redundant gzip."""
from __future__ import annotations
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import stat
import sys

DIRECTORY = Path('/workspace/p24-export-retention-20261126/attempt-001')
ORIGINAL = Path('/workspace/p2-4-compact-proof-20261125/.lake/p24-audit-export/source6e-full324-preflight-001/all.tar.gz')
ORIGINAL_SHA = '3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463'
ORIGINAL_BYTES = 581735403
MANIFEST_SHA = '7a99f246b4c8bc54bc55ce3497de1445a270d76a34ce6af0a2e1b8e1f5e1e934'

def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            h.update(data)
    return h.hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def durable_new(path, value):
    data = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(data); stream.flush(); os.fsync(stream.fileno())
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-stage1-receipt-sha256', required=True)
    parser.add_argument('--release-original', action='store_true')
    args = parser.parse_args()
    first = DIRECTORY / 'stage1-receipt.json'
    require(sha_file(first) == args.expected_stage1_receipt_sha256, 'Stage1 receipt does not match the separately reviewed hash')
    preserved = json.loads(first.read_text())
    require(preserved['stage1_passed'] is True and preserved['persistent_bundle_all_members_sha256_verified'] is True, 'Preservation stage did not pass')
    require(preserved['bundle_compression'] == 'xz'
            and Path(preserved['bundle_path']).name == 'preserved-members.tar.xz'
            and preserved['lossless_tar_recompression_verified'] is True, 'Wrong retained bundle format/binding')
    for name, expected in preserved['recipe_files'].items():
        require(sha_file(DIRECTORY / name) == expected, 'Frozen recipe source changed')
    verification_path = DIRECTORY / 'stage2-rebuild-verification.json'
    require(not verification_path.exists(), 'Stage2 receipt already exists; review it instead of overwriting')
    sys.path.insert(0, str(DIRECTORY))
    rebuild_module = importlib.import_module('rebuild_original_export')
    verified = rebuild_module.rebuild(DIRECTORY)
    require(verified['stage2_rebuild_passed'] is True and verified['reconstructed_archive_sha256'] == ORIGINAL_SHA
            and verified['reconstructed_archive_bytes'] == ORIGINAL_BYTES
            and verified['all_original_members_verified'] == 13856
            and verified['all_original_member_bytes_verified'] == 4302650543, 'Full original reconstruction did not pass')
    durable_new(verification_path, verified)
    if not args.release_original:
        print(json.dumps({'rebuild_verified': True, 'original_archive_removed': False, 'verification_receipt': str(verification_path)}), flush=True)
        return

    # The only unlink in this script is this one exact, self-created export gzip.
    # It is reachable only after a cross-job reconstruction from durable inputs.
    require(ORIGINAL.parent.resolve() == Path('/workspace/p2-4-compact-proof-20261125/.lake/p24-audit-export/source6e-full324-preflight-001'), 'Unexpected archive parent')
    require(not ORIGINAL.is_symlink() and stat.S_ISREG(ORIGINAL.stat().st_mode), 'Original is not the expected regular gzip')
    require(ORIGINAL.stat().st_size == ORIGINAL_BYTES and sha_file(ORIGINAL) == ORIGINAL_SHA, 'Original gzip changed')
    manifest = ORIGINAL.with_name('manifest.json')
    require(sha_file(manifest) == MANIFEST_SHA, 'Original outer manifest changed')
    bundle = Path(preserved['bundle_path'])
    require(bundle.parent.resolve() == DIRECTORY and sha_file(bundle) == preserved['bundle_sha256'], 'Durable preservation bundle changed')
    require(sha_file(first) == args.expected_stage1_receipt_sha256, 'Preservation receipt changed')
    marker = ORIGINAL.with_name('all.tar.gz.reconstruction.json')
    marker_data = {
        'schema': 1, 'state': 'verified reconstruction inputs durably retained; original gzip scheduled for release',
        'original_archive_path': str(ORIGINAL), 'original_archive_bytes': ORIGINAL_BYTES, 'original_archive_sha256': ORIGINAL_SHA,
        'original_manifest_path': str(manifest), 'original_manifest_sha256': MANIFEST_SHA,
        'preservation_directory': str(DIRECTORY), 'bundle_path': str(bundle), 'bundle_sha256': preserved['bundle_sha256'],
        'stage1_receipt_path': str(first), 'stage1_receipt_sha256': args.expected_stage1_receipt_sha256,
        'stage2_verification_path': str(verification_path), 'stage2_verification_sha256': sha_file(verification_path),
        'shared_native_inputs': verified['shared_native'],
        'gzip_path_is_not_a_downloadable_archive_after_release': True,
        'only_this_redundant_gzip_may_be_removed': True, 'no_new_acceptance_credit': True,
    }
    durable_new(marker, marker_data)
    ORIGINAL.unlink()
    descriptor = os.open(ORIGINAL.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    require(not ORIGINAL.exists() and sha_file(manifest) == MANIFEST_SHA, 'Post-release state differs')
    final = dict(marker_data, state='original redundant gzip released; reconstructible from verified retained inputs',
                 original_archive_removed=True, native_source_object_audit_files_not_removed=True)
    final_path = DIRECTORY / 'stage2-release-receipt.json'
    durable_new(final_path, final)
    print(json.dumps({'original_archive_removed': True, 'released_bytes': ORIGINAL_BYTES,
                      'reconstruction_marker': str(marker), 'release_receipt': str(final_path)}, sort_keys=True), flush=True)

if __name__ == '__main__':
    main()
