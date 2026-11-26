#!/usr/bin/env python3
"""Read-only capsule recovery classification. Never deletes or overwrites."""
from pathlib import Path
import hashlib
import json
import stat

ROOT = Path('/workspace/p26-continuation-557a12f3bcd7/supplier-capsule')
VERSIONS = {
    'v1': {'builder_name': 'build_p1_minimal_capsule.py', 'request_name': 'REQUEST.json',
           'builder': {'bytes': 18565, 'sha256': 'f641496f2a875f36a150ad50903cc6f4e1d790e532f0477e438cd72742b4dc70'},
           'request': {'bytes': 271284, 'sha256': 'b6e34dc6d72abcd1969dd31b04cbda7a78c3deca0f0b7d018258cf69416fbf7a'},
           'independent_review_usable': False},
    'v2': {'builder_name': 'build_p1_minimal_capsule_v2.py', 'request_name': 'REQUEST_v2.json',
           'builder': {'bytes': 20560, 'sha256': '9cd6baaeecf17acdea43a33748e942d2c2132bc624202d8d9bb2c5525287c986'},
           'request': {'bytes': 271339, 'sha256': 'b07ae3d4fe26889b33438694aa7c011e2a7842c1d53478425dfc0633072612b8'},
           'independent_review_usable': None},
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(path):
    path = Path(path).absolute()
    need('row001' not in str(path).lower() and '..' not in path.parts,
         'Blocked/noncanonical recovery path')
    need(not path.is_symlink() and path.resolve() == path,
         'Recovery path or ancestor is a symlink: ' + str(path))
    return path


def fp(path):
    path = canonical(path)
    before = path.stat()
    need(stat.S_ISREG(before.st_mode), 'Recovery input is not a regular file')
    h = hashlib.sha256()
    with path.open('rb') as incoming:
        for block in iter(lambda: incoming.read(1024 * 1024), b''):
            h.update(block)
    after = path.stat()
    need((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns),
         'Recovery input changed during hash')
    return {'path': str(path), 'bytes': before.st_size, 'sha256': h.hexdigest()}


def same(actual, expected):
    return all(actual.get(key) == expected.get(key) for key in ('bytes', 'sha256'))


def inspect(version, controls):
    root = canonical(ROOT)
    out = canonical(root / ('missing189-objects-and14sources-' + version))
    fixed_paths = {
        'builder': canonical(root / controls['builder_name']),
        'request': canonical(root / controls['request_name']),
        'manifest': canonical(out / 'MANIFEST.json'),
        'archive': canonical(out / 'objects-and-missing-sources.tar.xz'),
        'summary': canonical(out / 'SUMMARY.json'),
    }
    actual = {key: fp(path) if path.is_file() else None for key, path in fixed_paths.items()}
    report = {'version': version, 'output_directory': str(out), 'files': actual,
              'proof_acceptance_claimed': False, 'rerun_permitted_by_this_check': False,
              'independent_review_usable': controls['independent_review_usable']}
    if not any(actual.values()) and not out.exists():
        report['status'] = 'NOT_UPLOADED_NO_ACCEPTANCE'
        return report
    for key in ('builder', 'request'):
        if actual[key] is None or not same(actual[key], controls[key]):
            report['status'] = 'CONTROL_MISSING_OR_PIN_MISMATCH_NO_ACCEPTANCE'
            return report
    if actual['summary'] is None:
        report['status'] = ('PARTIAL_ARCHIVE_NO_ACCEPTANCE' if actual['archive'] else
                            'PARTIAL_METADATA_NO_ACCEPTANCE' if actual['manifest'] else
                            'EMPTY_OUTPUT_NO_ACCEPTANCE' if out.exists() else
                            'CONTROLS_PRESENT_NO_CAPSULE_NO_ACCEPTANCE')
        return report
    need(actual['manifest'] is not None and actual['archive'] is not None,
         'Summary exists without both fixed manifest and archive')
    summary = json.loads(fixed_paths['summary'].read_text())
    need(summary['status'] == 'PASS_EXACT_MINIMAL_CAPSULE_READBACK', 'Unexpected summary status')
    need(summary['schema'] == 'p26_minimal_missing189_capsule_summary_' + version,
         'Unexpected summary schema/version')
    for key, expected in (('object_count', 189), ('source_body_count', 14), ('sidecar_count', 0),
                          ('payload_members', 203), ('archive_members', 204)):
        need(summary.get(key) == expected, 'Summary count mismatch: ' + key)
    for key in ('builder', 'request', 'manifest', 'archive'):
        # Verify the recorded path against the fixed destination before using it.
        need(summary[key]['path'] == str(fixed_paths[key]), 'Summary redirects ' + key + ' path')
        need(summary[key] == actual[key], 'Summary/current file pin mismatch: ' + key)
    need(summary['all_archive_members_size_sha256_verified'] is True,
         'Missing recorded readback success')
    need(summary['compiler_or_proof_commands_executed'] is False and
         summary['row001_files_accessed'] is False and summary['old_files_written'] is False and
         summary['receipt_or_log_bodies_included'] is False, 'Unexpected capsule scope')
    manifest = json.loads(fixed_paths['manifest'].read_text())
    need(manifest['schema'] == 'p26_minimal_p3_missing189_object_capsule_' + version and
         manifest['object_count'] == 189 and manifest['source_body_count'] == 14 and
         manifest['payload_file_count'] == 203 and manifest['sidecar_count'] == 0,
         'Manifest schema/count mismatch')
    need(manifest['builder'] == actual['builder'] and manifest['request'] == actual['request'],
         'Manifest/control pins mismatch')
    request = json.loads(fixed_paths['request'].read_text())
    need(request['capsule_name'] == out.name and request['destination_root'] == str(root),
         'Request destination mismatch')
    expected_names = {'objects/' + item['module'].replace('.', '/') + '.olean'
                      for item in request['items']}
    expected_names |= {'sources/' + item['module'].replace('.', '/') + '.lean'
                       for item in request['items'] if item['include_source_body']}
    members = manifest['members']
    need(len(members) == len({row['member'] for row in members}) == 203 and
         {row['member'] for row in members} == expected_names,
         'Manifest payload inventory differs from frozen request')
    need({row['module'] for row in manifest['modules']} ==
         {row['module'] for row in request['items']} and len(manifest['modules']) == 189,
         'Manifest supplier selection differs')
    if version == 'v2':
        need(summary['prefix_current_pins_match_fixed_export'] is True and
             manifest['receipt_validation']['C_prefix']['all_current_prefix_receipt_and_object_pins_match_fixed_export'] is True,
             'Missing v2 fixed historical prefix binding')
    report['status'] = ('COMPLETED_ARTIFACT_PINS_MATCH_RECORDED_READBACK_REVIEW_PENDING'
                        if version == 'v2' else
                        'V1_ARTIFACT_PINS_MATCH_BUT_REVIEW_REJECTED_NO_REUSE')
    report['summary'] = summary
    return report


def main():
    results = []
    for version, controls in VERSIONS.items():
        try:
            results.append(inspect(version, controls))
        except (ValueError, OSError, KeyError, TypeError) as error:
            results.append({'version': version, 'status': 'RECOVERY_VALIDATION_FAILED_NO_ACCEPTANCE',
                            'error': str(error), 'proof_acceptance_claimed': False,
                            'rerun_permitted_by_this_check': False})
    print(json.dumps({'schema': 'p26_p1_capsule_readonly_recovery_v2', 'versions': results,
                      'remote_files_written': False, 'deleted_or_overwritten': False,
                      'actual_completed_MCP_task_still_required': True},
                     sort_keys=True, separators=(',', ':')))


if __name__ == '__main__':
    main()
