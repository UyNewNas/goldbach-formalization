#!/usr/bin/env python3
"""Local capture of lossless P1 output pages; payload stays outside the repository."""
from pathlib import Path
import base64
import hashlib
import json
import os
import stat
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRIVATE = Path('/tmp/p26-row15-transfer-557a12f3bcd7')
DESTINATION = PRIVATE / 'rows15-provider-v1.tar.xz'
TASK = 'job_b05cd207f74c4ff0bb1f28340c363f0f'
PAGE_BYTES = 32768
CAPSULE_PIN = {'bytes': 2397884, 'sha256': 'b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd'}
REPORT_PIN = {'bytes': 720, 'sha256': 'ca950b17e7d8f9508318a9624e037aa9157d28e6c91e757313c63685819c6f7c'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def safe(path):
    require(path.is_absolute() and '..' not in path.parts, 'Unsafe local path')
    for ancestor in [*reversed(path.parents), path]:
        try:
            info = ancestor.lstat()
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(info.st_mode), 'Local symlink rejected')
        if ancestor != path:
            require(stat.S_ISDIR(info.st_mode), 'Nondirectory local ancestor')
    return path


def save(path, body, private=False):
    safe(path)
    if path.exists():
        require(path.is_file() and path.read_bytes() == body, 'Existing output differs: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True, mode=0o700 if private else 0o755)
        safe(path.parent)
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o600 if private else 0o644)
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(body)
            stream.flush()
            os.fsync(stream.fileno())
    require(path.read_bytes() == body, 'Local write readback differs')
    return {'path': str(path), **pin(body)}


def save_json(path, data):
    return save(path, (json.dumps(data, indent=2, sort_keys=True) + '\n').encode())


def status():
    value = json.loads((HERE / 'TRANSFER_TASK.json').read_bytes())
    require(value['task_id'] == TASK and value['status'] == 'succeeded' and value['exit_code'] == 0,
            'Transfer task did not succeed')
    require(value['output_truncated'] is False and 0 < value['output_bytes'] < 8 * 1024 * 1024,
            'Transfer output is missing or truncated')
    return value


def accept_page():
    meta = status()
    value = json.load(sys.stdin)
    keys = {'task_id', 'offset', 'next_offset', 'eof', 'bytes', 'output_truncated', 'stream', 'data_base64'}
    require(set(value) == keys and value['task_id'] == TASK, 'Unexpected output page schema')
    require(value['output_truncated'] is False, 'Truncated task output page')
    body = base64.b64decode(value['data_base64'], validate=True)
    offset, end = value['offset'], value['next_offset']
    require(type(offset) is int and type(end) is int and type(value['bytes']) is int,
            'Noninteger page offsets')
    require(0 <= offset < end <= meta['output_bytes'] and end - offset == len(body) == value['bytes'],
            'Page offsets or byte counts differ')
    require(offset % PAGE_BYTES == 0 and len(body) == min(PAGE_BYTES, meta['output_bytes'] - offset),
            'Unexpected fixed-page interval')
    require(value['eof'] is (end == meta['output_bytes']), 'Page EOF does not match final task byte count')
    page_path = PRIVATE / 'pages' / ('%010d.stdout' % offset)
    page_pin = save(page_path, body, private=True)
    recorded = {key: value[key] for key in keys - {'data_base64'}}
    recorded['schema'] = 'cell05_rows15_lossless_transfer_page_v1'
    recorded['decoded_page'] = page_pin
    recorded['payload_stored_outside_repository'] = True
    record_path = HERE / 'transfer-page-pins' / ('%010d.json' % offset)
    save_json(record_path, recorded)
    print(json.dumps({'offset': offset, 'next_offset': end, 'bytes': len(body),
                      'sha256': page_pin['sha256'], 'eof': value['eof']}, sort_keys=True))


def finalize():
    meta = status()
    records = [json.loads(path.read_bytes()) for path in sorted((HERE / 'transfer-page-pins').glob('*.json'))]
    require(records, 'No captured pages')
    offset, chunks = 0, []
    for index, record in enumerate(records):
        require(record['task_id'] == TASK and record['offset'] == offset and
                record['output_truncated'] is False, 'Gap, overlap, or foreign page')
        path = safe(Path(record['decoded_page']['path']))
        require(path == PRIVATE / 'pages' / ('%010d.stdout' % offset), 'Unexpected private page path')
        body = path.read_bytes()
        require(pin(body) == {key: record['decoded_page'][key] for key in ('bytes', 'sha256')},
                'Private page no longer matches its recorded pin')
        require(len(body) == record['bytes'] == record['next_offset'] - offset, 'Page interval mismatch')
        require(record['eof'] is (index == len(records) - 1), 'Unexpected intermediate EOF')
        chunks.append(body)
        offset = record['next_offset']
    require(offset == meta['output_bytes'], 'Captured output does not reach the actual task length')
    raw = b''.join(chunks)
    require(raw.endswith(b'\n') and len(raw.splitlines()) == 3, 'Malformed fixed transfer stream')
    header_bytes, encoded, footer_bytes = raw.splitlines()
    header, footer = json.loads(header_bytes), json.loads(footer_bytes)
    require(header['schema'] == footer['schema'] == 'cell05_rows15_readback_stream_v1' and
            header['kind'] == 'header' and footer['kind'] == 'complete', 'Missing transfer endpoints')
    require(header['payload_encoding'] == 'base64' and header['payload_encoded_bytes'] == len(encoded),
            'Encoded capsule byte count differs')
    capsule = base64.b64decode(encoded, validate=True)
    require(pin(capsule) == CAPSULE_PIN, 'Transferred capsule differs from the accepted P1 pin')
    original = (HERE / 'BUILD_REPORT_ORIGINAL.json').read_bytes()
    require(pin(original) == REPORT_PIN and header['original_report_text'].encode() == original and
            header['original_report'] == json.loads(original), 'Original report did not survive transfer')
    report = json.loads(original)
    require(header['archive'] == footer['archive_after'] == report['archive'], 'Before/after capsule pins differ')
    require(header['original_report_file'] == footer['original_report_after'] and
            {key: header['original_report_file'][key] for key in ('bytes', 'sha256')} == REPORT_PIN,
            'Before/after original report pins differ')
    require(footer['source_retained_on_P1'] is True and footer['original_inputs_unchanged'] is True and
            footer['remote_files_written'] == footer['Lean_commands'] == footer['new_Lean_acceptance'] == 0 and
            footer['archive_rebuilt'] is False and footer['P2_deployment_performed'] is False,
            'Read-only transfer boundary differs')
    private_stream = save(PRIVATE / 'TRANSFER_STDOUT.log', raw, private=True)
    local_archive = save(DESTINATION, capsule, private=True)

    # Use the original archive reader and pinned source mapping, without any proof command.
    donor = HERE.parent / 'scalable-cell05-connections-run'
    sys.path.insert(0, str(donor))
    from evidence_io import archive_bytes
    from supplier_capsule import load_plan, row_mapping
    bodies = archive_bytes(DESTINATION, CAPSULE_PIN)
    require(len(bodies) == 267 and 'CAPSULE_MANIFEST.json' in bodies, 'Wrong regular member count')
    manifest = json.loads(bodies['CAPSULE_MANIFEST.json'])
    require(manifest['schema'] == 'cell05_rows15_relocatable_supplier_capsule_v1', 'Wrong capsule schema')
    expected = [{'member': name, **pin(body)} for name, body in sorted(bodies.items())
                if name != 'CAPSULE_MANIFEST.json']
    require(manifest['members'] == expected and len(expected) == 266, 'Manifest/member pins differ')
    plan = load_plan(donor)
    spec = plan['batches']['rows15']
    for key, expected_pin in [('source_archive', spec['archive']), ('source_export_manifest', spec['export_manifest']),
                              ('source_run', spec['run']), ('source_success', spec['success'])]:
        require(manifest[key] == expected_pin, 'Original supplier anchor differs: ' + key)
    require(pin(bodies['ORIGINAL_EXPORT_MANIFEST.json']) ==
            {key: spec['export_manifest'][key] for key in ('bytes', 'sha256')}, 'Original export manifest changed')
    mappings = row_mapping(donor, plan)
    require(manifest['mappings'] == mappings and len(mappings) == 496, 'Original path mapping differs')
    blob_names = {row['resolved']['member'] for row in mappings if row['resolved']['kind'] == 'blob'}
    require(set(bodies) == blob_names | {'ORIGINAL_EXPORT_MANIFEST.json', 'CAPSULE_MANIFEST.json'},
            'Unexpected or missing blob member')
    for row in mappings:
        if row['resolved']['kind'] == 'blob':
            require(pin(bodies[row['resolved']['member']]) ==
                    {key: row['original'][key] for key in ('bytes', 'sha256')}, 'Mapped blob pin differs')
    scoped = {'accepted_targets_rechecked': 15, 'accepted_steps_rechecked': 45,
              'owned_declarations_rechecked': 5147, 'new_object_bodies': 15,
              'old_supplier_object_bodies': 0, 'fields_object_bodies': 0,
              'shared_baseline_members': 154, 'original_receipt_bytes_rewritten': False,
              'Lean_commands': 0, 'Git_commands': 0, 'complete_join_acceptance': False}
    require(all(manifest.get(key) == value for key, value in scoped.items()), 'Capsule scope differs')
    require(pin(DESTINATION.read_bytes()) == CAPSULE_PIN, 'Local capsule changed during member verification')
    inventory = {'schema': 'cell05_rows15_transfer_member_inventory_v1', 'archive': local_archive,
                 'members': [{'member': name, **pin(body)} for name, body in sorted(bodies.items())],
                 'regular_member_count': 267, 'original_path_mappings': 496}
    inventory_pin = save_json(HERE / 'TRANSFER_MEMBER_PINS.json', inventory)
    result = {'schema': 'cell05_rows15_private_transfer_result_v1',
              'status': 'PASS_EXACT_CAPSULE_RECOVERED_OUTSIDE_REPOSITORY', 'task': meta,
              'local_archive': local_archive, 'original_P1_archive': report['archive'],
              'original_report': report, 'exact_output_bytes': len(raw), 'output_pages': len(records),
              'pages_contiguous_from_zero_through_EOF': True, 'pages': records,
              'private_stdout_pin': private_stream, 'member_inventory_pin': inventory_pin,
              'all_267_regular_members_checked': True, 'all_266_payload_member_pins_checked': True,
              'original_anchor_and_496_mapping_pins_checked': True,
              'original_P1_capsule_retained': True, 'archive_rebuilt': False,
              'Lean_commands': 0, 'new_Lean_acceptance': 0, 'P2_upload_submitted': False,
              'payload_written_to_repository': False, 'old_Cell01_Row001_selected': False}
    result_pin = save_json(HERE / 'TRANSFER_RESULT.json', result)
    print(json.dumps({'status': result['status'], 'local_archive': local_archive,
                      'output_pages': len(records), 'exact_output_bytes': len(raw),
                      'member_inventory': inventory_pin, 'result': result_pin}, sort_keys=True))


if __name__ == '__main__':
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    require(len(sys.argv) == 2 and sys.argv[1] in ('accept-page', 'finalize'), 'Expected accept-page or finalize')
    safe(PRIVATE)
    require(not PRIVATE.is_relative_to(HERE.parents[2]), 'Private payload overlaps the repository')
    PRIVATE.mkdir(mode=0o700, parents=True, exist_ok=True)
    if sys.argv[1] == 'accept-page':
        accept_page()
    else:
        finalize()
