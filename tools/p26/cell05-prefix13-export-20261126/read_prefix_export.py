#!/usr/bin/env python3
"""Read the separately verified new thirteen-owner prefix export, without Lean."""
from pathlib import Path
import base64
import hashlib
import json

root = Path('/workspace/p26-cell05-connections13-prefix-557a12f3bcd7')
report_path = root / 'PARTIAL_EXPORT_REPORT.json'
archive_path = root / 'connections14-prefix13-v1-evidence.tar.xz'

def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

for path in (report_path, archive_path):
    if not path.is_file() or path.is_symlink() or path.resolve(strict=True) != path:
        raise RuntimeError('Missing or noncanonical prefix export: ' + str(path))
report_bytes = report_path.read_bytes()
report = json.loads(report_bytes)
if not (report['status'] == 'PASS_PARTIAL_PREFIX13_EXPORT_RECHECK'
        and report['accepted_targets'] == 13 and report['accepted_steps'] == 39
        and report['step_counts'] == {'normal': 13, 'kernel': 13, 'owned': 13}
        and report['archive_member_recheck_passed'] is True
        and report['original_stage_and_frozen_inputs_unchanged'] is True
        and report['old_supplier_object_bodies_included'] is False
        and report['old_supplier_proof_commands'] == 0
        and report['Lean_commands_executed_for_export'] == 0
        and report['full_fourteen_target_success'] is False
        and report['P2_6_complete'] is False):
    raise RuntimeError('The complete original partial-export report is required')
data = archive_path.read_bytes()
identity = {'path': str(archive_path), **pin(data)}
if report['archive'] != identity or report_path.read_bytes() != report_bytes:
    raise RuntimeError('Archive/report changed or differ from the verified export')
print(json.dumps({'schema': 'p26_cell05_prefix13_export_read_v1',
                  'archive': identity, 'original_report': report,
                  'original_report_pin': {'path': str(report_path), **pin(report_bytes)},
                  'original_report_text': report_bytes.decode('utf-8'),
                  'payload_encoding': 'base64',
                  'payload_base64': base64.b64encode(data).decode('ascii'),
                  'Lean_commands_executed': 0,
                  'existing_files_modified': False}), flush=True)
