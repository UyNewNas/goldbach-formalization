#!/usr/bin/env python3
"""Read only the exact new fourteen-owner Cell05 export after its recorded success.

This transfer helper does not run Lean, generate evidence, or read any Cell01
row001 archive/receipt/log. Expected pins must come from the completed dispatcher.
"""
from pathlib import Path
import argparse
import base64
import hashlib
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-bytes', type=int, required=True)
    parser.add_argument('--expected-sha256', required=True)
    args = parser.parse_args()
    path = Path('/workspace/p26-cell05-connections14-stage-557a12f3bcd7/exports/'
                'connections14-ready14-complete-v1-v1-evidence.tar.xz')
    if path.is_symlink() or path.resolve(strict=True) != path:
        raise RuntimeError('The exact new export path must be a regular file')
    report = json.loads(path.with_name(path.name + '.json').read_text())
    if not (report['status'] == 'PASS_EXPORT_RECHECK'
            and report['accepted_targets'] == 14
            and report['accepted_steps'] == 42
            and report['archive_member_recheck_passed'] is True
            and report['old_supplier_object_bodies_included'] is False
            and report['Lean_executed_for_export'] is False):
        raise RuntimeError('The original successful export report is required')
    data = path.read_bytes()
    pin = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    expected = {'bytes': args.expected_bytes, 'sha256': args.expected_sha256}
    if pin != expected or any(report['archive'][key] != value for key, value in pin.items()):
        raise RuntimeError('Export bytes differ from the completed dispatcher/report')
    print(json.dumps({'schema': 'p26_new_cell05_export_read_v1',
                      'archive_path': str(path), 'archive': pin,
                      'original_report': report, 'Lean_commands_executed': 0,
                      'payload_encoding': 'base64',
                      'payload_base64': base64.b64encode(data).decode('ascii')}), flush=True)


if __name__ == '__main__':
    main()
