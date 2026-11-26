python3 -B - <<'P26_CELL05_ROWS15_FIXED_READONLY'
#!/usr/bin/env python3
"""Read only the newly validated Cell05 capsule; write its transfer stream to stdout."""
from pathlib import Path
import base64
import hashlib
import json
import os
import stat
import sys

sys.dont_write_bytecode = True
CAPSULE = Path('/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-capsule-v1/rows15-provider-v1.tar.xz')
REPORT = CAPSULE.with_name(CAPSULE.name + '.json')
CAPSULE_PIN = {'bytes': 2397884, 'sha256': 'b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd'}
REPORT_PIN = {'bytes': 720, 'sha256': 'ca950b17e7d8f9508318a9624e037aa9157d28e6c91e757313c63685819c6f7c'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def read_fixed(path, expected):
    require(path.is_absolute() and '..' not in path.parts, 'Noncanonical fixed path')
    for ancestor in [*reversed(path.parents), path]:
        info = ancestor.lstat()
        require(not stat.S_ISLNK(info.st_mode), 'Symlink rejected')
        if ancestor != path:
            require(stat.S_ISDIR(info.st_mode), 'Nondirectory ancestor')
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(descriptor, 'rb') as source:
        before = os.fstat(source.fileno())
        require(stat.S_ISREG(before.st_mode), 'Nonregular fixed input')
        body = source.read()
        after = os.fstat(source.fileno())
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns), 'Input changed while reading')
    require(pin(body) == expected, 'Fixed input byte identity differs')
    return body


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    capsule = read_fixed(CAPSULE, CAPSULE_PIN)
    report_bytes = read_fixed(REPORT, REPORT_PIN)
    report = json.loads(report_bytes)
    require(report['schema'] == 'cell05_rows15_capsule_build_report_v1' and
            report['status'] == 'PASS_EXACT_ROW_SUPPLIER_CAPSULE', 'Wrong original report')
    require(report['archive'] == {'path': str(CAPSULE), **CAPSULE_PIN}, 'Original archive pin differs')
    expected = {'members': 267, 'new_object_bodies': 15, 'old_supplier_object_bodies': 0,
                'fields_object_bodies': 0, 'accepted_steps_rechecked': 45,
                'owned_declarations_rechecked': 5147, 'original_absolute_path_mappings': 496,
                'regular_archive_readback': True, 'original_inputs_unchanged': True,
                'Lean_commands': 0, 'Git_commands': 0, 'full_evidence_archive_transferred': False}
    require(all(report.get(key) == value for key, value in expected.items()), 'Original report scope differs')
    payload = base64.b64encode(capsule)
    header = {'schema': 'cell05_rows15_readback_stream_v1', 'kind': 'header',
              'archive': report['archive'], 'original_report_file': {'path': str(REPORT), **REPORT_PIN},
              'original_report': report, 'original_report_text': report_bytes.decode('utf-8'),
              'payload_encoding': 'base64', 'payload_encoded_bytes': len(payload),
              'Lean_commands': 0, 'archive_rebuilt': False, 'remote_files_written': 0}
    require(read_fixed(CAPSULE, CAPSULE_PIN) == capsule and read_fixed(REPORT, REPORT_PIN) == report_bytes,
            'Fixed original capsule or report changed before transfer output')
    footer = {'schema': 'cell05_rows15_readback_stream_v1', 'kind': 'complete',
              'archive_after': report['archive'], 'original_report_after': header['original_report_file'],
              'source_retained_on_P1': True, 'original_inputs_unchanged': True,
              'Lean_commands': 0, 'new_Lean_acceptance': 0, 'archive_rebuilt': False,
              'remote_files_written': 0, 'P2_deployment_performed': False}
    stream = (json.dumps(header, sort_keys=True, separators=(',', ':')).encode() + b'\n' +
              payload + b'\n' + json.dumps(footer, sort_keys=True, separators=(',', ':')).encode() + b'\n')
    require(len(stream) < 8 * 1024 * 1024, 'Transfer output exceeds the task log budget')
    sys.stdout.buffer.write(stream)
    sys.stdout.buffer.flush()


if __name__ == '__main__':
    main()

P26_CELL05_ROWS15_FIXED_READONLY
