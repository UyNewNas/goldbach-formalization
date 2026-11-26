#!/usr/bin/env python3
"""P1 read-only recovery probe; PAYLOAD is supplied in memory by the saved command."""
from pathlib import Path
import hashlib
import json
import stat
import sys

sys.dont_write_bytecode = True


def require(value, message):
    if not value:
        raise ValueError(message)


def canonical(path):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts and 'row001' not in str(path).lower(),
            'Path outside the permitted recovery boundary')
    require(not path.is_symlink() and path.resolve() == path, 'Symlink/noncanonical path')
    return path


def fingerprint(path):
    path = canonical(path)
    before = path.stat()
    require(stat.S_ISREG(before.st_mode), 'Not a regular file')
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for part in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(part)
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            'File changed during fingerprint')
    return {'path': str(path), 'bytes': before.st_size, 'sha256': digest.hexdigest()}


def matches(actual, expected):
    return isinstance(expected, dict) and all(actual.get(key) == expected.get(key) for key in ('bytes', 'sha256'))


def inspect_file(path, expected=None):
    try:
        path = canonical(path)
        if not path.exists():
            return {'path': str(path), 'status': 'MISSING', 'expected': expected}
        actual = fingerprint(path)
        return {'path': str(path), 'status': 'PRESENT_MATCH' if matches(actual, expected) else
                'PRESENT_UNANCHORED' if expected is None else 'PRESENT_PIN_MISMATCH',
                'actual': actual, 'expected': expected}
    except (OSError, ValueError) as error:
        return {'path': str(path), 'status': 'READONLY_CHECK_FAILED', 'error': str(error)}


def main(payload):
    request = payload['request']
    require(request['expected_module_count'] == len(request['items']) == 189 and
            len(request['source_body_modules']) == 14, 'Unexpected requested supplier scope')
    inspector = payload['capsule_inspector_source'].encode()
    require(len(inspector) == payload['capsule_inspector']['bytes'] and
            hashlib.sha256(inspector).hexdigest() == payload['capsule_inspector']['sha256'],
            'Frozen capsule recovery inspector differs')
    namespace = {'__name__': 'p26_readonly_capsule_inspector'}
    exec(compile(inspector, '<exact-reviewed-capsule-recovery-inspector>', 'exec'), namespace)
    capsule_reports = []
    for version, controls in namespace['VERSIONS'].items():
        try:
            capsule_reports.append(namespace['inspect'](version, controls))
        except (ValueError, OSError, KeyError, TypeError) as error:
            capsule_reports.append({'version': version, 'status': 'RECOVERY_VALIDATION_FAILED_NO_ACCEPTANCE',
                                    'error': str(error), 'proof_acceptance_claimed': False})
    fixed_metadata = [inspect_file(row['path'], row) for row in payload['fixed_metadata']]
    prefix_pin = request['prefix_export_manifest']
    prefix_check = inspect_file(prefix_pin['path'], prefix_pin)
    prefix_members = {}
    if prefix_check['status'] == 'PRESENT_MATCH':
        exported = json.loads(canonical(prefix_pin['path']).read_text())
        for row in exported['members']:
            if 'path' in row:
                pin = {key: row[key] for key in ('path', 'bytes', 'sha256')}
                require(prefix_members.setdefault(pin['path'], pin) == pin, 'Conflicting fixed prefix pins')
    suppliers = []
    for item in request['items']:
        require('row001' not in json.dumps(item).lower(), 'Blocked supplier must not be inspected')
        source = inspect_file(item['source']['path'], item['source'])
        expected = item.get('object_expected')
        candidates = item.get('object_candidates', [])
        if item['kind'] == 'finite_prefix':
            expected = prefix_members.get(item['object_path'])
            candidates = [{'path': item['object_path']}]
        object_checks = [inspect_file(row['path'], expected) for row in candidates]
        matching = [row['actual'] for row in object_checks if row['status'] == 'PRESENT_MATCH']
        sidecars = []
        for obj in matching[:1]:
            path = Path(obj['path'])
            for sidecar in (Path(str(path) + '.server'), Path(str(path) + '.private'), path.with_suffix('.ir')):
                if sidecar.exists() or sidecar.is_symlink():
                    sidecars.append(inspect_file(sidecar))
        suppliers.append({'module': item['module'], 'kind': item['kind'],
                          'source_body_required': item['include_source_body'], 'source_check': source,
                          'object_checks': object_checks, 'chosen_exact_object': matching[0] if matching else None,
                          'expected_object_pin_available': expected is not None, 'sidecars': sidecars,
                          'proof_acceptance_revalidated_here': False})
    pilot_controls = [inspect_file(row['path'], row.get('expected')) for row in payload['pilot_files']]
    pilot_artifacts = []
    for row in payload['pilot_artifacts']:
        pilot_artifacts.append(inspect_file(row))
    stage = canonical(payload['pilot_stage'])
    attempts = stage / 'attempts'
    if attempts.is_dir():
        for attempt in sorted(attempts.iterdir()):
            canonical(attempt)
            if attempt.is_dir():
                for name in ('RESULT.json', 'PROOF_RESULT.json'):
                    path = attempt / name
                    if path.exists():
                        report = inspect_file(path)
                        value = json.loads(canonical(path).read_text())
                        report['recorded_status'] = value.get('status')
                        report['record_count'] = len(value.get('records', []))
                        pilot_artifacts.append(report)
    result = {'schema': 'p26_p1_readonly_recovery_inventory_v1',
              'capsule_inspector': payload['capsule_inspector'], 'capsules': capsule_reports,
              'pilot_controls': pilot_controls, 'pilot_artifacts': pilot_artifacts,
              'pilot_stage_exists': stage.exists(), 'fixed_metadata': fixed_metadata,
              'prefix_export_anchor': prefix_check, 'suppliers': suppliers,
              'summary': {'requested_objects': 189,
                          'objects_matching_original_pins': sum(row['chosen_exact_object'] is not None for row in suppliers),
                          'required_sources': 14,
                          'required_sources_matching_original_pins': sum(row['source_body_required'] and
                              row['source_check']['status'] == 'PRESENT_MATCH' for row in suppliers),
                          'all_selected_sources_matching_original_pins': sum(row['source_check']['status'] == 'PRESENT_MATCH'
                              for row in suppliers),
                          'unexpected_sidecars': sum(len(row['sidecars']) for row in suppliers)},
              'remote_files_written': False, 'old_files_written': False, 'tasks_resubmitted': False,
              'Lean_commands_executed': 0, 'row001_files_accessed': False,
              'receipt_or_log_bodies_exported': False, 'proof_acceptance_claimed': False}
    print(json.dumps(result, sort_keys=True, separators=(',', ':')), flush=True)


if __name__ == '__main__':
    main(PAYLOAD)
