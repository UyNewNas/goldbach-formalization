#!/usr/bin/env python3
"""Fixed read-only D failure collector. No Lean, live preflight, or filesystem writes.

Only public error excerpts, fingerprints, and presence classifications are emitted.
Existing validation records and artifact contents stay at their original paths.
The complete 157-row source inventory is hashed in memory; only missing/mismatched
rows and the four requested future R sources are disclosed. Output is <= 20000 B.
"""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
COMMIT = '7ca00b5fcc24e188a53d3a645808d388a5b9e6d1'
JOB = 'job_7292274bc17b4af7b07b528d872e02b9'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 48542, 'sha256': '035798dde6cf355355912c60e5c23805d07b201a6ddc0ffe1115aaff3da5167b'}
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
MANIFEST_FP = {'bytes': 329447, 'sha256': 'a4af2ccc0ec40e955e5138ba1304cd226dcf39d7106ce2419929ae7047258565'}
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
PAIR = [HB, CUTOFF]
FUTURE = [
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime',
    'ImbalancedChen.P5LicensedOriginalIntegerProfile',
    'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
    'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily',
    'ImbalancedChen.Part3AllKLambdaChartCorrection',
    'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
]
FUTURE_R = [
    'ImbalancedChen.P5LicensedOriginalIntegerProfile',
    'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
    'ImbalancedChen.Part3AllKLambdaChartCorrection',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime',
]
BASE = ROOT / COMMIT
RUN = BASE / 'runs/attempt-00000'
NORMAL = BASE / HB / 'normal' / HB / 'attempt-00000'
RUN_NAMES = ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
             'GIT_BEFORE.json', 'GIT_AFTER.json', 'COMMITTED_INPUT_BINDINGS.json', 'executed-driver.py')
NORMAL_NAMES = ('CONTEXT_BEFORE.json', 'normal-command.json', 'normal.log',
                'directdeps-command.json', 'directdeps-started.json', 'directdeps.log',
                'normal-started.json', 'target-ready-command.json',
                'target-ready-started.json', 'target-ready.log')
EVIDENCE_PATHS = [RUN / name for name in RUN_NAMES] + [NORMAL / name for name in NORMAL_NAMES]
MAX_FILE = 128 * 1024 * 1024
MAX_METADATA = 8 * 1024 * 1024
MAX_OUTPUT = 20000
STAGE = 'initialization'


def require(condition, code):
    if not condition:
        raise ValueError(code)


def fingerprint_bytes(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def encode(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode('utf-8')


def fingerprint(path):
    """Read only a fixed regular file; never follow a symlink or inspect a directory."""
    if not os.path.lexists(path):
        return None
    if path.resolve() != path:
        return {'kind': 'NONCANONICAL_PATH'}
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode):
        return {'kind': 'NONREGULAR'}
    if before.st_size > MAX_FILE:
        return {'kind': 'TOO_LARGE_FOR_BOUNDED_COLLECTOR', 'bytes': before.st_size}
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as source:
        opened = os.fstat(source.fileno())
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino),
                'FILE_CHANGED_DURING_OPEN')
        digest, size = hashlib.sha256(), 0
        while True:
            chunk = source.read(1024 * 1024)
            if not chunk:
                break
            size += len(chunk)
            require(size <= MAX_FILE, 'FILE_GREW_PAST_BOUND')
            digest.update(chunk)
        after = os.fstat(source.fileno())
    current = path.lstat()
    fields = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns)
    require(fields(before) == fields(after) == fields(current) and size == before.st_size,
            'FILE_CHANGED_DURING_HASH')
    return {'bytes': size, 'sha256': digest.hexdigest()}


def regular_binding(value):
    return isinstance(value, dict) and set(value) == {'bytes', 'sha256'}


def read_bound(path, expected):
    require(regular_binding(expected) and expected['bytes'] <= MAX_METADATA,
            'MISSING_OR_UNBOUNDED_REQUIRED_METADATA')
    require(path.resolve() == path and not path.is_symlink(), 'METADATA_PATH_CHANGED')
    with path.open('rb') as source:
        raw = source.read(MAX_METADATA + 1)
    require(fingerprint_bytes(raw) == expected, 'METADATA_CHANGED_DURING_READ')
    return raw


@contextlib.contextmanager
def quiet_bound_helpers():
    """Suppress helper/Git incidental output; only this collector emits public JSON."""
    capture = io.StringIO()
    sys.stdout.flush()
    sys.stderr.flush()
    saved = [os.dup(1), os.dup(2)]
    null_fd = os.open(os.devnull, os.O_WRONLY)
    try:
        os.dup2(null_fd, 1)
        os.dup2(null_fd, 2)
        with contextlib.redirect_stdout(capture), contextlib.redirect_stderr(capture):
            yield
    finally:
        for fd, original in zip((1, 2), saved):
            os.dup2(original, fd)
            os.close(original)
        os.close(null_fd)


def git_file(path):
    return subprocess.check_output(['git', 'show', COMMIT + ':' + path], cwd=REPO,
                                   stderr=subprocess.PIPE)


def bounded_diagnostics(raw):
    matches = list(re.finditer(rb'(?m)^error: ImbalancedChen/P5OriginalPrimeChartHBWitnesses\.lean:\d+:\d+:', raw))
    boundaries = list(re.finditer(rb'(?m)^error:', raw))
    result = []
    for match in matches[:5]:
        end = next((point.start() for point in boundaries if point.start() > match.start()), len(raw))
        block = raw[match.start():end].rstrip(b'\r\n')
        header = block.split(b'\n', 1)[0]
        row = {'start_byte': match.start(), 'bytes': len(block), 'sha256': hashlib.sha256(block).hexdigest(),
               'header': header[:320].decode('utf-8', 'ignore'), 'truncated': len(block) > 640}
        if len(block) <= 640:
            row['excerpt'] = block.decode('utf-8', 'replace')
        else:
            row['prefix'] = block[:320].decode('utf-8', 'ignore')
            row['suffix'] = block[-320:].decode('utf-8', 'ignore')
        result.append(row)
    return len(matches), result


def collect():
    global STAGE
    STAGE = 'fixed_D_Git_driver_and_source_manifest'
    code = git_file(DRIVER)
    require(fingerprint_bytes(code) == DRIVER_FP, 'FIXED_D_DRIVER_DIFFERS')
    require(fingerprint_bytes(git_file(MANIFEST)) == MANIFEST_FP, 'FIXED_D_MANIFEST_DIFFERS')
    driver = ModuleType('fixed_D_readonly_collector_import')
    driver.__file__ = DRIVER
    exec(compile(code, DRIVER, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT), 'FIXED_ENVIRONMENT_DIFFERS')
    s = driver.helpers()
    manifest, graph, sources, _, _ = driver.source_manifest(s, COMMIT, FUTURE)
    require(manifest['selection_guidance']['subsequent_15_targets'] == FUTURE,
            'FIXED_FUTURE_TARGETS_DIFFER')
    active = s.h.closure(graph, FUTURE)
    require(len(graph) == 360 and len(active) == 157 and set(FUTURE_R + PAIR) <= active,
            'FIXED_FUTURE_CLOSURE_DIFFERS')

    STAGE = 'eighteen_fixed_failure_records'
    evidence = {str(path): fingerprint(path) for path in EVIDENCE_PATHS}
    data = {str(path): read_bound(path, evidence[str(path)]) for path in EVIDENCE_PATHS}
    require(data[str(RUN / 'executed-driver.py')] == code, 'RETAINED_D_DRIVER_DIFFERS')
    result = json.loads(data[str(RUN / 'RESULT.json')])
    worker = json.loads(data[str(RUN / 'WORKER_RESULT.json')])
    normal = json.loads(data[str(NORMAL / 'normal-command.json')])
    checks = {}
    checks['D_result_scope'] = all(record.get('source_commit') == COMMIT and
        set(record.get('targets', [])) == set(PAIR) and len(record.get('targets', [])) == 2 and
        record.get('accepted_owners') == [] and set(record.get('failures', {})) == {HB} and
        not any(key in record for key in ('context_error', 'final_context_error', 'git_error'))
        for record in (result, worker))
    checks['normal_command_identity'] = (normal.get('argv') == s.h.guard(0, ['lake', 'build', '+' + HB + ':olean']) and
        normal.get('cwd') == str(PROJECT) and normal.get('exit_code') == 1 and
        normal.get('actual_built_modules') == [] and normal.get('actual_failed_modules') == [HB] and
        normal.get('log') == str(NORMAL / 'normal.log') and
        normal.get('log_bytes') == evidence[str(NORMAL / 'normal.log')]['bytes'] and
        normal.get('log_sha256') == evidence[str(NORMAL / 'normal.log')]['sha256'])
    checks['retained_context_unchanged'] = data[str(RUN / 'CONTEXT_BEFORE.json')] == data[str(RUN / 'CONTEXT_AFTER.json')]
    checks['retained_Git_state_unchanged'] = data[str(RUN / 'GIT_BEFORE.json')] == data[str(RUN / 'GIT_AFTER.json')]
    error_count, diagnostics = bounded_diagnostics(data[str(NORMAL / 'normal.log')])
    checks['five_source_diagnostics'] = error_count == 5

    STAGE = 'fixed_six_modules_artifacts_and_future157_sources'
    artifact_paths = {}
    artifacts = {}
    for module in PAIR + FUTURE_R:
        paths = [PROJECT / relative for relative in driver.artifact_paths(module)]
        require(len(paths) == 21 and len(set(paths)) == 21, 'FIXED_ARTIFACT_LAYOUT_DIFFERS')
        artifact_paths[module] = paths
        artifacts[module] = {str(path): fingerprint(path) for path in paths}
    normal_paths = {module: BASE / module / 'normal' / module / 'NORMAL_PASS.json' for module in PAIR}
    normal_pass = {module: fingerprint(path) for module, path in normal_paths.items()}
    checks['both_target_normal_receipts_absent'] = all(value is None for value in normal_pass.values())
    source_paths = {module: PROJECT / manifest['project_sources'][module]['path'] for module in sorted(active)}
    source_inventory = {module: fingerprint(path) for module, path in source_paths.items()}
    expected_sources = {module: {'bytes': manifest['project_sources'][module]['bytes'], 'sha256': sources[module]}
                        for module in sorted(active)}
    missing = [module for module, value in source_inventory.items() if value is None]
    mismatch = {module: {'expected': expected_sources[module], 'actual': value}
                for module, value in source_inventory.items() if value is not None and value != expected_sources[module]}

    STAGE = 'same_fixed_paths_after_read'
    checks['evidence_unchanged_across_collection'] = {str(path): fingerprint(path) for path in EVIDENCE_PATHS} == evidence
    checks['artifacts_unchanged_across_collection'] = all(
        {str(path): fingerprint(path) for path in artifact_paths[module]} == artifacts[module] for module in artifacts)
    checks['normal_receipts_unchanged_across_collection'] = {
        module: fingerprint(path) for module, path in normal_paths.items()} == normal_pass
    checks['future_sources_unchanged_across_collection'] = {
        module: fingerprint(path) for module, path in source_paths.items()} == source_inventory
    inventory_hash = fingerprint_bytes(encode(source_inventory))
    report = {
        'schema': 'p15_hb_D_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
        'status': 'READ_ONLY_FAILURE_METADATA_COLLECTED' if all(checks.values()) else 'HOLD_METADATA_EXPECTATIONS_DIFFER',
        'checks': checks, 'driver': DRIVER_FP, 'source_manifest': MANIFEST_FP,
        'failed_evidence': [{'path': str(path), **evidence[str(path)]} for path in EVIDENCE_PATHS],
        'target_source': source_inventory[HB], 'companion_source': source_inventory[CUTOFF],
        'artifacts': artifacts[HB], 'companion_artifacts': artifacts[CUTOFF],
        'normal_pass_present': normal_pass[HB] is not None,
        'companion_normal_pass_present': normal_pass[CUTOFF] is not None,
        'normal_receipt_fingerprints': normal_pass,
        'actual_source_diagnostic_count': error_count, 'bounded_source_diagnostics': diagnostics,
        'failure_summary': {'accepted_owners': result.get('accepted_owners'),
            'failed_modules': sorted(result.get('failures', {})), 'worker_exit_code': result.get('worker_exit_code'),
            'normal_exit_code': normal.get('exit_code'), 'built': normal.get('actual_built_modules'),
            'failed': normal.get('actual_failed_modules')},
        'future_sources': {'root_count': 15, 'closure_count': len(active),
            'matching_count': len(active) - len(missing) - len(mismatch),
            'missing': missing, 'mismatch': mismatch, 'canonical_inventory_json': inventory_hash,
            'missing_source_is_an_observation_not_a_preflight_failure': True},
        'future_R': {module: {'source': source_inventory[module], 'expected_source': expected_sources[module],
            'artifact_count': 21, 'all_absent': all(value is None for value in artifacts[module].values()),
            'nonabsent': {path: value for path, value in artifacts[module].items() if value is not None}}
            for module in FUTURE_R},
        'read_only': True, 'Lean_commands_executed': 0, 'future_preflight_called': False,
        'cache_adoption_performed': False, 'new_acceptance': False,
    }
    return report


def emit_bounded(report):
    payload = encode(report) + b'\n'
    if len(payload) > MAX_OUTPUT:
        # Keep all fingerprints if possible; shorten only the clearly labelled excerpts.
        for row in report.get('bounded_source_diagnostics', []):
            for key in ('excerpt', 'prefix', 'suffix'):
                row.pop(key, None)
            row['truncated'] = True
        payload = encode(report) + b'\n'
    if len(payload) > MAX_OUTPUT:
        original = fingerprint_bytes(payload)
        report = {'schema': 'p15_hb_D_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
            'status': 'HOLD_PUBLIC_OUTPUT_BUDGET', 'complete_public_metadata_emitted': False,
            'unemitted_report_fingerprint': original, 'read_only': True,
            'Lean_commands_executed': 0, 'future_preflight_called': False, 'new_acceptance': False}
        payload = encode(report) + b'\n'
    require(len(payload) <= MAX_OUTPUT, 'OUTPUT_BOUND_FAILED')
    sys.stdout.buffer.write(payload)
    sys.stdout.buffer.flush()
    return 0 if report['status'] == 'READ_ONLY_FAILURE_METADATA_COLLECTED' else 3


def main():
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        require(__debug__, 'PYTHON_OPTIMIZATION_NOT_ALLOWED')
        with quiet_bound_helpers():
            report = collect()
    except Exception as error:
        report = {'schema': 'p15_hb_D_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
            'status': 'HOLD_FIXED_READ_FAILED', 'stage': STAGE, 'error_type': type(error).__name__,
            'read_only': True, 'Lean_commands_executed': 0, 'future_preflight_called': False,
            'new_acceptance': False}
    return emit_bounded(report)


if __name__ == '__main__':
    raise SystemExit(main())
