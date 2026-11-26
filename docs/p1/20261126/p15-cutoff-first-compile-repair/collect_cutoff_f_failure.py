#!/usr/bin/env python3
"""Fixed F Cutoff failure metadata; HB acceptance is preserved, never recompiled.

Only eighteen fixed receipt fingerprints, two sources, forty-two artifacts, and
four bounded compiler diagnostics are disclosed. No live preflight, future source
inventory, private archive/type export, filesystem writes, or Lean invocation.
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
COMMIT = '080d4178711ae042235104f7f4768649f51da2ab'
JOB = 'job_f0761da7e6124e818d654afef54ff5c5'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 48571, 'sha256': '9fffe0f6608eec153c5d58d8269f5ddb1b8f0552d8b862ae73b03451d4eda45c'}
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
MANIFEST_FP = {'bytes': 330884, 'sha256': '12c8898624290d088a7f51065db87fefa0e7f6ee72954a7fb582a28e17f4f609'}
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
PAIR = [HB, CUTOFF]
BASE = ROOT / COMMIT
RUN = BASE / 'runs/attempt-00000'
NORMAL = BASE / CUTOFF / 'normal' / CUTOFF / 'attempt-00000'
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
    matches = list(re.finditer(rb'(?m)^error: ImbalancedChen/P1OriginalSingletonCutoffData\.lean:(\d+):(\d+):', raw))
    boundaries = list(re.finditer(rb'(?m)^error:', raw))
    result = []
    for match in matches[:4]:
        end = next((point.start() for point in boundaries if point.start() > match.start()), len(raw))
        block = raw[match.start():end].rstrip(b'\r\n')
        row = {'line': int(match.group(1)), 'column': int(match.group(2)),
               'start_byte': match.start(), 'bytes': len(block), 'sha256': hashlib.sha256(block).hexdigest(),
               'header': block.split(b'\n', 1)[0][:320].decode('utf-8', 'ignore'),
               'truncated': len(block) > 2000}
        if len(block) <= 2000:
            row['excerpt'] = block.decode('utf-8', 'replace')
        else:
            row['prefix'] = block[:1000].decode('utf-8', 'ignore')
            row['suffix'] = block[-1000:].decode('utf-8', 'ignore')
        result.append(row)
    return len(matches), result


def collect():
    global STAGE
    STAGE = 'fixed_F_Git_driver_and_source_manifest'
    code = git_file(DRIVER)
    require(fingerprint_bytes(code) == DRIVER_FP, 'FIXED_F_DRIVER_DIFFERS')
    require(fingerprint_bytes(git_file(MANIFEST)) == MANIFEST_FP, 'FIXED_F_MANIFEST_DIFFERS')
    driver = ModuleType('fixed_F_readonly_Cutoff_failure_import')
    driver.__file__ = DRIVER
    exec(compile(code, DRIVER, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT), 'FIXED_ENVIRONMENT_DIFFERS')
    s = driver.helpers()
    manifest, graph, sources, _, _ = driver.source_manifest(s, COMMIT, PAIR)
    require(len(graph) == 360 and len(s.h.closure(graph, PAIR)) == 68,
            'FIXED_PAIR_SOURCE_CLOSURE_DIFFERS')

    STAGE = 'eighteen_fixed_Cutoff_failure_records'
    evidence = {str(path): fingerprint(path) for path in EVIDENCE_PATHS}
    data = {str(path): read_bound(path, evidence[str(path)]) for path in EVIDENCE_PATHS}
    require(len(evidence) == 18, 'FIXED_METADATA_COUNT_DIFFERS')
    require(data[str(RUN / 'executed-driver.py')] == code, 'RETAINED_F_DRIVER_DIFFERS')
    result = json.loads(data[str(RUN / 'RESULT.json')])
    worker = json.loads(data[str(RUN / 'WORKER_RESULT.json')])
    normal = json.loads(data[str(NORMAL / 'normal-command.json')])
    checks = {}
    checks['F_result_scope'] = all(record.get('source_commit') == COMMIT and
        set(record.get('targets', [])) == set(PAIR) and len(record.get('targets', [])) == 2 and
        record.get('accepted_owners') == [HB] and set(record.get('failures', {})) == {CUTOFF} and
        set(record.get('acceptance_bindings', {})) == {HB} and
        not any(key in record for key in ('context_error', 'final_context_error', 'git_error'))
        for record in (result, worker))
    checks['only_known_outer_dispatch_failure'] = (
        result.get('worker_exit_code') == 1 and result.get('all_selected_owners_accepted') is False and
        result.get('dispatch_error') == 'serialized worker exited 1' and 'dispatch_error' not in worker and
        result.get('failures') == worker.get('failures') and
        result.get('acceptance_bindings') == worker.get('acceptance_bindings'))
    checks['normal_command_identity'] = (normal.get('argv') == s.h.guard(0, ['lake', 'build', '+' + CUTOFF + ':olean']) and
        normal.get('cwd') == str(PROJECT) and normal.get('exit_code') == 1 and
        normal.get('actual_built_modules') == [] and normal.get('actual_failed_modules') == [CUTOFF] and
        normal.get('log') == str(NORMAL / 'normal.log') and
        normal.get('log_bytes') == evidence[str(NORMAL / 'normal.log')]['bytes'] and
        normal.get('log_sha256') == evidence[str(NORMAL / 'normal.log')]['sha256'])
    checks['retained_context_unchanged'] = data[str(RUN / 'CONTEXT_BEFORE.json')] == data[str(RUN / 'CONTEXT_AFTER.json')]
    checks['retained_Git_state_unchanged'] = data[str(RUN / 'GIT_BEFORE.json')] == data[str(RUN / 'GIT_AFTER.json')]
    error_count, diagnostics = bounded_diagnostics(data[str(NORMAL / 'normal.log')])
    checks['four_known_source_diagnostics'] = error_count == 4 and {row['line'] for row in diagnostics} == {30, 152, 230, 263}
    goal152 = [row for row in diagnostics if row['line'] == 152]
    checks['line152_goal_fully_emitted'] = len(goal152) == 1 and not goal152[0]['truncated']

    STAGE = 'fixed_pair_sources_and_two_twenty_one_artifact_sets'
    artifact_paths, artifacts = {}, {}
    for module in PAIR:
        relatives = driver.artifact_paths(module)
        require(len(relatives) == 21 and len(set(relatives)) == 21, 'FIXED_ARTIFACT_LAYOUT_DIFFERS')
        artifact_paths[module] = {relative: PROJECT / relative for relative in relatives}
        artifacts[module] = {relative: fingerprint(path) for relative, path in artifact_paths[module].items()}
    checks['artifact_entries_regular_or_absent'] = all(
        value is None or regular_binding(value) for row in artifacts.values() for value in row.values())
    hb_binding = result.get('acceptance_bindings', {}).get(HB, {})
    checks['HB_twenty_one_artifacts_equal_original_acceptance'] = (
        artifacts[HB] == hb_binding.get('all_observed_target_artifacts'))
    normal_paths = {module: BASE / module / 'normal' / module / 'NORMAL_PASS.json' for module in PAIR}
    normal_pass = {module: fingerprint(path) for module, path in normal_paths.items()}
    original_hb_normal = hb_binding.get('normal_receipt', {})
    checks['HB_normal_receipt_matches_original'] = (
        original_hb_normal.get('path') == str(normal_paths[HB]) and regular_binding(normal_pass[HB]) and
        normal_pass[HB] == {key: original_hb_normal.get(key) for key in ('bytes', 'sha256')})
    checks['Cutoff_normal_receipt_absent'] = normal_pass[CUTOFF] is None
    source_paths = {module: PROJECT / manifest['project_sources'][module]['path'] for module in PAIR}
    source_inventory = {module: fingerprint(path) for module, path in source_paths.items()}
    expected_sources = {module: {'bytes': manifest['project_sources'][module]['bytes'], 'sha256': sources[module]}
                        for module in PAIR}
    checks['both_sources_match_fixed_F'] = source_inventory == expected_sources

    STAGE = 'same_fixed_paths_after_read'
    checks['evidence_unchanged_across_collection'] = {str(path): fingerprint(path) for path in EVIDENCE_PATHS} == evidence
    checks['artifacts_unchanged_across_collection'] = all(
        {relative: fingerprint(path) for relative, path in artifact_paths[module].items()} == artifacts[module]
        for module in PAIR)
    checks['normal_receipts_unchanged_across_collection'] = {
        module: fingerprint(path) for module, path in normal_paths.items()} == normal_pass
    checks['two_sources_unchanged_across_collection'] = {
        module: fingerprint(path) for module, path in source_paths.items()} == source_inventory
    return {
        'schema': 'p15_cutoff_F_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
        'status': 'READ_ONLY_FAILURE_METADATA_COLLECTED' if all(checks.values()) else 'HOLD_METADATA_EXPECTATIONS_DIFFER',
        'checks': checks, 'driver': DRIVER_FP, 'source_manifest': MANIFEST_FP,
        'failed_evidence': [{'path': str(path), **evidence[str(path)]} for path in EVIDENCE_PATHS],
        'target_source': source_inventory[CUTOFF], 'accepted_companion_source': source_inventory[HB],
        'source_paths': {module: str(path) for module, path in source_paths.items()},
        'expected_sources': expected_sources, 'artifact_project': str(PROJECT),
        'artifacts': artifacts[CUTOFF], 'accepted_companion_artifacts': artifacts[HB],
        'normal_pass_present': normal_pass[CUTOFF] is not None,
        'accepted_companion_normal_pass_present': normal_pass[HB] is not None,
        'normal_receipt_fingerprints': normal_pass,
        'actual_source_diagnostic_count': error_count, 'bounded_source_diagnostics': diagnostics,
        'failure_summary': {'accepted_owners': result.get('accepted_owners'),
            'failed_modules': sorted(result.get('failures', {})), 'worker_exit_code': result.get('worker_exit_code'),
            'all_selected_owners_accepted': result.get('all_selected_owners_accepted'),
            'normal_exit_code': normal.get('exit_code'), 'built': normal.get('actual_built_modules'),
            'failed': normal.get('actual_failed_modules')},
        'read_only': True, 'Lean_commands_executed': 0, 'live_preflight_called': False,
        'future_source_inventory_queried': False, 'HB_full_audit_rechecked_by_this_metadata_script': False,
        'cache_adoption_performed': False, 'new_acceptance': False,
    }


def emit_bounded(report):
    payload = encode(report) + b'\n'
    if len(payload) > MAX_OUTPUT:
        original = fingerprint_bytes(payload)
        report = {'schema': 'p15_cutoff_F_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
            'status': 'HOLD_PUBLIC_OUTPUT_BUDGET', 'complete_public_metadata_emitted': False,
            'unemitted_report_fingerprint': original, 'read_only': True,
            'Lean_commands_executed': 0, 'live_preflight_called': False, 'new_acceptance': False}
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
        report = {'schema': 'p15_cutoff_F_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
            'status': 'HOLD_FIXED_READ_FAILED', 'stage': STAGE, 'error_type': type(error).__name__,
            'read_only': True, 'Lean_commands_executed': 0, 'live_preflight_called': False,
            'new_acceptance': False}
    return emit_bounded(report)


if __name__ == '__main__':
    raise SystemExit(main())
