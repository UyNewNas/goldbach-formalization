#!/usr/bin/env python3
"""Fixed K Licensed failure metadata plus one exact whole-module no-output probe.

Only Licensed, accepted Cutoff@K and HB@F artifact tables; three pending scope
sources; fixed failure/acceptance receipts; and existing runtime/config bindings
are observed. No full live157/160 inventory or repeated full-owned audit.
The only Lean command is serialized and guarded lake --no-build env lean on the
fixed complete Licensed candidate. It requests no owner object or output file.
"""
import argparse
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
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-licensed-scope-probe-v1')
COMMIT = '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e'
JOB = 'job_05205bc1d3f7442da9444752ab8a9972'
NORMAL_LOG_SHA = '49325bcc9885453411976db0a2db759541b80bcd87b9332bed61186614c2cb77'
TARGET = 'ImbalancedChen.P5LicensedOriginalIntegerProfile'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
SMOOTH = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
GEOMETRIC = 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily'
ARTIFACT_OWNERS = [TARGET, CUTOFF, HB]
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 59950, 'sha256': '575fcc9737d0b239cb0d994ad286ad8cae5dbf4406ca898157d7c2e87782c293'}
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
MANIFEST_FP = {'bytes': 333254, 'sha256': 'f683cfc328b7323d4e1840e10dc1eca0b24c4b55b644756ef2e5d910152a27e5'}
PROBE_FP = {'bytes': 3763, 'sha256': '675cea556d3f85f4ca5e4e4c197b95ddd11e2e60f85e86de52388fe9b2531679'}
CUTOFF_PUBLIC_FP = {'bytes': 4286, 'sha256': 'd7154414aa34e42a0b34e4e6cc7283b2b91fb55c114c0f44e9a9f7c4e582ed74'}
CUTOFF_RESULT_FP = {'bytes': 24292, 'sha256': 'd56259942009c390a7c4d55055dfe50a4fa19d7974841db433f8309e8f281117'}
CUTOFF_WORKER_FP = {'bytes': 24227, 'sha256': 'c5bdd0d16ffd21a3c5eecdd5d1a54d6d8e51ba25da2b4d044c871c74a6d675c4'}
HB_COMMIT = '080d4178711ae042235104f7f4768649f51da2ab'
HB_PUBLIC_COMMIT = 'f6fdd7fffe17803c60914bf28b39b55715d34464'
HB_PUBLIC_PATH = 'docs/p1/20261125/p15-current-public-acceptance/HB_F_PUBLIC_ACCEPTANCE.json'
HB_PUBLIC_FP = {'bytes': 3109, 'sha256': 'b1c9bbf219d3d1fea2294683f71dce391c91b9abe7d6bb80ceb0238b40081598'}
HB_RESULT_FP = {'bytes': 22986, 'sha256': '2df6012e05dd4f600fc1d098aeea674efed4c39da0b3eb1516f3ca59c0b94efa'}
EXPECTED_SOURCES = {
    TARGET: {'bytes': 3754, 'sha256': '876627ddcd468229d57a5921157445730e57abf71d3157d1874037d761f29f8a'},
    SMOOTH: {'bytes': 4336, 'sha256': '49677aed381fbd4c661d7132208d920d4f5e366aa0a1515c5566bbbdee968c83'},
    GEOMETRIC: {'bytes': 6644, 'sha256': 'ba364732afa8ef3c5f2de97eca598f40119ce2b925e77a9ef9edc2868ed254cb'},
}
BASE = ROOT / COMMIT
RUN = BASE / 'runs/attempt-00001'
NORMAL = BASE / TARGET / 'normal' / TARGET / 'attempt-00000'
RUN_NAMES = ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
             'GIT_BEFORE.json', 'GIT_AFTER.json', 'COMMITTED_INPUT_BINDINGS.json', 'executed-driver.py')
NORMAL_NAMES = ('CONTEXT_BEFORE.json', 'normal-command.json', 'normal.log',
                'directdeps-command.json', 'directdeps-started.json', 'directdeps.log',
                'normal-started.json', 'target-ready-command.json', 'target-ready-started.json', 'target-ready.log')
EVIDENCE_PATHS = [RUN / name for name in RUN_NAMES] + [NORMAL / name for name in NORMAL_NAMES]
MAX_FILE = 128 * 1024 * 1024
MAX_METADATA = 8 * 1024 * 1024
MAX_OUTPUT = 32768
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


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO, stderr=subprocess.PIPE)


def diagnostics(raw, pattern, limit):
    matches = list(re.finditer(pattern, raw))
    boundaries = list(re.finditer(rb'(?m)^error:', raw))
    rows = []
    for match in matches[:limit]:
        end = next((point.start() for point in boundaries if point.start() > match.start()), len(raw))
        block = raw[match.start():end].rstrip(b'\r\n')
        rows.append({'line': int(match.group(1)), 'column': int(match.group(2)),
            'bytes': len(block), 'sha256': hashlib.sha256(block).hexdigest(),
            'excerpt': block[:2000].decode('utf-8', 'ignore'), 'truncated': len(block) > 2000})
    return len(matches), rows


def run(candidate, cutoff_public_file):
    global STAGE
    STAGE = 'fixed_public_inputs'
    code = git_file(COMMIT, DRIVER)
    require(fingerprint_bytes(code) == DRIVER_FP, 'FIXED_K_DRIVER_DIFFERS')
    raw = git_file(COMMIT, MANIFEST)
    require(fingerprint_bytes(raw) == MANIFEST_FP, 'FIXED_K_MANIFEST_DIFFERS')
    manifest = json.loads(raw)
    expected_targets = manifest['selection_guidance']['subsequent_15_targets']
    require(len(expected_targets) == 15 and TARGET in expected_targets and
            CUTOFF not in expected_targets and HB not in expected_targets, 'FIXED_LATER15_SCOPE_DIFFERS')
    require(fingerprint(candidate) == PROBE_FP and fingerprint(cutoff_public_file) == CUTOFF_PUBLIC_FP,
            'FIXED_PROBE_OR_CUTOFF_PUBLIC_INPUT_DIFFERS')
    probe_raw = read_bound(candidate, PROBE_FP)
    require(probe_raw.splitlines()[:2] == [b'import ImbalancedChen.P5OriginalPrimeChartHBWitnesses', b'import Mathlib'],
            'WHOLE_PROBE_IMPORTS_DIFFER')
    old = git_file(COMMIT, TARGET.replace('.', '/') + '.lean')
    require(fingerprint_bytes(old) == EXPECTED_SOURCES[TARGET] and
            old.count(b'open scoped BigOperators\n') == 1 and
            old.replace(b'open scoped BigOperators\n', b'open scoped BigOperators ContDiff\n') == probe_raw,
            'PROBE_NOT_EXACT_WHOLE_MODULE_SCOPE_REPAIR')
    cutoff_public_raw = read_bound(cutoff_public_file, CUTOFF_PUBLIC_FP)
    cutoff_public = json.loads(cutoff_public_raw)
    hb_raw = git_file(HB_PUBLIC_COMMIT, HB_PUBLIC_PATH)
    require(fingerprint_bytes(hb_raw) == HB_PUBLIC_FP, 'FIXED_HB_PUBLIC_INPUT_DIFFERS')
    hb_public = json.loads(hb_raw)
    driver = ModuleType('fixed_K_licensed_metadata_probe_reader')
    driver.__file__ = DRIVER
    exec(compile(code, DRIVER, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT), 'FIXED_ENVIRONMENT_DIFFERS')
    s = driver.helpers()
    review = json.loads(driver.pinned(COMMIT, driver.REVIEW, driver.REVIEW_SHA))
    environment_before = driver.environment(s, review)
    git_before = s.d.original_git_state(REPO)
    preserved = {candidate: PROBE_FP, cutoff_public_file: CUTOFF_PUBLIC_FP}

    def read(path, pin=None):
        actual = fingerprint(path)
        require(regular_binding(actual) and (pin is None or actual == pin), 'REQUIRED_RECEIPT_DIFFERS')
        require(path not in preserved or preserved[path] == actual, 'RECEIPT_CHANGED_DURING_READ')
        preserved[path] = actual
        return read_bound(path, actual)

    STAGE = 'fixed_K_attempt1_failure'
    data = {str(path): read(path) for path in EVIDENCE_PATHS}
    require(len(data) == 18 and data[str(RUN / 'executed-driver.py')] == code, 'FIXED_FAILURE_RECORDS_DIFFER')
    result = json.loads(data[str(RUN / 'RESULT.json')])
    worker = json.loads(data[str(RUN / 'WORKER_RESULT.json')])
    for record in (result, worker):
        require(record['source_commit'] == COMMIT and len(record['targets']) == 15 and
                set(record['targets']) == set(expected_targets) and record['targets'][0] == TARGET and
                record['accepted_owners'] == [] and set(record['failures']) == {TARGET} and
                record['acceptance_bindings'] == {} and record['selected_live_source_count'] == 157 and
                not any(k in record for k in ('context_error', 'final_context_error', 'git_error')),
                'ORIGINAL_K_SINGLE_FAILURE_SCOPE_DIFFERS')
    require(result['worker_exit_code'] == 1 and result['all_selected_owners_accepted'] is False and
            result.get('dispatch_error') == 'serialized worker exited 1' and 'dispatch_error' not in worker and
            result['failures'] == worker['failures'], 'ONLY_KNOWN_DISPATCH_FAILURE_ALLOWED')
    for stem in ('CONTEXT', 'GIT'):
        require(data[str(RUN / (stem + '_BEFORE.json'))] == data[str(RUN / (stem + '_AFTER.json'))],
                'ORIGINAL_FAILED_RUN_CONTEXT_CHANGED')
    normal = json.loads(data[str(NORMAL / 'normal-command.json')])
    log = NORMAL / 'normal.log'
    require(normal['argv'] == s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean']) and
            normal['cwd'] == str(PROJECT) and normal['exit_code'] == 1 and
            normal['actual_built_modules'] == [] and normal['actual_failed_modules'] == [TARGET] and
            normal['log'] == str(log) and normal['log_bytes'] == len(data[str(log)]) and
            normal['log_sha256'] == fingerprint_bytes(data[str(log)])['sha256'] == NORMAL_LOG_SHA,
            'FAILED_NORMAL_IDENTITY_DIFFERS')
    ready = result['direct_import_readiness'][TARGET]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'FAILED_RUN_IMPORT_READINESS_DIFFERS')
    count, errors = diagnostics(data[str(log)],
        rb'(?m)^error: ImbalancedChen/P5LicensedOriginalIntegerProfile\.lean:(\d+):(\d+):', 2)
    require(count == 13 and len(errors) == 2 and all(row['line'] == 16 for row in errors),
            'EXPECTED_SCOPE_DIAGNOSTICS_DIFFER')
    normal_pass = BASE / TARGET / 'normal' / TARGET / 'NORMAL_PASS.json'
    require(fingerprint(normal_pass) is None, 'FAILED_TARGET_HAS_NORMAL_RECEIPT')

    STAGE = 'three_sources_and_exactly_sixty_three_artifacts'
    source_paths = {m: PROJECT / (m.replace('.', '/') + '.lean') for m in EXPECTED_SOURCES}
    sources = {m: fingerprint(p) for m, p in source_paths.items()}
    require(sources == EXPECTED_SOURCES and all(
        {k: manifest['project_sources'][m][k] for k in ('bytes', 'sha256')} == pin
        for m, pin in EXPECTED_SOURCES.items()), 'THREE_LIVE_SOURCE_PREIMAGES_DIFFER')
    artifact_paths = {m: driver.artifact_paths(m) for m in ARTIFACT_OWNERS}
    require(all(len(paths) == 21 and len(set(paths)) == 21 for paths in artifact_paths.values()), 'ARTIFACT_LAYOUT_DIFFERS')
    artifacts = {m: {rel: fingerprint(PROJECT / rel) for rel in paths} for m, paths in artifact_paths.items()}
    require(all(v is None or regular_binding(v) for row in artifacts.values() for v in row.values()),
            'ARTIFACT_NOT_REGULAR_OR_ABSENT')
    accepted = {}
    accepted_source_five = {}
    for module, accepted_commit, public, pub_fp, result_fp in [
        (CUTOFF, COMMIT, cutoff_public, CUTOFF_PUBLIC_FP, CUTOFF_RESULT_FP),
        (HB, HB_COMMIT, hb_public, HB_PUBLIC_FP, HB_RESULT_FP)]:
        require(public['source_commit'] == accepted_commit and public['original_result'] == result_fp and
                set(public['owners']) == {module}, 'ORIGINAL_ACCEPTANCE_PUBLIC_IDENTITY_DIFFERS')
        accepted_run = ROOT / accepted_commit / 'runs/attempt-00000'
        original = json.loads(read(accepted_run / 'RESULT.json', result_fp))
        require(original['source_commit'] == accepted_commit and original['accepted_owners'] == [module] and
                set(original['acceptance_bindings']) == {module}, 'ORIGINAL_ACCEPTANCE_SCOPE_DIFFERS')
        if module == CUTOFF:
            ow = json.loads(read(accepted_run / 'WORKER_RESULT.json', CUTOFF_WORKER_FP))
            require(original['targets'] == [CUTOFF] and original['failures'] == {} and
                    original['worker_exit_code'] == 0 and original['all_selected_owners_accepted'] is True and
                    not any(k in original for k in ('dispatch_error', 'context_error', 'final_context_error', 'git_error')) and
                    ow['source_commit'] == COMMIT and ow['accepted_owners'] == [CUTOFF] and
                    ow['failures'] == {} and ow['acceptance_bindings'] == original['acceptance_bindings'],
                    'ORIGINAL_CUTOFF_K_SUCCESS_DIFFERS')
        else:
            require(original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False and
                    set(original['failures']) == {CUTOFF} and original['dispatch_error'] == 'serialized worker exited 1',
                    'ORIGINAL_HB_F_PARTIAL_SCOPE_DIFFERS')
        owner = public['owners'][module]
        binding = original['acceptance_bindings'][module]
        require(artifacts[module] == binding['all_observed_target_artifacts'] and
                s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'] and
                owner['source_commit'] == accepted_commit, 'ACCEPTED_SOURCE_OR_ARTIFACTS_CHANGED')
        accepted_source_five[module] = binding['source_plus_five_outputs']
        base = ROOT / accepted_commit / module
        audit = base / 'audits' / owner['audit_id']
        paths = {'normal': base / 'normal' / module / 'NORMAL_PASS.json',
            'audit_plan': audit / 'AUDIT_PLAN.json', 'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
            'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json', 'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
            'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
        require(set(paths) == set(owner['receipt_bindings']), 'ACCEPTED_SIX_RECEIPTS_DIFFER')
        for key, path in paths.items():
            # Hash only; do not load, parse or disclose owned declaration types/logs.
            require(fingerprint(path) == owner['receipt_bindings'][key], 'ACCEPTED_RECEIPT_HASH_CHANGED')
            preserved[path] = owner['receipt_bindings'][key]
        accepted[module] = {'source_commit': accepted_commit, 'public_summary': pub_fp,
            'original_result': {'path': str(accepted_run / 'RESULT.json'), **result_fp},
            'receipt_bindings': owner['receipt_bindings'], 'all_21_artifacts_match_original': True,
            'owned_count_from_original_public_summary': owner['owned_count'],
            'public_count_from_original_public_summary': owner['public_count'], 'full_audit_reexecuted': False}

    def unchanged():
        require({m: fingerprint(p) for m, p in source_paths.items()} == sources, 'SOURCE_CHANGED')
        require({m: {rel: fingerprint(PROJECT / rel) for rel in paths}
                 for m, paths in artifact_paths.items()} == artifacts, 'PROJECT_ARTIFACT_CHANGED')
        require({m: s.d.snapshot(PROJECT, m) for m in accepted_source_five} == accepted_source_five,
                'ACCEPTED_SOURCE_OR_FIVE_OUTPUTS_CHANGED')
        require(all(fingerprint(p) == pin for p, pin in preserved.items()), 'RETAINED_RECEIPT_CHANGED')
        require(fingerprint(normal_pass) is None, 'FAILED_NORMAL_RECEIPT_APPEARED')
        require(driver.environment(s, review) == environment_before, 'RUNTIME_CONFIGURATION_CHANGED')
        require(s.d.original_git_state(REPO) == git_before, 'REPOSITORY_STATE_CHANGED')

    unchanged()
    setup = '.lake/build/ir/' + TARGET.replace('.', '/') + '.setup.json'
    target_expected_shape = all(v is None or rel == setup for rel, v in artifacts[TARGET].items())
    metadata = {'schema': 'p15_licensed_K_failure_exact_metadata_v1', 'source_commit': COMMIT, 'job': JOB,
        'status': 'READ_ONLY_FAILURE_METADATA_COLLECTED', 'driver': DRIVER_FP, 'source_manifest': MANIFEST_FP,
        'failed_evidence': [{'path': str(p), **preserved[p]} for p in EVIDENCE_PATHS],
        'target_source': sources[TARGET], 'scope_source_preimages': sources,
        'artifacts': artifacts[TARGET], 'accepted_owner_artifacts': {m: artifacts[m] for m in [CUTOFF, HB]},
        'accepted_owner_bindings': accepted, 'normal_pass_present': False,
        'actual_source_error_count': count, 'first_two_public_source_diagnostics': errors,
        'other_eleven_errors_already_recorded_in_public_K_failure': True,
        'normal_exit_code': 1, 'failed_setup_only_or_all_absent': target_expected_shape,
        'live_sources_observed': 3, 'artifact_entries_observed': 63,
        'current_runtime_snapshot': fingerprint_bytes(encode(environment_before)),
        'source_runtime_receipts_unchanged_across_collection': True,
        'full_live157_or_watch160_inventory_observed': False, 'full_owned_audit_reexecuted': False,
        'Lean_commands_executed': 0, 'new_acceptance': False}
    if not target_expected_shape:
        return {'schema': 'p15_licensed_K_metadata_and_whole_module_probe_v1',
            'status': 'HOLD_UNEXPECTED_FAILED_OWNER_ARTIFACT', 'metadata': metadata,
            'probe': {'Lean_typecheck_commands': 0, 'not_executed': True},
            'new_owner_acceptance': False, 'whole_P1_5_complete': False}

    STAGE = 'one_serialized_guarded_whole_module_probe'
    attempt = s.d.attempt(PROBE_ROOT / COMMIT / 'runs')
    require(attempt.resolve() == attempt, 'PROBE_EVIDENCE_PATH_NOT_CANONICAL')
    s.d.save(attempt / 'ACTUAL_K_METADATA.json', metadata)
    s.d.save(attempt / 'RUNTIME_BEFORE.json', environment_before)
    s.d.save(attempt / 'GIT_BEFORE.json', git_before)
    probe = attempt / 'LicensedOriginalIntegerProfileProbe.lean'
    s.d.write_frozen(probe, probe_raw)
    require(fingerprint(probe) == PROBE_FP, 'WRITTEN_WHOLE_MODULE_PROBE_DIFFERS')
    output_suffixes = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.c', '.bc', '.o']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in output_suffixes), 'PROBE_ALREADY_HAS_OUTPUT')
    command = s.h.serialize(0, attempt / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    outcome = s.ops.run(attempt, 'serialized-whole-licensed-probe', command, cwd=PROJECT, relay=False)
    unchanged()
    require(fingerprint(probe) == PROBE_FP and
            all(not os.path.lexists(probe.with_suffix(ext)) for ext in output_suffixes), 'PROBE_WROTE_OUTPUT_OBJECT')
    require(outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'PROBE_ATTEMPTED_PROJECT_BUILD')
    log_path = Path(outcome['log'])
    require(log_path == attempt / 'serialized-whole-licensed-probe.log', 'PROBE_LOG_PATH_DIFFERS')
    log_fp = {'bytes': outcome['log_bytes'], 'sha256': outcome['log_sha256']}
    rawlog = read_bound(log_path, log_fp)
    probe_result = {'schema': 'p15_Licensed_actual_whole_module_scope_probe_v1',
        'source_base_commit': COMMIT, 'exit_code': outcome['exit_code'],
        'probe_source': {'path': str(probe), **PROBE_FP},
        'whole_original_Licensed_module_submitted': True,
        'only_original_ContDiff_scope_enabled': True, 'imports': ['ImbalancedChen.P5OriginalPrimeChartHBWitnesses', 'Mathlib'],
        'Lean_typecheck_commands': 1, 'original_serializer_and_guard_used': True,
        'lake_no_build_env_lean': True, 'output_object_requested': False,
        'existing_project_modules_rebuilt': [], 'log': {'path': str(log_path), **log_fp},
        'compiler_output_prefix': rawlog[:6000].decode('utf-8', 'ignore'),
        'compiler_output_truncated_in_public_report': len(rawlog) > 6000,
        'three_sources_and_sixty_three_artifacts_unchanged': True,
        'accepted_Cutoff_K_and_HB_F_original_identity_preserved': True,
        'runtime_configuration_and_Git_state_unchanged': True,
        'other_two_scope_candidates_probed': False, 'normal_or_kernel_acceptance_claimed': False}
    s.d.save(attempt / 'ACTUAL_PROBE_RESULT.json', probe_result)
    s.d.save(attempt / 'RUNTIME_AFTER.json', driver.environment(s, review))
    s.d.save(attempt / 'GIT_AFTER.json', s.d.original_git_state(REPO))
    return {'schema': 'p15_licensed_K_metadata_and_whole_module_probe_v1',
        'status': 'METADATA_BOUND_AND_PROBE_SUCCEEDED_NO_OWNER_OUTPUT' if outcome['exit_code'] == 0 else 'HOLD_PROBE_FAILED',
        'evidence_root': str(attempt), 'metadata': metadata, 'probe': probe_result,
        'new_owner_acceptance': False, 'whole_P1_5_complete': False}


def main():
    global STAGE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe', type=Path, required=True)
    parser.add_argument('--cutoff-public', type=Path, required=True)
    args = parser.parse_args()
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        require(__debug__, 'PYTHON_OPTIMIZATION_NOT_ALLOWED')
        with quiet_bound_helpers():
            report = run(args.probe.absolute(), args.cutoff_public.absolute())
    except Exception as error:
        report = {'schema': 'p15_licensed_K_metadata_and_whole_module_probe_v1',
            'status': 'HOLD', 'stage': STAGE, 'failure_class': type(error).__name__,
            'source_commit': COMMIT, 'new_owner_acceptance': False}
    raw = encode(report) + b'\n'
    if len(raw) > MAX_OUTPUT:
        report = {'schema': 'p15_licensed_K_metadata_and_whole_module_probe_v1',
            'status': 'HOLD_PUBLIC_OUTPUT_BUDGET', 'unemitted_report_fingerprint': fingerprint_bytes(raw),
            'new_owner_acceptance': False}
        raw = encode(report) + b'\n'
    require(len(raw) <= MAX_OUTPUT, 'PUBLIC_OUTPUT_BOUND_FAILED')
    sys.stdout.buffer.write(raw)
    sys.stdout.buffer.flush()
    return 0 if report['status'] == 'METADATA_BOUND_AND_PROBE_SUCCEEDED_NO_OWNER_OUTPUT' else 3


if __name__ == '__main__':
    raise SystemExit(main())
