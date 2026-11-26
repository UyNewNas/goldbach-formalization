#!/usr/bin/env python3
"""Archive the exact failed AllK setup, then install its two-splice source repair.

This entrypoint uses the unmodified O reader and original installation/serializer
helpers. It never invokes normal compilation, kernel checking, or owner acceptance.
--source-commit names the publication of this script (Q); proof source is pinned
separately to P. A missing setup is admissible only with this Q/script/P-bound
durable archive. An already-installed source is held for explicit inspection.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace
import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-allk-api-repair-v1')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
SCRIPT = 'docs/p1/20261126/p15-allk-api-repair/apply_allk_repair.py'
O = 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d'
P = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
OLD_ANCHOR = 'c47ea640bf40c22423aec7066c13e5b05956d349'
OLD_JOB = 'job_cda017c5183c4b5ba80a8a2182f446ba'
PROBE_JOB = 'job_7ace088559f843d180cb12d7e4bd45a1'
TARGET = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
PRIOR = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
SOURCE = 'ImbalancedChen/Part3AllKLambdaChartCorrection.lean'
SETUP = '.lake/build/ir/ImbalancedChen/Part3AllKLambdaChartCorrection.setup.json'
ARCHIVE_NAME = 'Part3AllKLambdaChartCorrection.setup.json'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PREFIX = 'docs/p1/20261126/p15-allk-first-compile-repair/'
REPAIR = PREFIX + 'REPAIR_CANDIDATE.json'
METADATA = PREFIX + 'ACTUAL_O_METADATA.json'
PROBE = PREFIX + 'ACTUAL_ALLK_PROBE_RESULT.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/PERGROUP_O_PUBLIC_ACCEPTANCE.json'
DRIVER_FP = {'bytes': 87907, 'sha256': '9e673a755108d8cf58f02db2165654a1df97e701b0137275078e33da2136f5d9'}
MANIFEST_FP = {'bytes': 339019, 'sha256': '0801ba4e04eacfa8c8d9f99ec657898035d1af3153bcc4023de54bb20833ed2f'}
BEFORE = {'bytes': 11458, 'sha256': '124094d9fbc7358bfbc5e841cc2c5f853330f54f1f432fa17728e1ce1a5f64b8'}
AFTER = {'bytes': 11416, 'sha256': '9d739aab99a7873daaf25f649cca910d11f02a08ae22a32a70f517734df67962'}
SETUP_FP = {'bytes': 6329098, 'sha256': '14330c5ee87da605a861559cdd3adb035302ef8e4aa90d3f20cf467b751e0b87'}
RESULT_FP = {'bytes': 39901, 'sha256': '48934d443e7598fb71c8c20eead738e63af03b4fa7ad11f5c00943b723db2bee'}
WORKER_FP = {'bytes': 39785, 'sha256': 'd0886d01d8b06fc23db731d730fdd05bcb2445faa9fc45799cab766df9bd6cfd'}
PINS = {
    REPAIR: {'bytes': 2891, 'sha256': 'dce78b863f0be44745b4f7e24a42973a189ed91df98b769aa3edcfa07c97ad9d'},
    PROBE: {'bytes': 2804, 'sha256': '1a0a8092be5ea2a2631afee6ba8dce1e5363a61903b97791b78809efc61aa073'},
    METADATA: {'bytes': 20838, 'sha256': 'abf4f362d6b0bc8a4b6e91a8422c0e68d367cc1e2af59a20c6a47871898ec985'},
    PUBLIC: {'bytes': 6477, 'sha256': '3d69364fab09231361e4f551c2318147966c092ba2e56f3c8292675d6fb196c6'},
}
ORIGINAL_TARGETS = [PRIOR, TARGET,
    'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily',
    'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
REMAINING = ORIGINAL_TARGETS[1:]
AUDIT_ID = '370ebae525106ac7bd2e'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(binding):
    return {key: binding[key] for key in ('bytes', 'sha256')}


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def file_fp(c, path):
    path = Path(path)
    return c.driver.regular_fingerprint(c.s, path) if os.path.lexists(path) else None


def tree_inventory(c, root):
    require(root.is_dir() and root.resolve() == root, 'original evidence root differs')
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'symlink in original evidence tree: ' + str(path))
        result[str(path.relative_to(root))] = 'directory' if path.is_dir() else file_fp(c, path)
    return result


def source_inventory(c, modules):
    return {m: file_fp(c, PROJECT / c.s.h.module_path(m)) for m in sorted(modules)}


def artifact_inventory(c, modules):
    return {m: c.driver.module_artifacts(c.s, m) for m in sorted(modules)}


def normal_path(module):
    return OLD_ROOT / O / module / 'normal' / module / 'NORMAL_PASS.json'


def load(commit):
    require(__debug__ and re.fullmatch('[0-9a-f]{40}', commit), 'full Q commit and unoptimized Python required')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'execution source must name a commit')
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', P, commit], cwd=REPO).returncode == 0,
            'execution Q must descend from published repair P')
    executed = Path(__file__)
    require(executed.is_file() and not executed.is_symlink(), 'executed updater is not a regular file')
    script = executed.read_bytes()
    require(script == git_file(commit, SCRIPT), 'executed updater differs from its Q publication')
    published = {}
    for path, expected in PINS.items():
        raw = git_file(P, path)
        require(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published P/Q evidence differs: ' + path)
        published[path] = json.loads(raw)
    before, after = git_file(O, SOURCE), git_file(P, SOURCE)
    require(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
            'canonical O/P/Q AllK source binding differs')
    repair = published[REPAIR]
    require(repair['schema'] == 'p15_AllK_exact_two_splice_repair_v1' and
            repair['failed_source_commit'] == O and repair['failed_job'] == OLD_JOB and
            repair['module'] == TARGET and repair['canonical_path'] == SOURCE and
            pin(repair['before']) == BEFORE and pin(repair['after']) == AFTER and
            repair['failed_setup']['path'] == SETUP and pin(repair['failed_setup']) == SETUP_FP and
            repair['probe']['compiler_job'] == PROBE_JOB and repair['probe']['result_path'] == PROBE and
            pin(repair['probe']) == PINS[PROBE] and repair['new_AllK_owner_acceptance'] is False and
            repair['whole_P1_5_complete'] is False, 'exact published repair identity differs')
    pieces, end = [], 0
    require(len(repair['splices']) == 2, 'repair is not two exact splices')
    for splice in repair['splices']:
        start, stop = splice['original_byte_start'], splice['original_byte_end']
        require(end <= start < stop <= len(before) and before[start:stop] == splice['before_utf8'].encode(),
                'original splice range or bytes differ')
        pieces.extend((before[end:start], splice['after_utf8'].encode()))
        end = stop
    require(b''.join(pieces) + before[end:] == after, 'repair changes bytes outside the two splices')
    raw = git_file(O, DRIVER)
    entry = OLD_ROOT / O / 'published-entrypoints/run_selected.py'
    require(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw,
            'original O driver binding differs')
    require(raw_fp(git_file(O, MANIFEST)) == MANIFEST_FP, 'original O manifest binding differs')
    driver = ModuleType('unchanged_original_O_allk_repair_reader')
    driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
            (REPO, PROJECT, OLD_ROOT, DRIVER, OLD_ANCHOR), 'original O reader environment differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(script)},
        'source_repair_commit': P, 'published_evidence': PINS, 'failed_source_commit': O,
        'failed_job': OLD_JOB, 'module': TARGET, 'source_path': SOURCE,
        'source_before': BEFORE, 'source_after': AFTER, 'failed_setup': {'path': SETUP, **SETUP_FP}}
    return SimpleNamespace(commit=commit, driver=driver, s=driver.helpers(), published=published,
                           before=before, after=after, script=script, identity=identity)


def read_original_evidence(c):
    base, s, driver = OLD_ROOT / O, c.s, c.driver
    old_run = base / 'runs/attempt-00000'
    require(file_fp(c, old_run / 'executed-driver.py') == DRIVER_FP, 'actual O executed driver differs')
    require(file_fp(c, old_run / 'RESULT.json') == RESULT_FP and
            file_fp(c, old_run / 'WORKER_RESULT.json') == WORKER_FP, 'original O failed run pins differ')
    result, worker = [s.api.read_json(old_run / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
    for record in (result, worker):
        require(record['source_commit'] == O and record['targets'] == ORIGINAL_TARGETS and
                record['accepted_owners'] == [PRIOR] and set(record['failures']) == {TARGET} and
                set(record['acceptance_bindings']) == {PRIOR} and record['published_source_count'] == 360 and
                record['selected_live_source_count'] == 157 and record['whole_P1_5_complete'] is False and
                record['whole_P1_complete'] is False and
                not any(k in record for k in ('context_error', 'final_context_error', 'git_error', 'final_stock_readiness')),
                'original O fourteen-target partial failure scope differs')
    require(all(result.get(k) == value for k, value in worker.items()) and result['worker_exit_code'] == 1 and
            result['all_selected_owners_accepted'] is False and
            result['dispatch_error'] == 'serialized worker exited 1', 'original O failure status differs')
    public = c.published[PUBLIC]
    require(public['source_commit'] == O and public['source_anchor_commit'] == OLD_ANCHOR and
            public['compiler_job'] == OLD_JOB and public['original_targets'] == ORIGINAL_TARGETS and
            public['original_group_accepted_owners'] == [PRIOR] and
            public['original_group_failed_modules'] == [TARGET] and
            public['original_group_not_started_modules'] == ORIGINAL_TARGETS[2:] and
            public['original_group_not_accepted_modules'] == REMAINING and
            public['original_result'] == RESULT_FP and public['original_worker_result'] == WORKER_FP and
            public['normal_or_kernel_commands_executed'] == 0, 'PerGroup public O scope differs')
    for stem, pair in public['original_context_pairs'].items():
        require(stem in ('CONTEXT', 'GIT') and pair['before'] == pair['after'] and
                file_fp(c, old_run / (stem + '_BEFORE.json')) == pair['before'] and
                file_fp(c, old_run / (stem + '_AFTER.json')) == pair['after'], 'original O context pair differs')
    context = s.api.read_json(old_run / 'CONTEXT_BEFORE.json')
    metadata = c.published[METADATA]
    require(metadata['source_commit'] == O and len(metadata['records']) == 12, 'actual O metadata scope differs')
    bindings = {row['binding']['path']: pin(row['binding']) for row in metadata['records']}
    require(len(bindings) == 12 and bindings[str(PROJECT / SOURCE)] == BEFORE and
            bindings[str(PROJECT / SETUP)] == SETUP_FP, 'actual source/setup metadata differs')
    for path, expected in bindings.items():
        require(path in (str(PROJECT / SOURCE), str(PROJECT / SETUP)) or Path(path).is_relative_to(base),
                'unexpected original metadata path')
        if path != str(PROJECT / SETUP):
            require(file_fp(c, path) == expected, 'actual original evidence differs: ' + path)
    normal_dir = base / TARGET / 'normal' / TARGET / 'attempt-00000'
    command = s.api.read_json(normal_dir / 'normal-command.json')
    log = normal_dir / 'normal.log'
    require(command['argv'] == s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean']) and
            command['cwd'] == str(PROJECT) and command['exit_code'] == 1 and
            command['actual_built_modules'] == [] and command['actual_failed_modules'] == [TARGET] and
            command['log'] == str(log) and
            {'bytes': command['log_bytes'], 'sha256': command['log_sha256']} == bindings[str(log)],
            'original failed AllK normal command differs')
    return result, context


def bind_pergroup(c, spec, result):
    driver, s = c.driver, c.s
    require(len(spec.active) == 69 and len(spec.dependency_pins) == 68 and TARGET not in spec.active and
            set(spec.initial_owners) == {PRIOR}, 'original PerGroup reader scope differs')
    driver.require_completed_existing_owner(s, O, spec, PRIOR, spec.initial_owners[PRIOR])
    accepted = driver.acceptance_binding(s, O, PRIOR)
    require(accepted == result['acceptance_bindings'][PRIOR], 'complete original PerGroup acceptance differs')
    public = c.published[PUBLIC]['owners'][PRIOR]
    require(public['source_commit'] == O and public['source_sha256'] == spec.sources[PRIOR] and
            (public['owned_count'], public['public_count'], public['audit_id']) == (68, 58, AUDIT_ID) and
            public['receipt_rebound_to_current_commit'] is False, 'PerGroup original identity/counts differ')
    audit = OLD_ROOT / O / PRIOR / 'audits' / AUDIT_ID
    paths = {'normal': normal_path(PRIOR), 'audit_plan': audit / 'AUDIT_PLAN.json',
        'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    require({key: file_fp(c, path) for key, path in paths.items()} == public['receipt_bindings'],
            'PerGroup six original public receipt pins differ')
    counts = s.api.read_json(paths['audit_result'])
    require((counts['total_owned_exports'], counts['total_public_exports']) == (68, 58), 'PerGroup actual counts differ')
    return accepted


def probe_bindings(c):
    probe = c.published[PROBE]
    require(probe['source_base_commit'] == O and probe['exit_code'] == 0 and
            pin(probe['candidate']) == AFTER and probe['original_source'] == BEFORE and
            probe['whole_original_module_submitted'] is True and probe['exact_two_proof_splices_only'] is True and
            probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
            probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False,
            'published whole-module probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    require(file_fp(c, candidate) == AFTER and file_fp(c, log) == pin(probe['log']) and
            log.read_bytes() == probe['compiler_output'].encode(), 'retained successful probe differs')
    paths = {str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_ALLK_PROBE_RESULT.json'): PINS[PROBE],
        str(candidate.parent / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json'): PINS[PUBLIC]}
    require(all(file_fp(c, path) == expected for path, expected in paths.items()), 'retained probe/public result differs')
    return paths


def archive_binding(c, receipt):
    run = receipt.parent
    require(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
            receipt.resolve() == receipt, 'unexpected AllK archive receipt location')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    require(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
            record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
            record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
            record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
            record['new_lean_acceptance'] is False and archive.resolve() == archive and
            file_fp(c, archive) == SETUP_FP, 'archive is not bound to this exact AllK/Q/script/P/O repair')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}


def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    require(receipts, 'active setup absent without this updater publication\'s durable archive')
    bindings = {}
    for receipt in receipts:
        bindings.update(archive_binding(c, receipt))
    return bindings


def prepare(c):
    driver, s = c.driver, c.s
    git = s.d.original_git_state(REPO)
    evidence = tree_inventory(c, OLD_ROOT / O)
    result, original_context = read_original_evidence(c)
    prior_spec = driver.preflight(s, O, [PRIOR])
    accepted = bind_pergroup(c, prior_spec, result)
    graph, sources = prior_spec.graph, prior_spec.sources
    active = s.h.closure(graph, REMAINING)
    watch = active | set(driver.TARGETS)
    require(len(graph) == 360 and len(active) == 157 and len(watch) == 160 and prior_spec.active <= active and
            set(ORIGINAL_TARGETS) == set(prior_spec.manifest['selection_guidance']['subsequent_14_targets']) and
            not active.intersection(prior_spec.manifest['unaccepted_p3_dependencies']), 'O source/watch scope differs')
    for module, row in prior_spec.manifest['project_sources'].items():
        raw = git_file(P, row['path'])
        require(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and git_file(c.commit, row['path']) == raw and
                s.h.imports(raw) == row['all_imports'], 'unrelated P/Q published source or import changed: ' + module)
    installed = source_inventory(c, graph)
    require(installed[TARGET] == BEFORE and (PROJECT / SOURCE).resolve() == PROJECT / SOURCE,
            'AllK is not the exact O preimage; already-installed repairs require inspection')
    actual_graph, actual = s.h.project_graph(PROJECT, REMAINING)
    require(actual_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in actual.items()} == {m: sources[m] for m in active}, 'live O graph differs')
    artifacts = artifact_inventory(c, watch)
    require(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
            all(v is None for p, v in artifacts[TARGET].items() if p != SETUP), 'AllK failed artifacts are not exact setup only')
    for module in REMAINING:
        require(not os.path.lexists(normal_path(module)), 'unexpected remaining-owner normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    require(original_context['selected_live_sources'] == {m: sources[m] for m in active} and
            set(original_context['preserved_dependency_artifacts']) == active - set(ORIGINAL_TARGETS) and
            all(artifacts[m] == value for m, value in original_context['preserved_dependency_artifacts'].items()),
            'original O 143 dependency artifacts or live157 source bindings differ')
    retained = {**original_context['retained_original_evidence'], **probe_bindings(c), **archives}
    require(all(file_fp(c, path) == expected for path, expected in retained.items()), 'original retained evidence differs')
    environment = driver.environment(s, prior_spec.review)
    require(all(original_context[k] == v for k, v in environment.items()), 'original O runtime/configuration differs')
    state = SimpleNamespace(prior_spec=prior_spec, accepted=accepted, active=active, watch=watch,
        sources=installed, artifacts=artifacts, evidence=evidence, retained=retained, git=git,
        result=result, original_context=original_context, archives=archives)
    unchanged(c, state)
    return state


def unchanged(c, state, *, setup_absent=False, source_after=False):
    sources, artifacts = copy.deepcopy(state.sources), copy.deepcopy(state.artifacts)
    if source_after:
        sources[TARGET] = AFTER
    if setup_absent:
        artifacts[TARGET][SETUP] = None
    require(source_inventory(c, state.prior_spec.graph) == sources and artifact_inventory(c, state.watch) == artifacts,
            'source360 or artifact160 preservation differs')
    require(tree_inventory(c, OLD_ROOT / O) == state.evidence and
            all(file_fp(c, path) == expected for path, expected in state.retained.items()), 'original evidence changed')
    require(c.driver.snapshot(c.s, state.prior_spec) == state.prior_spec.baseline and
            c.driver.acceptance_binding(c.s, O, PRIOR) == state.accepted, 'complete original PerGroup context changed')
    require(c.s.d.original_git_state(REPO) == state.git and
            all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'Git or original remaining normal state changed')


def fsync_directory(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def preserve_failed_setup(c, state, run):
    if state.artifacts[TARGET][SETUP] is None:
        require(state.archives == prior_archive(c), 'resume archive binding changed')
        return {'action': 'ALREADY_ARCHIVED_AND_ABSENT', 'bindings': state.archives}
    path = PROJECT / SETUP
    require(path.resolve() == path and path.is_file() and not path.is_symlink(), 'failed setup is not the fixed regular file')
    original, raw = path.stat(), path.read_bytes()
    require(raw_fp(raw) == SETUP_FP, 'active failed setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    require(archive.parent.resolve() == archive.parent, 'archive parent is not a regular directory')
    descriptor = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    require(file_fp(c, archive) == SETUP_FP, 'exclusive AllK setup archive differs')
    for directory in (archive.parent, run, run.parent, run.parent.parent, ROOT, ROOT.parent):
        fsync_directory(directory)
    receipt = run / 'FAILED_SETUP_ARCHIVE.json'
    c.s.d.save(receipt, {'status': 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED', 'identity': c.identity,
        'active_path': str(path), 'archive_path': str(archive), 'fingerprint': SETUP_FP,
        'archive_fsync_verified': True, 'active_removal_planned': True, 'new_lean_acceptance': False,
        'original_stat': {'device': original.st_dev, 'inode': original.st_ino, 'size': original.st_size,
                          'mtime_ns': original.st_mtime_ns, 'mode': original.st_mode & 0o777}})
    with receipt.open('rb') as stream:
        os.fsync(stream.fileno())
    fsync_directory(run)
    bindings = archive_binding(c, receipt)
    current = path.stat()
    require(not path.is_symlink() and path.resolve() == path and
            (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns) ==
            (original.st_dev, original.st_ino, original.st_size, original.st_mtime_ns) and path.read_bytes() == raw,
            'active setup changed before its authorized removal')
    path.unlink()
    fsync_directory(path.parent)
    require(not os.path.lexists(path), 'failed setup remains active after archival')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}


def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'original_O_status': {'targets': ORIGINAL_TARGETS, 'accepted_owners': [PRIOR], 'failed_modules': [TARGET],
                             'worker_exit_code': 1, 'all_selected_owners_accepted': False},
        'published_source_count': 360, 'active_source_count': 157, 'watched_module_count': 160,
        'sources_before': state.sources, 'artifacts_before': state.artifacts,
        'complete_original_O_evidence': state.evidence, 'retained_original_inputs': state.retained,
        'PerGroup_original_acceptance': state.accepted, 'PerGroup_context': state.prior_spec.baseline,
        'original_O_context': state.original_context, 'Git_before': state.git,
        'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = preserve_failed_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, setup_absent=True)
    # This is the actual O reader, with its actual O manifest/source identity.
    # No replaced TARGET/global/source map is used to make this preflight pass.
    fresh = driver.preflight(s, O, REMAINING)
    require(fresh.active == state.active and fresh.graph == state.prior_spec.graph and
            fresh.sources == state.prior_spec.sources and fresh.order == REMAINING and
            len(fresh.dependency_pins) == 144 and set(fresh.initial_owners) == set(ORIGINAL_TARGETS) and
            all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
            fresh.initial_owners[PRIOR]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
            fresh.dependency_pins[PRIOR] == state.artifacts[PRIOR] and
            fresh.supplier_evidence == state.result['original_supplier_acceptance_bindings'],
            'unchanged O thirteen-target preflight or original accepted identities differ')
    unchanged(c, state, setup_absent=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_O_PREFLIGHT.json', {'source_commit': O, 'targets': fresh.order,
        'active_source_count': len(fresh.active), 'preserved_dependency_count': len(fresh.dependency_pins),
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require((PROJECT / SOURCE).read_bytes() == c.before and file_fp(c, PROJECT / SOURCE) == BEFORE,
            'AllK source preimage changed before original single-source installer')
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    require(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True,
            'original installer did not perform exactly one AllK source mutation')
    backup = run / 'backups' / SOURCE
    require(file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
            (PROJECT / SOURCE).read_bytes() == c.after, 'exact source backup/postimage differs')
    # Post-install preservation uses a separate snapshot expectation. The O
    # preflight/manifest is never relabelled as an acceptance of the repaired file.
    post_spec = copy.copy(fresh)
    post_spec.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline)
    expected['selected_live_sources'][TARGET] = AFTER['sha256']
    require(driver.snapshot(s, post_spec) == expected, 'post-install dependency/runtime context changed')
    unchanged(c, state, setup_absent=True, source_after=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    require(graph == {m: fresh.graph[m] for m in fresh.active} and
            {m: row['sha256'] for m, row in sources.items()} == {m: post_spec.sources[m] for m in fresh.active},
            'post-repair live157 graph differs')
    result = {'status': 'EXACT_SINGLE_ALLK_SOURCE_REPAIR_VERIFIED_NOT_COMPILED', 'identity': c.identity,
        'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_O_thirteen_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359,
        'active_source_count': 157, 'preserved_dependency_count': 144, 'watched_module_count': 160,
        'original_PerGroup_O_full_acceptance_preserved': True,
        'original_O_evidence_and_other_artifacts_unchanged': True,
        'runtime_configuration_and_Git_state_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True, help='published updater execution commit Q')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.check:
        require(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_ALLK_PREFLIGHT_ONLY', 'identity': c.identity,
            'original_PerGroup_O_full_acceptance_preserved': True, 'published_source_count': 360,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_O_thirteen_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        require(run.is_absolute() and run.resolve() == run and run.parent == runs and
                re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected AllK repair worker path')
        try:
            result = apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_ALLK_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
                     mutated_modules=[TARGET], new_lean_acceptance=False, path=str(run / 'SOURCE_REPAIR_RESULT.json'))
        return 0
    require(runs.resolve() == runs, 'repair evidence parent must not traverse symlinks')
    run = c.s.d.attempt(runs)
    require(run.resolve() == run, 'repair evidence directory must not traverse symlinks')
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-repair.py'
    c.s.d.write_frozen(executed, c.script)
    try:
        command = c.s.ops.run(run, 'serialized-source-repair', c.s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--apply', '--inside-lane', str(run)]), relay=True)
        require(command['exit_code'] == 0 and command['actual_built_modules'] == [] and
                command['actual_failed_modules'] == [], 'serialized AllK repair held; inspect private failure evidence')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty Git state changed')
    return 0


if __name__ == '__main__':
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'EXACT_SINGLE_ALLK_HELD', 'error_type': type(error).__name__,
                          'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
