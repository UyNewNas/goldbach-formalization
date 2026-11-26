#!/usr/bin/env python3
"""Repair HBWitnesses and its Cutoff notation companion; preserve Support at B.

Publication C contains the exact two repaired sources and this entrypoint while
retaining the original B correction driver/manifest/installer/static verifier.
D separately re-anchors that driver and keeps the original Support B identity.
This script never builds. Unknown or incomplete evidence holds before mutation.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-hb-witness-api-repair-v1')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-hb-witness-api-repair/'
SCRIPT = PREFIX + 'apply_source_repair.py'
MANIFEST = PREFIX + 'REPAIR_MANIFEST.json'
MANIFEST_SHA = 'd6388f3a7c91f5cbd273883102c46dcd21abd48ed077731fb415f1268ca0afb6'
FAILED = '3d292e4cd193ab422ca990e80a25165d5aca33a1'
FAILED_JOB = 'job_216f3dbd13b24dab8524da9ada0cac1b'
OLD_DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
OLD_DRIVER_SHA = 'ad45eb501f9a89ce1e594497a7105e4f3fac3587963e9249f40021691a82d725'
TARGET = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
SOURCE = 'ImbalancedChen/P5OriginalPrimeChartHBWitnesses.lean'
SUPPORT = 'ImbalancedChen.P1OriginalSingletonSupportData'
COMPANION = 'ImbalancedChen.P1OriginalSingletonCutoffData'
REPAIRED = [TARGET, COMPANION]
FIRST3 = [SUPPORT, TARGET, COMPANION]
BEFORE_SHA = {
    TARGET: '93858742e3c6fd13e69bea47e0c92af273d913784a96f10ac03883a6a8823075',
    COMPANION: '3e78ff44ad0e6fdea017402b6ff2b431a81c9c9c01a12611c8b405aad22e9cc4'}
# Both postimages are the fixed three-notation source repairs.
AFTER_SHA = {
    TARGET: '15c3a939529b5af6133467b8922e7fa8179218b127c31bd22bd9e535de3df569',
    COMPANION: 'c61b80c930959e86f310299c8c4b1d0b86d358320f08a89be404dbadc33c8b1d'}
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalPrimeChartHBWitnesses.setup.json'
SETUP_FP = {'bytes': 6328085,
            'sha256': '99cad186ff4aa90dee75dfed9f9c858d4ee2f518f49d1903ef353d5ef181dd3a'}



def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def check_bytes(raw, binding):
    actual = {'bytes': len(raw), 'sha256': sha(raw)}
    if 'git_blob' in binding:
        actual['git_blob'] = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    require(all(binding.get(k) == v for k, v in actual.items()), 'fixed byte binding differs')


def load(commit):
    require(__debug__, 'immutable installer requires Python assertions')
    require(isinstance(MANIFEST_SHA, str) and re.fullmatch('[0-9a-f]{64}', MANIFEST_SHA) and
            isinstance(SETUP_FP, dict), 'repair inputs are not frozen; actual failure evidence required')
    require(re.fullmatch('[0-9a-f]{40}', commit), 'full publication-C commit required')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'publication C must be a commit')
    require(Path(__file__).read_bytes() == git_file(commit, SCRIPT), 'executed repair script differs')
    raw = git_file(commit, MANIFEST)
    require(sha(raw) == MANIFEST_SHA, 'repair manifest differs')
    repair = json.loads(raw)
    require(repair['schema'] == 'p15_hb_witness_cutoff_api_source_repair_v1' and
            repair['failed_source_commit'] == FAILED and repair['failed_job'] == FAILED_JOB and
            repair['failed_owner'] == TARGET and repair['accepted_owner_preserved'] == SUPPORT and
            repair['first_targets'] == FIRST3 and
            [row['module'] for row in repair['repairs']] == REPAIRED,
            'fixed failed-owner/companion/accepted-owner scope differs')
    for row in repair['repairs']:
        module = row['module']
        require(row['path'] == module.replace('.', '/') + '.lean' and
                row['before']['sha256'] == BEFORE_SHA[module] and
                row['after']['sha256'] == AFTER_SHA[module], 'fixed source repair differs')
    setup = repair['failed_setup_preservation']
    require(setup['path'] == str(PROJECT / SETUP) and setup['relative_path'] == SETUP and
            {k: setup[k] for k in SETUP_FP} == SETUP_FP and
            setup['all_other_target_artifacts_must_be_absent'] == 20 and
            setup['companion_has_no_artifact_exception'] is True,
            'failed setup preservation scope differs')
    for binding in repair['unchanged_inputs']:
        require(binding['commit'] == FAILED, 'unexpected old input commit')
        check_bytes(git_file(FAILED, binding['path']), binding)
        check_bytes(git_file(commit, binding['path']), binding)
    code = git_file(FAILED, OLD_DRIVER)
    require(sha(code) == OLD_DRIVER_SHA, 'original correction driver differs')
    driver = ModuleType('pinned_original_correction_driver')
    driver.__file__ = OLD_DRIVER
    exec(compile(code, OLD_DRIVER, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, OLD_ROOT),
            'original environment differs')
    return driver, driver.helpers(), repair, raw


def payloads(commit, repair):
    before, after = {}, {}
    for row in repair['repairs']:
        module, path = row['module'], row['path']
        old, new = git_file(FAILED, path), git_file(commit, path)
        check_bytes(old, row['before'])
        check_bytes(new, row['after'])
        pieces, cursor = [], 0
        for splice in row['exact_byte_splices']:
            lo, hi = splice['pre_start_byte'], splice['pre_end_byte']
            require(type(lo) is int and type(hi) is int and cursor <= lo < hi <= len(old),
                    'invalid repair interval')
            removed, added = splice['old_utf8'].encode(), splice['new_utf8'].encode()
            require(old[lo:hi] == removed and removed != added, 'repair splice differs')
            pieces.extend((old[cursor:lo], added))
            cursor = hi
        pieces.append(old[cursor:])
        require(row['exact_byte_splices'] and b''.join(pieces) == new and old != new,
                'postimage is not the fixed exact splice repair')
        before[module], after[module] = old, new
    require(list(before) == REPAIRED and list(after) == REPAIRED, 'repair payload coverage differs')
    return before, after


def source_watch(driver, modules):
    result = {}
    for module in sorted(modules):
        path = PROJECT / (module.replace('.', '/') + '.lean')
        require(path.parent == PROJECT / 'ImbalancedChen' and path.parent.resolve() == path.parent and
                not path.is_symlink(), 'unexpected watched source path')
        result[module] = None if not os.path.lexists(path) else {
            'bytes': path.stat().st_size, 'sha256': driver.file_binding(path)}
    return result


def bind_failed_evidence(driver, s, spec, repair, old_sources, artifacts):
    data = {}
    for row in repair['failed_evidence']:
        path = Path(row['path'])
        require(path.is_relative_to(OLD_ROOT / FAILED), 'failure evidence is outside its original root')
        data[str(path)] = driver.retained_read(s, spec, path,
                                             {k: row[k] for k in ('bytes', 'sha256')})
    run = OLD_ROOT / FAILED / 'runs/attempt-00000'
    folder = OLD_ROOT / FAILED / TARGET / 'normal' / TARGET / 'attempt-00000'
    result = json.loads(data[str(run / 'RESULT.json')])
    require(result['source_commit'] == FAILED and set(result['targets']) == set(FIRST3) and
            result['accepted_owners'] == [SUPPORT] and set(result['failures']) == {TARGET} and
            set(result['acceptance_bindings']) == {SUPPORT} and
            not any(k in result for k in ('context_error', 'final_context_error', 'git_error')),
            'failed run scope or the accepted Support identity differs')
    ready = result['direct_import_readiness'][TARGET]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'failed run import readiness differs')
    command = json.loads(data[str(folder / 'normal-command.json')])
    log = folder / 'normal.log'
    require(command['argv'] == s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean']) and
            command['cwd'] == str(PROJECT) and command['exit_code'] == 1 and
            command['actual_built_modules'] == [] and command['actual_failed_modules'] == [TARGET] and
            command['log'] == str(log) and command['log_bytes'] == len(data[str(log)]) and
            command['log_sha256'] == sha(data[str(log)]), 'failed normal identity differs')
    context = json.loads(data[str(folder / 'CONTEXT_BEFORE.json')])
    own = s.h.closure(spec.graph, [TARGET])
    objects = {'.lake/build/lib/lean/' + m.replace('.', '/') + ext:
               artifacts[m]['.lake/build/lib/lean/' + m.replace('.', '/') + ext]
               for m in own - {TARGET} for ext in ('.olean', '.trace')}
    require(len(own) == 67 and all(value is not None for value in objects.values()) and
            context == {'source_commit': FAILED,
                        'project_sources': {m: old_sources[m] for m in sorted(own)},
                        'dependency_objects_and_traces': objects,
                        'configuration': spec.review['runtime_configuration_bindings'],
                        'existing_runtime': spec.review['existing_runtime_bindings']},
            'failed normal context or its live dependency bytes differ')
    require(not os.path.lexists(folder.parent / 'NORMAL_PASS.json'),
            'failed target now has a normal receipt; inspect before repair')
    return result


def support_evidence_files(driver, s):
    folders = [OLD_ROOT / FAILED / SUPPORT,
               OLD_ROOT / FAILED / 'runs/attempt-00000' / SUPPORT]
    result = {}
    for folder in folders:
        require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder,
                'accepted Support evidence root differs')
        files = []
        for path in sorted(folder.rglob('*')):
            require(not path.is_symlink() and path.resolve() == path,
                    'accepted Support evidence contains a nonregular path')
            if path.is_dir():
                continue
            result[str(path)] = driver.regular_fingerprint(s, path)
            files.append(path)
        require(files, 'accepted Support evidence root is empty')
    return result


def bind_accepted_support(driver, s, spec, failed_result, public):
    owner = public['owners'][SUPPORT]
    require(public['schema'] == 'p15_support_B_original_public_acceptance_v1' and
            public['source_commit'] == FAILED and public['compiler_job'] == FAILED_JOB and
            public['published_source_count'] == 360 and public['selected_owner_live_closure_count'] == 109 and
            public['original_group_worker_exit_code'] == 1 and
            public['normal_or_kernel_commands_executed'] == 0 and set(public['owners']) == {SUPPORT} and
            owner['source_commit'] == FAILED and owner['source_sha256'] == spec.sources[SUPPORT] and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            owner['owned_count'] == owner['public_count'] == 5,
            'published original Support identity differs')
    state = driver.existing_owner(s, FAILED, spec, SUPPORT)
    driver.require_completed_existing_owner(s, FAILED, spec, SUPPORT, state)
    binding = driver.acceptance_binding(s, FAILED, SUPPORT)
    require(binding == failed_result['acceptance_bindings'][SUPPORT] and len(binding['audits']) == 1,
            'Support acceptance differs from the fixed original B result')
    audit = Path(binding['audits'][0]['plan']['path']).parent
    refs = {'normal': Path(binding['normal_receipt']['path']), 'audit_plan': audit / 'AUDIT_PLAN.json',
            'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
            'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
            'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
            'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    require(set(owner['receipt_bindings']) == set(refs), 'Support public receipt coverage differs')
    for key, path in refs.items():
        driver.retained_read(s, spec, path, owner['receipt_bindings'][key])
    result = s.api.read_json(refs['audit_result'])
    require(result['total_owned_exports'] == result['total_public_exports'] == 5,
            'Support full-owned coverage differs')
    files = support_evidence_files(driver, s)
    for path, fingerprint in files.items():
        require(spec.retained_inputs.setdefault(path, fingerprint) == fingerprint,
                'Support evidence changed after its public pin was checked')
    return binding, files


def archive_binding(driver, s, commit, receipt):
    run = receipt.parent
    require(run.parent == ROOT / commit / 'runs' and
            re.fullmatch('attempt-[0-9]{5}', run.name) and receipt.resolve() == receipt,
            'unexpected previous setup archive receipt')
    record = s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / 'P5OriginalPrimeChartHBWitnesses.setup.json'
    require(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
            record['source_commit'] == commit and record['failed_source_commit'] == FAILED and
            record['failed_job'] == FAILED_JOB and record['repair_manifest_sha256'] == MANIFEST_SHA and
            record['active_path'] == str(PROJECT / SETUP) and record['archive_path'] == str(archive) and
            record['fingerprint'] == SETUP_FP and record['archive_fsync_verified'] is True and
            archive.resolve() == archive and driver.regular_fingerprint(s, archive) == SETUP_FP,
            'previous setup archive is not the exact authorized file')
    return {str(receipt): driver.regular_fingerprint(s, receipt), str(archive): SETUP_FP}


def prior_archive(driver, s, spec, commit):
    receipts = sorted((ROOT / commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    require(receipts, 'active setup is absent without a retained authorized archive')
    retained = {}
    for receipt in receipts:
        retained.update(archive_binding(driver, s, commit, receipt))
    for path, expected in retained.items():
        driver.retained_read(s, spec, Path(path), expected)
    return retained


def fsync_directory(path):
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def preserve_failed_setup(driver, s, commit, state, run):
    if state.artifacts[TARGET][SETUP] is None:
        return {'action': 'ALREADY_ARCHIVED_AND_ABSENT', 'bindings': state.prior_archive}
    path = PROJECT / SETUP
    require(path.resolve() == path and path.is_file() and not path.is_symlink(),
            'failed setup is not the fixed regular path')
    original = path.stat()
    raw = path.read_bytes()
    check_bytes(raw, SETUP_FP)
    archive = run / 'failed-artifacts' / 'P5OriginalPrimeChartHBWitnesses.setup.json'
    archive.parent.mkdir(parents=True, exist_ok=True)
    require(archive.parent.resolve() == archive.parent, 'archive parent is not a regular directory')
    descriptor = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    require(driver.regular_fingerprint(s, archive) == SETUP_FP, 'exclusive setup archive differs')
    for directory in (archive.parent, run, run.parent, run.parent.parent, ROOT, ROOT.parent):
        fsync_directory(directory)
    receipt = run / 'FAILED_SETUP_ARCHIVE.json'
    record = {'status': 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED',
        'source_commit': commit, 'failed_source_commit': FAILED, 'failed_job': FAILED_JOB,
        'repair_manifest_sha256': MANIFEST_SHA, 'active_path': str(path), 'archive_path': str(archive),
        'fingerprint': SETUP_FP, 'archive_fsync_verified': True, 'active_removal_planned': True,
        'original_stat': {'device': original.st_dev, 'inode': original.st_ino,
                          'size': original.st_size, 'mtime_ns': original.st_mtime_ns,
                          'mode': original.st_mode & 0o777}, 'new_lean_acceptance': False}
    s.d.write_frozen(receipt, (json.dumps(record, sort_keys=True, indent=2) + '\n').encode())
    with receipt.open('rb') as stream:
        os.fsync(stream.fileno())
    fsync_directory(run)
    bindings = archive_binding(driver, s, commit, receipt)
    current = path.stat()
    require(not path.is_symlink() and path.resolve() == path and
            (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns) ==
            (original.st_dev, original.st_ino, original.st_size, original.st_mtime_ns) and
            path.read_bytes() == raw, 'active setup changed before its authorized removal')
    # Only this inspected failed configuration is removed, after its complete
    # exclusive archive and metadata are durable and independently hash-checked.
    path.unlink()
    fsync_directory(path.parent)
    require(not os.path.lexists(path), 'failed setup remains active after preservation')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}


def prepare(driver, s, commit, repair):
    manifest, graph, old_sources, observed, binding = driver.source_manifest(s, FAILED, FIRST3)
    before, after = payloads(commit, repair)
    require(all(s.h.imports(before[m]) == s.h.imports(after[m]) for m in REPAIRED),
            'repair changed imports')
    post_sources = dict(old_sources)
    for module, row in manifest['project_sources'].items():
        raw = git_file(commit, row['path'])
        require(raw == (after[module] if module in after else git_file(FAILED, row['path'])),
                'publication C changes an unrelated project source')
        require(s.h.imports(raw) == row['all_imports'], 'publication C changed the import graph')
        post_sources[module] = sha(raw)
    active = s.h.closure(graph, FIRST3)
    watch = active | set(driver.TARGETS)
    suppliers = active & set(manifest['accepted_suppliers'])
    fixed = active & set(manifest['fixed_dependencies'])
    require(len(graph) == 360 and len(active) == 130 and len(watch) == 148 and
            len(suppliers) == 9 and len(fixed) == 118 and active & set(driver.TARGETS) == set(FIRST3) and
            not active.intersection(manifest['unaccepted_p3_dependencies']) and
            all(not set(REPAIRED) & s.h.closure(graph, [m]) for m in manifest['accepted_suppliers']) and
            len(s.h.closure(graph, [SUPPORT])) == 109 and
            not set(REPAIRED) & s.h.closure(graph, [SUPPORT]),
            'published/live preservation scope differs')
    review = json.loads(driver.pinned(FAILED, driver.REVIEW, driver.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        check_bytes(git_file(commit, path), expected)
    actual_graph, actual = s.h.project_graph(PROJECT, FIRST3)
    require(actual_graph == {m: graph[m] for m in active}, 'live import graph differs')
    live_sources = dict(post_sources)
    for module in sorted(active):
        path = PROJECT / s.h.module_path(module)
        require(path.parent.resolve() == path.parent and path.is_file() and not path.is_symlink(),
                'live source is not an existing regular file')
        raw = path.read_bytes()
        require(raw in (before[module], after[module]) if module in after
                else sha(raw) == post_sources[module],
                'unknown preimage or unrelated live source difference')
        live_sources[module] = sha(raw)
    require({m: row['sha256'] for m, row in actual.items()} == {m: live_sources[m] for m in active},
            'source changed during graph inspection')
    spec = SimpleNamespace(manifest=manifest, graph=graph, sources=live_sources, observed=observed,
        review=review, active=active, retained_inputs={}, historical_groups={}, historical_owners={},
        supplier_evidence={}, dependency_pins={}, input_bindings={
            'publication_C': commit, 'failed_source_commit': FAILED, 'old_manifest_binding': binding,
            'repair_manifest_sha256': MANIFEST_SHA, 'accepted_Support_source_commit': FAILED})
    driver.environment(s, review)
    for module in sorted(suppliers):
        driver.retained_owner(s, spec, module, validate_live=True)
        spec.dependency_pins[module] = driver.module_artifacts(s, module)
    for module in sorted(fixed):
        spec.dependency_pins[module] = driver.fixed_dependency_pins(s, spec, module)
    artifacts = {m: driver.module_artifacts(s, m) for m in sorted(watch)}
    failed_result = bind_failed_evidence(driver, s, spec, repair, old_sources, artifacts)
    public_binding = repair['accepted_Support_preservation']['published_summary']
    require(public_binding['path'] ==
            'docs/p1/20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json',
            'published Support summary path differs')
    public_raw = git_file(commit, public_binding['path'])
    check_bytes(public_raw, public_binding)
    public = json.loads(public_raw)
    original_result_pin = {k: repair['failed_evidence'][0][k] for k in ('bytes', 'sha256')}
    require(public['original_result'] == original_result_pin and
            public['source_manifest'] == {'commit': FAILED, 'path': driver.MANIFEST,
                'bytes': binding['manifest']['bytes'], 'sha256': driver.MANIFEST_SHA},
            'Support public result or original B manifest binding differs')
    spec.input_bindings['accepted_Support_public_summary'] = public_binding
    support_binding, support_files = bind_accepted_support(driver, s, spec, failed_result, public)
    spec.dependency_pins[SUPPORT] = artifacts[SUPPORT]
    require(len(spec.dependency_pins) == 128 and set(spec.dependency_pins) == active - set(REPAIRED),
            'dependency pin coverage differs')
    require(len(artifacts[TARGET]) == 21 and SETUP in artifacts[TARGET] and
            all(value is None for path, value in artifacts[TARGET].items() if path != SETUP) and
            artifacts[TARGET][SETUP] in (None, SETUP_FP),
            'unexpected target artifact; only the inspected failed HB setup may be preserved')
    prior = prior_archive(driver, s, spec, commit) if artifacts[TARGET][SETUP] is None else {}
    driver.require_fresh_owner(COMPANION, artifacts[COMPANION])
    baseline = driver.snapshot(s, spec)
    watched_sources = source_watch(driver, watch)
    require(all(watched_sources[m]['sha256'] in (BEFORE_SHA[m], AFTER_SHA[m]) for m in REPAIRED),
            'repair source changed before plan')
    return SimpleNamespace(spec=spec, before=before, after=after, post_sources=post_sources,
        watch=watch, artifacts=artifacts, watched_sources=watched_sources, baseline=baseline,
        prior_archive=prior, support_binding=support_binding, support_files=support_files)


def apply_repair(driver, s, commit, repair, raw, run):
    s.d.verify_lane(s.h)
    state = prepare(driver, s, commit, repair)
    updates = [{'module': m, 'path': m.replace('.', '/') + '.lean', 'before_sha256': BEFORE_SHA[m],
                'after_sha256': AFTER_SHA[m], 'cloud_source_mutation_required': True} for m in REPAIRED]
    payload = {m.replace('.', '/') + '.lean': state.after[m] for m in REPAIRED}
    s.d.write_frozen(run / 'REPAIR_MANIFEST.json', raw)
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {
        'source_commit': commit, 'failed_source_commit': FAILED, 'updates': updates,
        'published_source_count': 360, 'live_source_count': 130, 'watch_module_count': 148,
        'context_before': state.baseline, 'sources_before': state.watched_sources,
        'artifacts_before': state.artifacts, 'accepted_Support_binding': state.support_binding,
        'accepted_Support_evidence_files': state.support_files, 'new_lean_acceptance': False})
    require(driver.snapshot(s, state.spec) == state.baseline and
            source_watch(driver, state.watch) == state.watched_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == state.artifacts and
            support_evidence_files(driver, s) == state.support_files,
            'preserved state changed before source replacement')
    preservation = preserve_failed_setup(driver, s, commit, state, run)
    expected_artifacts = copy.deepcopy(state.artifacts)
    expected_artifacts[TARGET][SETUP] = None
    current_artifacts = {m: driver.module_artifacts(s, m) for m in sorted(state.watch)}
    require(current_artifacts == expected_artifacts and
            driver.snapshot(s, state.spec) == state.baseline and
            source_watch(driver, state.watch) == state.watched_sources and
            support_evidence_files(driver, s) == state.support_files,
            'setup preservation changed another artifact, source, runtime or receipt')
    # Support is an accepted dependency. Only the failed HB target and its
    # unexecuted Cutoff companion receive the unchanged real full fresh gate.
    for module in REPAIRED:
        driver.require_fresh_owner(module, current_artifacts[module])
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    records = s.h.install_sources(PROJECT, updates, payload, run / 'backups')
    require([record['module'] for record in records] == REPAIRED, 'source mutation scope differs')
    for record in records:
        if record['mutated']:
            m = record['module']
            backup = run / 'backups' / (m.replace('.', '/') + '.lean')
            require(backup.is_file() and not backup.is_symlink() and backup.read_bytes() == state.before[m],
                    'exact source preimage backup differs')
    state.spec.sources.update(AFTER_SHA)
    expected = copy.deepcopy(state.baseline)
    expected['selected_live_sources'].update(AFTER_SHA)
    require(driver.snapshot(s, state.spec) == expected, 'runtime/dependency/receipt state changed')
    expected_sources = copy.deepcopy(state.watched_sources)
    for m in REPAIRED:
        expected_sources[m] = {'bytes': len(state.after[m]), 'sha256': AFTER_SHA[m]}
    require(source_watch(driver, state.watch) == expected_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts and
            support_evidence_files(driver, s) == state.support_files and
            all(driver.regular_fingerprint(s, Path(path)) == value
                for path, value in preservation['bindings'].items()),
            'unrelated source, Support evidence or cache changed during repair')
    support_state = driver.existing_owner(s, FAILED, state.spec, SUPPORT)
    driver.require_completed_existing_owner(s, FAILED, state.spec, SUPPORT, support_state)
    require(driver.acceptance_binding(s, FAILED, SUPPORT) == state.support_binding,
            'Support original B acceptance binding changed')
    actual_graph, actual = s.h.project_graph(PROJECT, FIRST3)
    require(actual_graph == {m: state.spec.graph[m] for m in state.spec.active} and
            {m: row['sha256'] for m, row in actual.items()} ==
            {m: state.post_sources[m] for m in state.spec.active}, 'post-repair live graph differs')
    result = {'status': 'EXACT_HB_CUTOFF_SOURCE_REPAIR_VERIFIED_NOT_COMPILED', 'source_commit': commit,
        'failed_source_commit': FAILED, 'failed_job': FAILED_JOB, 'repair_records': records,
        'context_after': expected, 'sources_after': expected_sources,
        'failed_setup_preservation': preservation, 'accepted_Support_binding': state.support_binding,
        'accepted_Support_evidence_files': state.support_files,
        'all_other_artifacts_and_original_receipts_unchanged': True,
        'original_accepted_suppliers_preserved': 9, 'accepted_Support_preserved_at_original_B': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', result)
    return [record['module'] for record in records if record['mutated']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    driver, s, repair, raw = load(commit)
    if args.check:
        require(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(driver, s, commit, repair)
        print(json.dumps({'status': 'EXACT_HB_CUTOFF_REPAIR_PREFLIGHT_ONLY', 'source_commit': commit,
            'current_source_sha256': {m: state.watched_sources[m]['sha256'] for m in REPAIRED},
            'postimage_sha256': AFTER_SHA, 'published_sources': 360, 'live_sources': 130,
            'watched_modules': 148, 'accepted_Support_preserved_at_B': True,
            'planned_exact_setup_archive': state.artifacts[TARGET][SETUP] is not None,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    base = ROOT / commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'unexpected source repair worker path')
        try:
            mutated = apply_repair(driver, s, commit, repair, raw, run)
        except Exception as error:
            s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'source_commit': commit,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            print(json.dumps({'status': 'HB_CUTOFF_SOURCE_REPAIR_HELD',
                              'error_type': type(error).__name__}), flush=True)
            return 1
        print(json.dumps({'status': 'HB_CUTOFF_SOURCE_REPAIR_VERIFIED', 'source_commit': commit,
            'mutated_modules': mutated, 'postimage_sha256': AFTER_SHA,
            'accepted_Support_preserved_at_B': True, 'new_lean_acceptance': False}), flush=True)
        return 0
    run = s.d.attempt(base)
    before = s.d.original_git_state(REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-repair.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    try:
        command = s.ops.run(run, 'serialized-source-repair',
            s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json',
                ['python3', '-B', str(executed), '--source-commit', commit,
                 '--apply', '--inside-lane', str(run)]), relay=True)
        require(command['exit_code'] == 0, 'serialized source repair held; inspect retained failure evidence')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty Git HEAD/status changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    raise SystemExit(main())
