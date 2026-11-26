#!/usr/bin/env python3
"""Apply the exact failed-HB name qualification and preserve original evidence.

Three later sources already exist without any artifacts and receive the same
exact qualification. The absent AtlasRough source stays absent until the
original additive installer selects that owner.
This entrypoint never invokes Lean, Lake, the kernel, or a readiness build.
"""
import argparse
import contextlib
import copy
import hashlib
import io
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
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-qualified-dyadic-repair-v1')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-qualified-dyadic-repair/'
SCRIPT = PREFIX + 'apply_source_repair.py'
MANIFEST = PREFIX + 'REPAIR_MANIFEST.json'
MANIFEST_SHA = '012909e00c13fa1bde452a5c6c12f28eb3a066a339b8a5a022574a9759935ce6'
FAILED = '7ca00b5fcc24e188a53d3a645808d388a5b9e6d1'
FAILED_JOB = 'job_7292274bc17b4af7b07b528d872e02b9'
OLD_DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
OLD_DRIVER_SHA = '035798dde6cf355355912c60e5c23805d07b201a6ddc0ffe1115aaff3da5167b'
SUPPORT_COMMIT = '3d292e4cd193ab422ca990e80a25165d5aca33a1'
SUPPORT_READER = 'docs/p1/20261125/p15-current-public-acceptance/collect_support_current.py'
SUPPORT_READER_SHA = '06204d53491d1ba858a119cd6de1488aea5076470a057def46e5fc987f39186b'
SUPPORT_PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json'
SUPPORT_PUBLIC_SHA = '25a6333e4b89b03ca541d72a26b5d7f9273849bb7cc8aed6cc351db99bbc3c1a'
SUPPORT = 'ImbalancedChen.P1OriginalSingletonSupportData'
TARGET = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
COMPANION = 'ImbalancedChen.P1OriginalSingletonCutoffData'
PAIR = [TARGET, COMPANION]
FUTURE = ['ImbalancedChen.P5LicensedOriginalIntegerProfile',
          'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
          'ImbalancedChen.Part3AllKLambdaChartCorrection',
          'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
REPAIRED = [TARGET] + FUTURE[:3]
ABSENT_FUTURE = FUTURE[3:]
PUBLISHED_REPAIRS = [TARGET] + FUTURE
BEFORE_SHA = '15c3a939529b5af6133467b8922e7fa8179218b127c31bd22bd9e535de3df569'
AFTER_SHA = '00af3647913f94a08870c659a6a051858e4b4f39c39db460861693e67b73694e'
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalPrimeChartHBWitnesses.setup.json'
SETUP_FP = {'bytes': 6328085, 'sha256': '99cad186ff4aa90dee75dfed9f9c858d4ee2f518f49d1903ef353d5ef181dd3a'}


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
    require(re.fullmatch('[0-9a-f]{40}', commit) and
            re.fullmatch('[0-9a-f]{64}', MANIFEST_SHA) and isinstance(SETUP_FP, dict),
            'publication and actual failure inputs must be frozen')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source publication must be a commit')
    require(Path(__file__).read_bytes() == git_file(commit, SCRIPT), 'executed repair script differs')
    raw = git_file(commit, MANIFEST)
    require(sha(raw) == MANIFEST_SHA, 'repair manifest differs')
    repair = json.loads(raw)
    require(repair['schema'] == 'p15_qualified_dyadic_source_repair_v1' and
            repair['failed_source_commit'] == FAILED and repair['failed_job'] == FAILED_JOB and
            repair['failed_owner'] == TARGET and repair['first_targets'] == PAIR and
            repair['live_repaired_modules'] == REPAIRED and
            repair['future_absent_source_modules'] == ABSENT_FUTURE and
            [row['module'] for row in repair['repairs']] == PUBLISHED_REPAIRS and
            repair['failed_setup_preservation']['fingerprint'] == SETUP_FP,
            'fixed failed-owner and absent-future scope differs')
    for binding in repair['unchanged_inputs']:
        require(binding['commit'] == FAILED, 'unexpected retained input commit')
        check_bytes(git_file(FAILED, binding['path']), binding)
        check_bytes(git_file(commit, binding['path']), binding)
    code = git_file(FAILED, OLD_DRIVER)
    require(sha(code) == OLD_DRIVER_SHA, 'original D correction driver differs')
    file = OLD_ROOT / FAILED / 'published-entrypoints/run_selected.py'
    require(file.is_file() and not file.is_symlink() and file.resolve() == file and
            file.read_bytes() == code, 'original D executed entrypoint differs')
    driver = ModuleType('original_D_qualification_repair_reader')
    driver.__file__ = str(file)
    exec(compile(code, str(file), 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, OLD_ROOT),
            'original D environment differs')
    return driver, driver.helpers(), repair, raw


def payloads(commit, repair):
    before, after = {}, {}
    for row in repair['repairs']:
        module, path = row['module'], row['path']
        require(path == module.replace('.', '/') + '.lean', 'source path differs')
        old, new = git_file(FAILED, path), git_file(commit, path)
        check_bytes(old, row['before'])
        check_bytes(new, row['after'])
        pieces, cursor = [], 0
        for splice in row['exact_byte_splices']:
            lo, hi = splice['pre_start_byte'], splice['pre_end_byte']
            require(type(lo) is int and type(hi) is int and cursor <= lo < hi <= len(old),
                    'invalid qualification interval')
            removed, added = splice['old_utf8'].encode(), splice['new_utf8'].encode()
            require(old[lo:hi] == removed and removed != added, 'qualification splice differs')
            pieces.extend((old[cursor:lo], added))
            cursor = hi
        pieces.append(old[cursor:])
        require(row['exact_byte_splices'] and b''.join(pieces) == new and old != new,
                'postimage is not the exact published qualification')
        before[module], after[module] = old, new
    require(list(before) == PUBLISHED_REPAIRS and sha(before[TARGET]) == BEFORE_SHA and
            sha(after[TARGET]) == AFTER_SHA, 'qualification payload coverage differs')
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


def support_evidence_files(driver, s):
    folders = [OLD_ROOT / SUPPORT_COMMIT / SUPPORT,
               OLD_ROOT / SUPPORT_COMMIT / 'runs/attempt-00000' / SUPPORT]
    result = {}
    for folder in folders:
        require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder,
                'accepted Support evidence root differs')
        count = 0
        for path in sorted(folder.rglob('*')):
            require(not path.is_symlink() and path.resolve() == path,
                    'accepted Support evidence contains a nonregular path')
            if path.is_dir():
                continue
            result[str(path)] = driver.regular_fingerprint(s, path)
            count += 1
        require(count > 0, 'accepted Support evidence root is empty')
    return result


def original_support(commit):
    code = git_file(FAILED, SUPPORT_READER)
    public = git_file(FAILED, SUPPORT_PUBLIC)
    require(sha(code) == SUPPORT_READER_SHA and sha(public) == SUPPORT_PUBLIC_SHA and
            code == git_file(commit, SUPPORT_READER) and public == git_file(commit, SUPPORT_PUBLIC),
            'fixed original Support collector or public receipt differs')
    reader = ModuleType('unchanged_original_B_support_collector')
    reader.__file__ = SUPPORT_READER
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        exec(compile(code, SUPPORT_READER, 'exec'), reader.__dict__)
    require(output.getvalue().encode() == public, 'original Support revalidation differs from public pins')
    require(reader.commit == SUPPORT_COMMIT and reader.module == SUPPORT and
            len(reader.spec.active) == 109, 'original Support identity or closure differs')
    return reader


def bind_failed_evidence(driver, s, spec, repair, artifacts):
    data = {}
    for row in repair['failed_evidence']:
        path = Path(row['path'])
        require(path.is_relative_to(OLD_ROOT / FAILED), 'failure evidence is outside original D')
        data[str(path)] = driver.retained_read(s, spec, path,
                                             {k: row[k] for k in ('bytes', 'sha256')})
    run = OLD_ROOT / FAILED / 'runs/attempt-00000'
    folder = OLD_ROOT / FAILED / TARGET / 'normal' / TARGET / 'attempt-00000'
    result = json.loads(data[str(run / 'RESULT.json')])
    require(result['source_commit'] == FAILED and result['targets'] == PAIR and
            result['accepted_owners'] == [] and set(result['failures']) == {TARGET} and
            result['acceptance_bindings'] == {} and result['worker_exit_code'] == 1 and
            result['all_selected_owners_accepted'] is False and
            not any(k in result for k in ('context_error', 'final_context_error', 'git_error')),
            'original D failure scope differs')
    for stem in ('CONTEXT', 'GIT'):
        require(data[str(run / (stem + '_BEFORE.json'))] == data[str(run / (stem + '_AFTER.json'))],
                'original D failure did not preserve its context')
    require(data[str(run / 'executed-driver.py')] == git_file(FAILED, OLD_DRIVER),
            'failed executed driver differs')
    ready = result['direct_import_readiness'][TARGET]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'original D import readiness differs')
    command = json.loads(data[str(folder / 'normal-command.json')])
    log = folder / 'normal.log'
    require(command['argv'] == s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean']) and
            command['cwd'] == str(PROJECT) and command['exit_code'] == 1 and
            command['actual_built_modules'] == [] and command['actual_failed_modules'] == [TARGET] and
            command['log'] == str(log) and command['log_bytes'] == len(data[str(log)]) and
            command['log_sha256'] == sha(data[str(log)]), 'original D normal identity differs')
    context = json.loads(data[str(folder / 'CONTEXT_BEFORE.json')])
    own = s.h.closure(spec.graph, [TARGET])
    objects = {'.lake/build/lib/lean/' + m.replace('.', '/') + ext:
               artifacts[m]['.lake/build/lib/lean/' + m.replace('.', '/') + ext]
               for m in own - {TARGET} for ext in ('.olean', '.trace')}
    require(len(own) == 67 and all(value is not None for value in objects.values()) and
            context == {'source_commit': FAILED,
                        'project_sources': {m: spec.sources[m] for m in sorted(own)},
                        'dependency_objects_and_traces': objects,
                        'configuration': spec.review['runtime_configuration_bindings'],
                        'existing_runtime': spec.review['existing_runtime_bindings']},
            'original D normal context or live dependency bytes differ')
    require(not os.path.lexists(folder.parent / 'NORMAL_PASS.json'),
            'failed HB now has a normal receipt; inspect before repair')
    require(not os.path.lexists(OLD_ROOT / FAILED / COMPANION / 'normal'),
            'Cutoff has since been attempted; inspect before repair')


# The archive operations below are copied verbatim from publication C. Only
# this file's frozen D job, root and manifest constants change their identity.
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


def original_D_readonly_context(driver, s, commit):
    """Validate D's context while the one inspected failed setup still exists.

No existing_owner/fresh gate is bypassed or modified: the unchanged complete
D preflight runs after that exact file has been durably archived and removed,
before any source replacement. This first phase uses the original read-only
source/supplier/dependency APIs, as the preceding C repair did.
    """
    manifest, graph, sources, observed, inputs = driver.source_manifest(s, FAILED, PAIR)
    active = s.h.closure(graph, PAIR)
    require(len(graph) == 360 and len(active) == 68 and
            active & set(driver.TARGETS) == set(PAIR) and
            not active.intersection(manifest['unaccepted_p3_dependencies']) and
            not active.intersection(manifest['previously_accepted_targets']),
            'original D read-only selected graph differs')
    review_raw = driver.pinned(FAILED, driver.REVIEW, driver.REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        check_bytes(git_file(FAILED, path), expected)
        check_bytes(git_file(commit, path), expected)
    actual_graph, actual = s.h.project_graph(PROJECT, PAIR)
    require(actual_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in actual.items()} == {m: sources[m] for m in active},
            'original D installed selected source graph differs')
    code = git_file(FAILED, OLD_DRIVER)
    spec = SimpleNamespace(manifest=manifest, graph=graph, sources=sources, observed=observed,
        review=review, active=active, selected=set(PAIR), order=s.d.compile_order([], PAIR, graph),
        input_bindings={**inputs,
            'runtime_review': {'path': driver.REVIEW, 'bytes': len(review_raw), 'sha256': sha(review_raw)},
            'runner': {'path': OLD_DRIVER, 'bytes': len(code), 'sha256': sha(code)}},
        retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    driver.environment(s, review)
    for module in sorted(active & set(manifest['accepted_suppliers'])):
        driver.retained_owner(s, spec, module, validate_live=True)
        spec.dependency_pins[module] = driver.module_artifacts(s, module)
    for module in sorted(active & set(manifest['fixed_dependencies'])):
        spec.dependency_pins[module] = driver.fixed_dependency_pins(s, spec, module)
    require(len(spec.supplier_evidence) == 8 and len(spec.dependency_pins) == 66 and
            set(spec.dependency_pins) == active - set(PAIR), 'D dependency preservation inventory differs')
    return spec


def prepare(driver, s, commit, repair):
    before, after = payloads(commit, repair)
    spec = original_D_readonly_context(driver, s, commit)
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(commit, row['path'])
        require(raw == (after[module] if module in after else git_file(FAILED, row['path'])) and
                s.h.imports(raw) == row['all_imports'], 'unrelated published source or import changed')
    support = original_support(commit)
    require(all(not set(PUBLISHED_REPAIRS) & s.h.closure(spec.graph, [m])
                for m in spec.manifest['accepted_suppliers']) and
            not set(PUBLISHED_REPAIRS) & support.spec.active and
            not set(FUTURE) & spec.active, 'qualification intersects an accepted source closure')
    watch = spec.active | support.spec.active | set(driver.TARGETS)
    require(len(spec.active | support.spec.active) == 130 and len(watch) == 148,
            'read-only preservation scope differs')
    artifacts = {m: driver.module_artifacts(s, m) for m in sorted(watch)}
    watched_sources = source_watch(driver, watch)
    for module in REPAIRED:
        require(watched_sources[module] == {'bytes': len(before[module]), 'sha256': sha(before[module])},
                'live source is not the inspected D preimage; no repeated mutation')
    for module in FUTURE:
        driver.require_fresh_owner(module, artifacts[module])
    for module in ABSENT_FUTURE:
        require(watched_sources[module] is None, 'absent future source appeared; inspect before installation')
    require(len(artifacts[TARGET]) == 21 and SETUP in artifacts[TARGET] and
            all(value is None for path, value in artifacts[TARGET].items() if path != SETUP) and
            artifacts[TARGET][SETUP] in (None, SETUP_FP),
            'unexpected HB artifact; only the inspected failed setup is eligible')
    prior = prior_archive(driver, s, spec, commit) if artifacts[TARGET][SETUP] is None else {}
    driver.require_fresh_owner(COMPANION, artifacts[COMPANION])
    bind_failed_evidence(driver, s, spec, repair, artifacts)
    files = support_evidence_files(driver, s)
    require(artifacts[SUPPORT] == support.spec.initial_owners[SUPPORT]['artifacts'],
            'Support outputs changed after its original B validation')
    public_pins = support.result['owners'][SUPPORT]['receipt_bindings']
    require(all(files.get(str(path)) == public_pins[key] for key, path in support.paths.items()),
            'Support public receipt pins changed before preservation baseline')
    support_baseline = support.driver.snapshot(support.s, support.spec)
    return SimpleNamespace(spec=spec, before=before, after=after, watch=watch,
        artifacts=artifacts, watched_sources=watched_sources, baseline=driver.snapshot(s, spec),
        prior_archive=prior, support=support, support_baseline=support_baseline, support_files=files)


def unchanged_support(driver, s, state):
    return (state.support.driver.snapshot(state.support.s, state.support.spec) == state.support_baseline and
            support_evidence_files(driver, s) == state.support_files)


def apply_repair(driver, s, commit, repair, raw, run):
    s.d.verify_lane(s.h)
    state = prepare(driver, s, commit, repair)
    updates = [{'module': module, 'path': module.replace('.', '/') + '.lean',
                'before_sha256': sha(state.before[module]), 'after_sha256': sha(state.after[module]),
                'cloud_source_mutation_required': True} for module in REPAIRED]
    s.d.write_frozen(run / 'REPAIR_MANIFEST.json', raw)
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {
        'source_commit': commit, 'failed_source_commit': FAILED, 'updates': updates,
        'published_source_count': 360, 'D_selected_source_count': 68, 'watch_module_count': 148,
        'context_before': state.baseline, 'sources_before': state.watched_sources,
        'artifacts_before': state.artifacts, 'Support_original_B_context': state.support_baseline,
        'Support_original_B_evidence_files': state.support_files, 'new_lean_acceptance': False})
    require(driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == state.artifacts,
            'preserved state changed before exact repair')
    preservation = preserve_failed_setup(driver, s, commit, state, run)
    expected_artifacts = copy.deepcopy(state.artifacts)
    expected_artifacts[TARGET][SETUP] = None
    require({m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts and
            driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources,
            'setup archive changed another source, artifact, runtime or receipt')
    driver.require_fresh_owner(TARGET, expected_artifacts[TARGET])
    driver.require_fresh_owner(COMPANION, expected_artifacts[COMPANION])
    for module in FUTURE:
        driver.require_fresh_owner(module, expected_artifacts[module])
    fresh = driver.preflight(s, FAILED, PAIR)
    require(fresh.active == state.spec.active and fresh.sources == state.spec.sources and
            fresh.dependency_pins == state.spec.dependency_pins and
            set(fresh.initial_owners) == set(PAIR) and
            all(owner['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT'
                for owner in fresh.initial_owners.values()), 'unchanged full D freshness preflight differs')
    require(driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts,
            'read-only full D preflight changed a preserved binding')
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    records = s.h.install_sources(PROJECT, updates,
        {module.replace('.', '/') + '.lean': state.after[module] for module in REPAIRED}, run / 'backups')
    require([record['module'] for record in records] == REPAIRED and all(r['mutated'] for r in records),
            'exact four-source mutation differs')
    for module in REPAIRED:
        backup = run / 'backups' / (module.replace('.', '/') + '.lean')
        require(backup.is_file() and not backup.is_symlink() and backup.read_bytes() == state.before[module],
                'exact source preimage backup differs')
        state.spec.sources[module] = sha(state.after[module])
    expected = copy.deepcopy(state.baseline)
    expected['selected_live_sources'][TARGET] = AFTER_SHA
    expected_sources = copy.deepcopy(state.watched_sources)
    for module in REPAIRED:
        expected_sources[module] = {'bytes': len(state.after[module]), 'sha256': sha(state.after[module])}
    require(driver.snapshot(s, state.spec) == expected and unchanged_support(driver, s, state) and
            source_watch(driver, state.watch) == expected_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts and
            all(driver.regular_fingerprint(s, Path(path)) == value
                for path, value in preservation['bindings'].items()),
            'unrelated source, Support evidence or artifact changed')
    actual_graph, actual = s.h.project_graph(PROJECT, PAIR)
    require(actual_graph == {m: state.spec.graph[m] for m in state.spec.active} and
            {m: row['sha256'] for m, row in actual.items()} ==
            {m: state.spec.sources[m] for m in state.spec.active}, 'post-repair selected graph differs')
    result = {'status': 'EXACT_HB_QUALIFIED_NAME_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'source_commit': commit, 'failed_source_commit': FAILED, 'failed_job': FAILED_JOB,
        'repair_records': records, 'context_after': expected, 'sources_after': expected_sources,
        'failed_setup_preservation': preservation, 'original_D_suppliers_preserved': 8,
        'Support_original_B_context_after': state.support_baseline,
        'Support_original_B_evidence_files': state.support_files,
        'accepted_Support_preserved_at_original_B': True, 'future_sources_still_absent': ABSENT_FUTURE,
        'full_unchanged_D_preflight_passed_after_setup_archive': True,
        'all_other_artifacts_and_original_receipts_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', result)
    return REPAIRED


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
        print(json.dumps({'status': 'EXACT_HB_QUALIFICATION_PREFLIGHT_ONLY', 'source_commit': commit,
            'current_source_sha256': BEFORE_SHA, 'postimage_sha256': AFTER_SHA,
            'published_sources': 360, 'D_selected_sources': 68, 'watched_modules': 148,
            'accepted_Support_preserved_at_B': True, 'future_sources_absent': ABSENT_FUTURE,
            'planned_live_source_repairs': REPAIRED,
            'planned_exact_setup_archive': state.artifacts[TARGET][SETUP] is not None,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    base = ROOT / commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'unexpected qualification worker path')
        try:
            mutated = apply_repair(driver, s, commit, repair, raw, run)
        except Exception as error:
            s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'source_commit': commit,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            print(json.dumps({'status': 'EXACT_HB_QUALIFICATION_HELD',
                              'error_type': type(error).__name__}), flush=True)
            return 1
        print(json.dumps({'status': 'EXACT_HB_QUALIFICATION_SOURCE_REPAIR_VERIFIED',
            'source_commit': commit, 'mutated_modules': mutated,
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
        require(command['exit_code'] == 0, 'serialized exact qualification held; inspect failure evidence')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty Git state changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    raise SystemExit(main())
