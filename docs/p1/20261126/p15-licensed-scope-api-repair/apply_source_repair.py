#!/usr/bin/env python3
"""Preserve K/F/B acceptance and apply three exact published ContDiff scopes.

--source-commit names publication M; its sources must be exactly fixed L.
Failed Licensed is K/run1; accepted Cutoff is K/run0, HB is F, Support is B.
L and the real failure/probe metadata are fixed independently of M.
The unchanged original K full fifteen-target preflight must pass after the sole
failed setup archive and before the original helper installs three sources.
This updater never invokes Lean, Lake, the kernel or a readiness build.
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
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-licensed-scope-api-repair-v1')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-licensed-scope-api-repair/'
SCRIPT = PREFIX + 'apply_source_repair.py'
MANIFEST = PREFIX + 'REPAIR_MANIFEST.json'
MANIFEST_SHA = '6b153194b1c98baacd60dbcd8bc23341cc991daa5a948299fd2848ab2b6271bd'
SOURCE_ANCHOR = '972c2220d87669869a65c03fa64dc04562e37f0d'
FAILED = '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e'
HB_SOURCE = '080d4178711ae042235104f7f4768649f51da2ab'
HB_JOB = 'job_f0761da7e6124e818d654afef54ff5c5'
HB_PUBLIC_COMMIT = 'f6fdd7fffe17803c60914bf28b39b55715d34464'
FAILED_JOB = 'job_05205bc1d3f7442da9444752ab8a9972'
OLD_DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
OLD_DRIVER_SHA = '575fcc9737d0b239cb0d994ad286ad8cae5dbf4406ca898157d7c2e87782c293'
SUPPORT_COMMIT = '3d292e4cd193ab422ca990e80a25165d5aca33a1'
SUPPORT_READER = 'docs/p1/20261125/p15-current-public-acceptance/collect_support_current.py'
SUPPORT_READER_SHA = '06204d53491d1ba858a119cd6de1488aea5076470a057def46e5fc987f39186b'
SUPPORT_PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json'
SUPPORT_PUBLIC_SHA = '25a6333e4b89b03ca541d72a26b5d7f9273849bb7cc8aed6cc351db99bbc3c1a'
SUPPORT = 'ImbalancedChen.P1OriginalSingletonSupportData'
TARGET = 'ImbalancedChen.P5LicensedOriginalIntegerProfile'
ACCEPTED = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
FAILED_TARGETS = ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary', 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy', 'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime', 'ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward', 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily', 'ImbalancedChen.Part3AllKLambdaChartCorrection', 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound', 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis', 'ImbalancedChen.P5PrimeDivisorMeanCorrection']
REPAIRED = PUBLISHED_REPAIRS = ['ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily']
BEFORE_SHA = '876627ddcd468229d57a5921157445730e57abf71d3157d1874037d761f29f8a'
AFTER_SHA = '675cea556d3f85f4ca5e4e4c197b95ddd11e2e60f85e86de52388fe9b2531679'
SETUP = '.lake/build/ir/ImbalancedChen/P5LicensedOriginalIntegerProfile.setup.json'
SETUP_FP = {'bytes': 6328250, 'sha256': '692e72cd9914cd70c80d62a5c81e4530e3d1c7f8cde7f5f46b590a593e1f4744'}


PUBLICATION_READY = True
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
CUTOFF_JOB = 'job_fce62dd5906d4d26ac8cb17790fbec32'
SOURCE_EVIDENCE_PREFIX = 'docs/p1/20261126/p15-licensed-profile-first-compile-repair/'

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
    require(PUBLICATION_READY and re.fullmatch('[0-9a-f]{40}', commit) and
            re.fullmatch('[0-9a-f]{40}', SOURCE_ANCHOR) and
            re.fullmatch('[0-9a-f]{64}', MANIFEST_SHA) and
            type(SETUP_FP['bytes']) is int and SETUP_FP['bytes'] > 0 and
            re.fullmatch('[0-9a-f]{64}', SETUP_FP['sha256']),
            'DRAFT_BLOCKED: actual Licensed metadata/probe and L publication must be frozen')
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source publication must name a commit')
    require(Path(__file__).read_bytes() == git_file(commit, SCRIPT), 'executed repair script differs')
    raw = git_file(commit, MANIFEST)
    require(sha(raw) == MANIFEST_SHA, 'repair manifest differs')
    repair = json.loads(raw)
    require(repair['schema'] == 'p15_licensed_three_scope_source_repair_v1' and
            repair['status'] == 'FROZEN_EXACT_SOURCE_REPAIR_NOT_NEW_ACCEPTANCE' and
            '__PENDING_' not in raw.decode() and
            repair['source_anchor_commit'] == SOURCE_ANCHOR and
            repair['failed_source_commit'] == FAILED and repair['failed_job'] == FAILED_JOB and
            repair['failed_run'] == 'runs/attempt-00001' and repair['failed_owner'] == TARGET and
            repair['fresh_preflight_targets'] == FAILED_TARGETS and
            repair['live_repaired_modules'] == REPAIRED and
            [row['module'] for row in repair['repairs']] == PUBLISHED_REPAIRS and
            repair['scope_counts'] == {'published_sources': 360, 'live_sources': 157,
                'watch_modules': 160, 'dependencies': 142, 'current_owner_states': 16,
                'fresh_selected_owners': 15, 'original_suppliers': 13, 'fixed_dependencies': 126} and
            repair['failed_setup_preservation']['fingerprint'] == SETUP_FP,
            'fixed three-scope source repair differs')
    for binding in repair['historical_K_inputs']:
        require(binding['commit'] == FAILED, 'historical failed input is not K')
        check_bytes(git_file(FAILED, binding['path']), binding)
    for binding in repair['historical_F_HB_inputs']:
        require(binding['commit'] == HB_SOURCE, 'historical accepted HB input is not F')
        check_bytes(git_file(HB_SOURCE, binding['path']), binding)
    for binding in repair['unchanged_shared_inputs']:
        require(binding['commit'] == FAILED, 'shared input origin is not K')
        check_bytes(git_file(FAILED, binding['path']), binding)
        check_bytes(git_file(commit, binding['path']), binding)
    for key in ('actual_bounded_metadata', 'actual_probe_result', 'candidate_provenance', 'accepted_Cutoff_public'):
        binding = repair[key]
        require(binding['commit'] == SOURCE_ANCHOR, 'new public evidence is not bound to L')
        check_bytes(git_file(SOURCE_ANCHOR, binding['path']), binding)
        check_bytes(git_file(commit, binding['path']), binding)
    public_hb = repair['accepted_HB']['public_summary']
    require(public_hb['commit'] == HB_PUBLIC_COMMIT and
            repair['accepted_HB']['source_commit'] == HB_SOURCE and
            repair['accepted_HB']['compiler_job'] == HB_JOB, 'original HB F identity differs')
    check_bytes(git_file(HB_PUBLIC_COMMIT, public_hb['path']), public_hb)
    check_bytes(git_file(commit, public_hb['path']), public_hb)
    metadata = json.loads(git_file(SOURCE_ANCHOR, repair['actual_bounded_metadata']['path']))
    probe = json.loads(git_file(SOURCE_ANCHOR, repair['actual_probe_result']['path']))
    require(metadata['schema'] == 'p15_licensed_K_failure_exact_metadata_v1' and
            metadata['source_commit'] == FAILED and metadata['job'] == FAILED_JOB and
            metadata['driver'] == {'bytes': 59950, 'sha256': OLD_DRIVER_SHA} and
            metadata['source_manifest'] == {'bytes': 333254,
                'sha256': 'f683cfc328b7323d4e1840e10dc1eca0b24c4b55b644756ef2e5d910152a27e5'} and
            metadata['failed_evidence'] == repair['failed_evidence'] and
            metadata['scope_source_preimages'] == {r['module']: r['before'] for r in repair['repairs']} and
            metadata['artifacts'] == repair['failed_owner_artifacts'] and
            metadata['artifacts'][SETUP] == SETUP_FP and
            metadata['accepted_owner_artifacts'][CUTOFF] == repair['accepted_Cutoff']['all_observed_target_artifacts'] and
            metadata['accepted_owner_artifacts'][ACCEPTED] == repair['accepted_HB']['all_observed_target_artifacts'] and
            metadata['normal_pass_present'] is False and metadata['normal_exit_code'] == 1 and
            metadata['live_sources_observed'] == 3 and metadata['artifact_entries_observed'] == 63 and
            metadata['full_live157_or_watch160_inventory_observed'] is False and
            metadata['source_runtime_receipts_unchanged_across_collection'] is True and
            metadata['accepted_owner_bindings'] == repair['bounded_accepted_owner_bindings'] and
            metadata['Lean_commands_executed'] == 0 and metadata['new_acceptance'] is False,
            'real bounded failure observation differs')
    require(probe['schema'] == 'p15_Licensed_actual_whole_module_scope_probe_v1' and
            probe['source_base_commit'] == FAILED and probe['exit_code'] == 0 and
            {k: probe['probe_source'][k] for k in ('bytes', 'sha256')} == repair['repairs'][0]['after'] and
            probe['whole_original_Licensed_module_submitted'] is True and
            probe['only_original_ContDiff_scope_enabled'] is True and
            probe['Lean_typecheck_commands'] == 1 and probe['original_serializer_and_guard_used'] is True and
            probe['output_object_requested'] is False and probe['existing_project_modules_rebuilt'] == [] and
            probe['imports'] == ['ImbalancedChen.P5OriginalPrimeChartHBWitnesses', 'Mathlib'] and
            probe['lake_no_build_env_lean'] is True and
            probe['three_sources_and_sixty_three_artifacts_unchanged'] is True and
            probe['accepted_Cutoff_K_and_HB_F_original_identity_preserved'] is True and
            probe['runtime_configuration_and_Git_state_unchanged'] is True and
            probe['other_two_scope_candidates_probed'] is False and
            probe['normal_or_kernel_acceptance_claimed'] is False,
            'whole Licensed probe binding differs')
    code = git_file(FAILED, OLD_DRIVER)
    require(sha(code) == OLD_DRIVER_SHA, 'original K driver differs')
    file = OLD_ROOT / FAILED / 'runs/attempt-00001/executed-driver.py'
    require(file.is_file() and not file.is_symlink() and file.resolve() == file and
            file.read_bytes() == code, 'original K failed executed driver differs')
    driver = ModuleType('original_K_licensed_scope_repair_reader')
    driver.__file__ = str(file)
    exec(compile(code, str(file), 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, OLD_ROOT),
            'original K environment differs')
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
                    'invalid exact scope interval')
            removed, added = splice['old_utf8'].encode(), splice['new_utf8'].encode()
            require(old[lo:hi] == removed and removed != added, 'scope splice differs')
            pieces.extend((old[cursor:lo], added))
            cursor = hi
        pieces.append(old[cursor:])
        require(row['exact_byte_splices'] and b''.join(pieces) == new and old != new,
                'postimage is not the exact published scope repair')
        before[module], after[module] = old, new
    require(list(before) == PUBLISHED_REPAIRS and sha(before[TARGET]) == BEFORE_SHA and
            sha(after[TARGET]) == AFTER_SHA, 'scope payload coverage differs')
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
        require(path.is_relative_to(OLD_ROOT / FAILED), 'failure evidence is outside original K')
        data[str(path)] = driver.retained_read(s, spec, path,
                                             {k: row[k] for k in ('bytes', 'sha256')})
    require(len(data) == 18, 'fixed failed evidence coverage differs')
    run = OLD_ROOT / FAILED / 'runs/attempt-00001'
    folder = OLD_ROOT / FAILED / TARGET / 'normal' / TARGET / 'attempt-00000'
    result = json.loads(data[str(run / 'RESULT.json')])
    worker = json.loads(data[str(run / 'WORKER_RESULT.json')])
    for record in (result, worker):
        require(record['source_commit'] == FAILED and record['targets'] == spec.order and
                record['accepted_owners'] == [] and
                set(record['failures']) == {TARGET} and record['acceptance_bindings'] == {} and
                not any(k in record for k in ('context_error', 'final_context_error', 'git_error')),
                'original K single-owner failure scope differs')
    require(result['worker_exit_code'] == 1 and result['all_selected_owners_accepted'] is False and
            result.get('dispatch_error') == 'serialized worker exited 1' and 'dispatch_error' not in worker and
            result['failures'] == worker['failures'] and
            result['acceptance_bindings'] == worker['acceptance_bindings'], 'original K group result differs')
    for stem in ('CONTEXT', 'GIT'):
        require(data[str(run / (stem + '_BEFORE.json'))] == data[str(run / (stem + '_AFTER.json'))],
                'original K failure did not preserve its context')
    require(data[str(run / 'executed-driver.py')] == git_file(FAILED, OLD_DRIVER),
            'failed executed driver differs')
    ready = result['direct_import_readiness'][TARGET]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'original K import readiness differs')
    command = json.loads(data[str(folder / 'normal-command.json')])
    log = folder / 'normal.log'
    require(command['argv'] == s.h.guard(0, ['lake', 'build', '+' + TARGET + ':olean']) and
            command['cwd'] == str(PROJECT) and command['exit_code'] == 1 and
            command['actual_built_modules'] == [] and command['actual_failed_modules'] == [TARGET] and
            command['log'] == str(log) and command['log_bytes'] == len(data[str(log)]) and
            command['log_sha256'] == sha(data[str(log)]), 'original K normal identity differs')
    context = json.loads(data[str(folder / 'CONTEXT_BEFORE.json')])
    own = s.h.closure(spec.graph, [TARGET])
    objects = {'.lake/build/lib/lean/' + m.replace('.', '/') + ext:
               artifacts[m]['.lake/build/lib/lean/' + m.replace('.', '/') + ext]
               for m in own - {TARGET} for ext in ('.olean', '.trace')}
    require(len(own) == 68 and all(value is not None for value in objects.values()) and
            context == {'source_commit': FAILED,
                        'project_sources': {m: spec.sources[m] for m in sorted(own)},
                        'dependency_objects_and_traces': objects,
                        'configuration': spec.review['runtime_configuration_bindings'],
                        'existing_runtime': spec.review['existing_runtime_bindings']},
            'original K normal context or live dependency bytes differ')
    require(not os.path.lexists(folder.parent / 'NORMAL_PASS.json'),
            'failed Licensed now has a normal receipt; inspect before repair')
    return result

def archive_binding(driver, s, commit, receipt):
    run = receipt.parent
    require(run.parent == ROOT / commit / 'runs' and
            re.fullmatch('attempt-[0-9]{5}', run.name) and receipt.resolve() == receipt,
            'unexpected previous setup archive receipt')
    record = s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / 'P5LicensedOriginalIntegerProfile.setup.json'
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
    archive = run / 'failed-artifacts' / 'P5LicensedOriginalIntegerProfile.setup.json'
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

def original_K_readonly_context(driver, s, commit):
    """Only K's read-only prefix, with Licensed freshness deferred to the real full preflight."""
    manifest, graph, sources, observed, inputs = driver.source_manifest(s, FAILED, FAILED_TARGETS)
    active = s.h.closure(graph, FAILED_TARGETS)
    previous = {SUPPORT, ACCEPTED}
    active_targets = (active & set(driver.TARGETS)) - previous
    require(len(graph) == 360 and len(active) == 157 and len(active_targets) == 16 and
            active_targets == set(FAILED_TARGETS) | {CUTOFF} and
            active.intersection(manifest['previously_accepted_targets']) == previous and
            not active.intersection(manifest['unaccepted_p3_dependencies']) and
            len(active | set(driver.TARGETS)) == 160,
            'original K fifteen-target graph differs')
    review_raw = driver.pinned(FAILED, driver.REVIEW, driver.REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        check_bytes(git_file(FAILED, path), expected)
        check_bytes(git_file(commit, path), expected)
    actual_graph, actual = s.h.project_graph(PROJECT, FAILED_TARGETS)
    require(actual_graph == {m: graph[m] for m in active} and
            {m: row['sha256'] for m, row in actual.items()} == {m: sources[m] for m in active},
            'original K installed fifteen-target source graph differs')
    executed = git_file(FAILED, OLD_DRIVER)
    spec = SimpleNamespace(manifest=manifest, graph=graph, sources=sources, observed=observed,
        review=review, active=active, selected=set(FAILED_TARGETS),
        order=s.d.compile_order([], FAILED_TARGETS, graph),
        input_bindings={**inputs,
            'runtime_review': {'path': driver.REVIEW, 'bytes': len(review_raw), 'sha256': s.api.sha(review_raw)},
            'runner': {'path': OLD_DRIVER, 'bytes': len(executed), 'sha256': s.api.sha(executed)}},
        retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    driver.environment(s, review)
    driver.retained_previous_target(s, spec, SUPPORT)
    driver.retained_hb_f_target(s, spec, ACCEPTED)
    suppliers = sorted(active & set(manifest['accepted_suppliers']))
    fixed = sorted(active & set(manifest['fixed_dependencies']))
    require(len(suppliers) == 13 and len(fixed) == 126, 'original K dependency partition differs')
    for module in suppliers:
        driver.retained_owner(s, spec, module, validate_live=True)
        spec.dependency_pins[module] = driver.module_artifacts(s, module)
    for module in fixed:
        spec.dependency_pins[module] = driver.fixed_dependency_pins(s, spec, module)
    # Licensed is NOT assigned a fabricated freshness or acceptance state.
    spec.initial_owners = {}
    for module in sorted(active_targets - {TARGET}):
        state = driver.existing_owner(s, FAILED, spec, module)
        spec.initial_owners[module] = state
        if module == CUTOFF:
            driver.require_completed_existing_owner(s, FAILED, spec, module, state)
            spec.dependency_pins[module] = driver.module_artifacts(s, module)
        else:
            require(state['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT',
                    'another selected owner is not the observed fresh state')
    require(set(spec.initial_owners) == active_targets - {TARGET} and
            len(spec.initial_owners) == 15 and
            set(spec.dependency_pins) == active - set(FAILED_TARGETS) and len(spec.dependency_pins) == 142 and
            spec.supplier_evidence[SUPPORT]['source_commit'] == SUPPORT_COMMIT and
            spec.supplier_evidence[ACCEPTED]['source_commit'] == HB_SOURCE,
            'original K preservation/current-owner inventory differs')
    views = {}
    for module, count in ((ACCEPTED, 67), (CUTOFF, 68)):
        own = s.h.closure(graph, [module])
        require(len(own) == count and not own.intersection(REPAIRED),
                'accepted closure count or repair disjointness differs')
        view = SimpleNamespace(**spec.__dict__)
        view.active, view.selected, view.order = own, set(), []
        view.sources, view.retained_inputs = dict(sources), dict(spec.retained_inputs)
        view.dependency_pins = {m: copy.deepcopy(spec.dependency_pins[m]) for m in own}
        view.baseline = driver.snapshot(s, view)
        views[module] = view
    return spec, views[ACCEPTED], views[CUTOFF]

def hb_evidence_files(driver, s):
    folders = [OLD_ROOT / HB_SOURCE / ACCEPTED,
               OLD_ROOT / HB_SOURCE / 'runs/attempt-00000' / ACCEPTED]
    result = {}
    for folder in folders:
        require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder,
                'accepted HB evidence root differs')
        count = 0
        for path in sorted(folder.rglob('*')):
            require(not path.is_symlink() and path.resolve() == path,
                    'accepted HB evidence contains a nonregular path')
            if path.is_dir():
                continue
            result[str(path)] = driver.regular_fingerprint(s, path)
            count += 1
        require(count > 0, 'accepted HB evidence root is empty')
    return result

def bind_hb_evidence(driver, s, spec, hb_spec, repair, artifacts):
    fixed = repair['accepted_HB']
    public = json.loads(git_file(HB_PUBLIC_COMMIT, fixed['public_summary']['path']))
    prior = spec.manifest['previously_accepted_targets'][ACCEPTED]
    require(fixed['public_summary'] == prior['historical_group']['public_evidence'],
            'HB public publication differs from the immutable I adapter')
    driver.require_hb_f_public_scope(prior, public)
    run = OLD_ROOT / HB_SOURCE / 'runs/attempt-00000'
    original = json.loads(driver.retained_read(s, spec, run / 'RESULT.json', public['original_result']))
    worker = json.loads(driver.retained_read(s, spec, run / 'WORKER_RESULT.json', public['original_worker_result']))
    driver.require_hb_f_run_scope(public, original, worker)
    require(public['schema'] == 'p15_hb_F_original_public_acceptance_v1' and
            public['source_commit'] == fixed['source_commit'] == HB_SOURCE and
            public['compiler_job'] == fixed['compiler_job'] == HB_JOB and
            set(public['owners']) == {ACCEPTED} and public['selected_owner_live_closure_count'] == 67 and
            public['normal_or_kernel_commands_executed'] == 0,
            'HB original F public acceptance differs')
    owner = public['owners'][ACCEPTED]
    require(owner['source_commit'] == HB_SOURCE and owner['source_sha256'] == spec.sources[ACCEPTED] and
            owner['receipt_bindings'] == fixed['receipt_bindings'], 'HB receipt identity differs')
    base = OLD_ROOT / HB_SOURCE / ACCEPTED
    audits = sorted((base / 'audits').iterdir())
    require(len(audits) == 1 and audits[0].is_dir() and not audits[0].is_symlink() and
            audits[0].name == owner['audit_id'], 'HB original unique audit differs')
    audit = audits[0]
    paths = {'normal': base / 'normal' / ACCEPTED / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json',
        'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    require(set(paths) == set(fixed['receipt_bindings']), 'HB six-receipt scope differs')
    for key, path in paths.items():
        driver.retained_read(s, spec, path, fixed['receipt_bindings'][key])
    validation = s.api.read_json(paths['audit_result'])
    require(validation['total_owned_exports'] == owner['owned_count'] == fixed['owned_count'] and
            validation['total_public_exports'] == owner['public_count'] == fixed['public_count'],
            'HB original audit counts differ')
    binding = original['acceptance_bindings'][ACCEPTED]
    require(driver.acceptance_binding(s, HB_SOURCE, ACCEPTED) == binding and
            artifacts[ACCEPTED] == spec.dependency_pins[ACCEPTED] ==
            binding['all_observed_target_artifacts'] == fixed['all_observed_target_artifacts'],
            'HB accepted source/receipt/full21 binding changed')
    files = hb_evidence_files(driver, s)
    require(all(files[str(path)] == fixed['receipt_bindings'][key] for key, path in paths.items()) and
            driver.snapshot(s, hb_spec) == hb_spec.baseline,
            'HB original evidence changed before preservation baseline')
    return files

def unchanged_hb(driver, s, state):
    return (driver.snapshot(s, state.hb_spec) == state.hb_baseline and
            hb_evidence_files(driver, s) == state.hb_files and
            driver.module_artifacts(s, ACCEPTED) == state.artifacts[ACCEPTED])

def cutoff_evidence_files(driver, s):
    folders = [OLD_ROOT / FAILED / CUTOFF,
               OLD_ROOT / FAILED / 'runs/attempt-00000' / CUTOFF]
    result = {}
    for folder in folders:
        require(folder.is_dir() and not folder.is_symlink() and folder.resolve() == folder,
                'accepted Cutoff K evidence root differs')
        count = 0
        for path in sorted(folder.rglob('*')):
            require(not path.is_symlink() and path.resolve() == path,
                    'accepted Cutoff K evidence contains a nonregular path')
            if path.is_dir():
                continue
            result[str(path)] = driver.regular_fingerprint(s, path)
            count += 1
        require(count > 0, 'accepted Cutoff K evidence root is empty')
    return result


def bind_cutoff_evidence(driver, s, spec, cutoff_spec, repair, artifacts):
    fixed = repair['accepted_Cutoff']
    public = json.loads(git_file(SOURCE_ANCHOR, repair['accepted_Cutoff_public']['path']))
    require(public['schema'] == 'p15_cutoff_K_original_public_acceptance_v1' and
            public['status'] == 'ORIGINAL_CUTOFF_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION' and
            public['source_commit'] == fixed['source_commit'] == FAILED and
            public['compiler_job'] == fixed['compiler_job'] == CUTOFF_JOB and
            public['selected_owners_revalidated'] == [CUTOFF] and
            set(public['owners']) == {CUTOFF} and public['selected_owner_live_closure_count'] == 68 and
            public['normal_or_kernel_commands_executed'] == 0,
            'Cutoff original K public acceptance differs')
    run = OLD_ROOT / FAILED / 'runs/attempt-00000'
    original = json.loads(driver.retained_read(s, spec, run / 'RESULT.json', public['original_result']))
    worker = json.loads(driver.retained_read(s, spec, run / 'WORKER_RESULT.json', public['original_worker_result']))
    for record in (original, worker):
        require(record['source_commit'] == FAILED and record['targets'] == [CUTOFF] and
                record['accepted_owners'] == [CUTOFF] and record['failures'] == {} and
                set(record['acceptance_bindings']) == {CUTOFF} and
                not any(key in record for key in ('dispatch_error', 'context_error', 'final_context_error', 'git_error')),
                'Cutoff original K successful group scope differs')
    require(original['worker_exit_code'] == 0 and original['all_selected_owners_accepted'] is True and
            original['acceptance_bindings'] == worker['acceptance_bindings'],
            'Cutoff K original worker success differs')
    for stem in ('CONTEXT', 'GIT'):
        pair = public['original_context_pairs'][stem]
        before = driver.retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before'])
        after = driver.retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after'])
        require(before == after, 'Cutoff K acceptance did not preserve its context')
    owner = public['owners'][CUTOFF]
    require(owner['source_commit'] == FAILED and owner['source_sha256'] == spec.sources[CUTOFF] and
            owner['receipt_bindings'] == fixed['receipt_bindings'] and
            owner['owned_count'] == fixed['owned_count'] == 16 and
            owner['public_count'] == fixed['public_count'] == 8 and
            owner['receipt_rebound_to_current_commit'] is False,
            'Cutoff K original owner identity differs')
    base = OLD_ROOT / FAILED / CUTOFF
    audits = sorted((base / 'audits').iterdir())
    require(len(audits) == 1 and audits[0].is_dir() and not audits[0].is_symlink() and
            audits[0].name == owner['audit_id'], 'Cutoff K original unique audit differs')
    audit = audits[0]
    paths = {'normal': base / 'normal' / CUTOFF / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json',
        'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    require(set(paths) == set(fixed['receipt_bindings']), 'Cutoff K six-receipt scope differs')
    for key, path in paths.items():
        driver.retained_read(s, spec, path, fixed['receipt_bindings'][key])
    validation = s.api.read_json(paths['audit_result'])
    require(validation['total_owned_exports'] == 16 and validation['total_public_exports'] == 8,
            'Cutoff K actual owned counts differ')
    binding = original['acceptance_bindings'][CUTOFF]
    require(driver.acceptance_binding(s, FAILED, CUTOFF) == binding and
            artifacts[CUTOFF] == spec.dependency_pins[CUTOFF] ==
            binding['all_observed_target_artifacts'] == fixed['all_observed_target_artifacts'],
            'Cutoff K original source/receipt/full21 binding differs')
    files = cutoff_evidence_files(driver, s)
    require(all(files[str(path)] == fixed['receipt_bindings'][key] for key, path in paths.items()) and
            driver.snapshot(s, cutoff_spec) == cutoff_spec.baseline,
            'Cutoff K original evidence changed before preservation baseline')
    return files


def unchanged_cutoff(driver, s, state):
    return (driver.snapshot(s, state.cutoff_spec) == state.cutoff_baseline and
            cutoff_evidence_files(driver, s) == state.cutoff_files and
            driver.module_artifacts(s, CUTOFF) == state.artifacts[CUTOFF])

def prepare(driver, s, commit, repair):
    before, after = payloads(commit, repair)
    require(all(after[m] == git_file(SOURCE_ANCHOR, m.replace('.', '/') + '.lean') for m in REPAIRED),
            'M source payload is not exactly the fixed L source')
    spec, hb_spec, cutoff_spec = original_K_readonly_context(driver, s, commit)
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(commit, row['path'])
        require(raw == git_file(SOURCE_ANCHOR, row['path']) and
                raw == (after[module] if module in after else git_file(FAILED, row['path'])) and
                s.h.imports(raw) == row['all_imports'], 'unrelated published source or import changed')
    support = original_support(commit)
    require(all(not set(REPAIRED).intersection(s.h.closure(spec.graph, [m]))
                for m in spec.manifest['accepted_suppliers']) and
            not set(REPAIRED).intersection(support.spec.active | hb_spec.active | cutoff_spec.active),
            'scope repair intersects an accepted source closure')
    watch = spec.active | support.spec.active | set(driver.TARGETS)
    require(len(spec.active) == 157 and support.spec.active <= spec.active and len(watch) == 160,
            'live157/watch160 preservation scope differs')
    artifacts = {m: driver.module_artifacts(s, m) for m in sorted(watch)}
    watched_sources = source_watch(driver, watch)
    require(all(watched_sources[m] == {'bytes': len(before[m]), 'sha256': sha(before[m])} for m in REPAIRED),
            'three live sources are not the inspected K preimages; no repeated mutation')
    require(len(artifacts[TARGET]) == 21 and SETUP in artifacts[TARGET] and
            all(value is None for path, value in artifacts[TARGET].items() if path != SETUP) and
            artifacts[TARGET][SETUP] in (None, SETUP_FP),
            'only the inspected Licensed failed setup is eligible')
    for module in set(FAILED_TARGETS) - {TARGET}:
        driver.require_fresh_owner(module, artifacts[module])
    prior = prior_archive(driver, s, spec, commit) if artifacts[TARGET][SETUP] is None else {}
    bind_failed_evidence(driver, s, spec, repair, artifacts)
    hb_files = bind_hb_evidence(driver, s, spec, hb_spec, repair, artifacts)
    cutoff_files = bind_cutoff_evidence(driver, s, spec, cutoff_spec, repair, artifacts)
    files = support_evidence_files(driver, s)
    require(artifacts[SUPPORT] == support.spec.initial_owners[SUPPORT]['artifacts'],
            'Support outputs changed after original B validation')
    public_pins = support.result['owners'][SUPPORT]['receipt_bindings']
    require(all(files.get(str(path)) == public_pins[key] for key, path in support.paths.items()),
            'Support B public receipts changed before preservation baseline')
    support_baseline = support.driver.snapshot(support.s, support.spec)
    return SimpleNamespace(spec=spec, before=before, after=after, watch=watch,
        artifacts=artifacts, watched_sources=watched_sources, baseline=driver.snapshot(s, spec),
        prior_archive=prior, hb_spec=hb_spec, hb_baseline=hb_spec.baseline, hb_files=hb_files,
        cutoff_spec=cutoff_spec, cutoff_baseline=cutoff_spec.baseline, cutoff_files=cutoff_files,
        support=support, support_baseline=support_baseline, support_files=files)

def unchanged_support(driver, s, state):
    return (state.support.driver.snapshot(state.support.s, state.support.spec) == state.support_baseline and
            support_evidence_files(driver, s) == state.support_files)

def apply_repair(driver, s, commit, repair, raw, run):
    s.d.verify_lane(s.h)
    state = prepare(driver, s, commit, repair)
    updates = [{'module': m, 'path': m.replace('.', '/') + '.lean',
                'before_sha256': sha(state.before[m]), 'after_sha256': sha(state.after[m]),
                'cloud_source_mutation_required': True} for m in REPAIRED]
    s.d.write_frozen(run / 'REPAIR_MANIFEST.json', raw)
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {
        'source_commit': commit, 'source_anchor_commit': SOURCE_ANCHOR, 'failed_source_commit': FAILED,
        'updates': updates, 'published_source_count': 360, 'K_selected_source_count': 157,
        'watch_module_count': 160, 'preserved_dependency_count': 142,
        'context_before': state.baseline, 'sources_before': state.watched_sources,
        'artifacts_before': state.artifacts, 'HB_F_preservation_context': state.hb_baseline,
        'HB_original_F_evidence_files': state.hb_files,
        'Cutoff_K_preservation_context': state.cutoff_baseline,
        'Cutoff_original_K_evidence_files': state.cutoff_files,
        'Support_original_B_context': state.support_baseline,
        'Support_original_B_evidence_files': state.support_files, 'new_lean_acceptance': False})
    require(driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            unchanged_hb(driver, s, state) and unchanged_cutoff(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == state.artifacts,
            'preserved state changed before exact scope repair')
    preservation = preserve_failed_setup(driver, s, commit, state, run)
    expected_artifacts = copy.deepcopy(state.artifacts)
    expected_artifacts[TARGET][SETUP] = None
    require({m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts and
            driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            unchanged_hb(driver, s, state) and unchanged_cutoff(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources,
            'setup archive changed another source, artifact, runtime or receipt')
    fresh = driver.preflight(s, FAILED, FAILED_TARGETS)
    require(fresh.active == state.spec.active and fresh.sources == state.spec.sources and
            fresh.dependency_pins == state.spec.dependency_pins and
            set(fresh.initial_owners) == set(FAILED_TARGETS) | {CUTOFF} and
            len(fresh.initial_owners) == 16 and
            all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in FAILED_TARGETS) and
            fresh.initial_owners[CUTOFF]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
            fresh.dependency_pins[CUTOFF] == state.artifacts[CUTOFF] and
            fresh.supplier_evidence[SUPPORT]['source_commit'] == SUPPORT_COMMIT and
            fresh.supplier_evidence[ACCEPTED]['source_commit'] == HB_SOURCE,
            'unchanged full K fifteen-target preflight or original accepted identities differ')
    require(driver.snapshot(s, state.spec) == state.baseline and unchanged_support(driver, s, state) and
            unchanged_hb(driver, s, state) and unchanged_cutoff(driver, s, state) and
            source_watch(driver, state.watch) == state.watched_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts,
            'read-only full K preflight changed a preserved binding')
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    records = s.h.install_sources(PROJECT, updates,
        {m.replace('.', '/') + '.lean': state.after[m] for m in REPAIRED}, run / 'backups')
    require([record['module'] for record in records] == REPAIRED and all(r['mutated'] for r in records),
            'exact three-source mutation differs')
    expected = copy.deepcopy(state.baseline)
    expected_sources = copy.deepcopy(state.watched_sources)
    for module in REPAIRED:
        backup = run / 'backups' / (module.replace('.', '/') + '.lean')
        require(backup.is_file() and not backup.is_symlink() and backup.read_bytes() == state.before[module],
                'exact source preimage backup differs')
        digest = sha(state.after[module])
        state.spec.sources[module] = digest
        expected['selected_live_sources'][module] = digest
        expected_sources[module] = {'bytes': len(state.after[module]), 'sha256': digest}
    require(driver.snapshot(s, state.spec) == expected and unchanged_support(driver, s, state) and
            unchanged_hb(driver, s, state) and unchanged_cutoff(driver, s, state) and
            source_watch(driver, state.watch) == expected_sources and
            {m: driver.module_artifacts(s, m) for m in sorted(state.watch)} == expected_artifacts and
            all(driver.regular_fingerprint(s, Path(path)) == value for path, value in preservation['bindings'].items()),
            'unrelated source, accepted evidence or artifact changed')
    actual_graph, actual = s.h.project_graph(PROJECT, FAILED_TARGETS)
    require(actual_graph == {m: state.spec.graph[m] for m in state.spec.active} and
            {m: row['sha256'] for m, row in actual.items()} ==
            {m: state.spec.sources[m] for m in state.spec.active}, 'post-repair full157 graph differs')
    result = {'status': 'EXACT_THREE_SCOPE_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'source_commit': commit, 'source_anchor_commit': SOURCE_ANCHOR,
        'failed_source_commit': FAILED, 'failed_job': FAILED_JOB, 'repair_records': records,
        'context_after': expected, 'sources_after': expected_sources,
        'failed_setup_preservation': preservation, 'original_K_suppliers_preserved': 13,
        'accepted_Cutoff_preserved_at_original_K': True, 'accepted_HB_preserved_at_original_F': True,
        'accepted_Support_preserved_at_original_B': True,
        'full_unchanged_K_fifteen_target_preflight_passed_after_setup_archive': True,
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
        print(json.dumps({'status': 'EXACT_THREE_SCOPE_PREFLIGHT_ONLY', 'source_commit': commit,
            'current_source_sha256': BEFORE_SHA, 'postimage_sha256': AFTER_SHA,
            'published_sources': 360, 'K_selected_sources': 157, 'watched_modules': 160,
            'accepted_Cutoff_preserved_at_K': True,
            'accepted_HB_preserved_at_F': True, 'accepted_Support_preserved_at_B': True,
            'planned_live_source_repairs': REPAIRED,
            'planned_exact_setup_archive': state.artifacts[TARGET][SETUP] is not None,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    base = ROOT / commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'unexpected three-scope repair worker path')
        try:
            mutated = apply_repair(driver, s, commit, repair, raw, run)
        except Exception as error:
            s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'source_commit': commit,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            print(json.dumps({'status': 'EXACT_THREE_SCOPE_HELD',
                              'error_type': type(error).__name__}), flush=True)
            return 1
        print(json.dumps({'status': 'EXACT_THREE_SCOPE_SOURCE_REPAIR_VERIFIED',
            'source_commit': commit, 'mutated_modules': mutated,
            'accepted_Cutoff_preserved_at_K': True,
            'accepted_HB_preserved_at_F': True, 'accepted_Support_preserved_at_B': True,
            'new_lean_acceptance': False}), flush=True)
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
        require(command['exit_code'] == 0, 'serialized exact three-scope repair held; inspect failure evidence')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty Git state changed')
    return 0

if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    try:
        raise SystemExit(main())
    except Exception as error:
        # The detailed original-reader exception remains private evidence only.
        print(json.dumps({'status': 'EXACT_THREE_SCOPE_HELD',
                          'error_type': type(error).__name__, 'new_lean_acceptance': False}), flush=True)
        raise SystemExit(3)
