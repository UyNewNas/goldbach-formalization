#!/usr/bin/env python3
"""Install only the R Family repair after durable archival and unchanged Q preflight.

S is the publication of this updater. Q owns both accepted owners and the failed
Family attempt; R owns the six-splice payload and public evidence. This wrapper
never compiles, audits, edits the Q reader, or rebinds an acceptance receipt.
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
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
R = '0935516b9bd978a61248c81b59776d1eb47f6044'
Q_ANCHOR = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
FAILED_JOB = 'job_7b6961dd4ada4d1e82ed170a66eee311'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-family-api-repair-v1')
SCRIPT = 'docs/p1/20261126/p15-family-api-repair/apply_family_repair.py'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 101219, 'sha256': 'c168664e6350f79a77c7b07d22db09167ac9a3906b18a251c4c308b773cfbce5'}
MANIFEST_FP = {'bytes': 342103, 'sha256': 'b37216a0928fbd7ebb0c14ff4cb51dfbfda568cd1d606db61966417dbb5077a6'}
ALLK = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
ADMISSIBLE = 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily'
ACCEPTED = [ALLK, ADMISSIBLE]
TARGET = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
SOURCE = 'ImbalancedChen/Part3AllKFamilyLambdaCorrectionBound.lean'
SETUP = '.lake/build/ir/ImbalancedChen/Part3AllKFamilyLambdaCorrectionBound.setup.json'
ARCHIVE_NAME = 'Part3AllKFamilyLambdaCorrectionBound.setup.json'
BEFORE = {'bytes': 19242, 'sha256': '5f78dd9a9bdb228388e4b219845ab0d6a0385513695fff58dd27596f8fe703b6'}
AFTER = {'bytes': 19563, 'sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109'}
SETUP_FP = {'bytes': 6329450, 'sha256': 'e060890186321528c208f648e9cf39c37359677dafba97fdbd79ab0424e100ef'}
PREFIX = 'docs/p1/20261126/p15-family-first-compile-repair/'
REPAIR, PROBE = PREFIX + 'REPAIR_CANDIDATE.json', PREFIX + 'ACTUAL_FAMILY_PROBE_RESULT.json'
DIAGNOSTICS, READ = PREFIX + 'ACTUAL_Q_FAILURE_METADATA.json', PREFIX + 'ACTUAL_Q_ACCEPTANCE_READ.json'
PUBLIC = {m: 'docs/p1/20261125/p15-current-public-acceptance/' + name + '_Q_PUBLIC_ACCEPTANCE.json'
          for m, name in ((ALLK, 'ALLK'), (ADMISSIBLE, 'ADMISSIBLE'))}
PINS = {
    REPAIR: {'bytes': 3615, 'sha256': '96bfd67335da54f363fcf00f3644ae9b683742255fd22d34d3581b233beba103'},
    PROBE: {'bytes': 2242, 'sha256': 'e1552fd9eca1e3ecda29c78a9c31ebec447f74bca9a6f3202c77b384d2bd5d6e'},
    DIAGNOSTICS: {'bytes': 9922, 'sha256': 'c5bc537e0a2230620f4c66552f725dd3974b4fdef85aee3645513c9322083ae6'},
    READ: {'bytes': 24872, 'sha256': '27556454d6448b25dace6cdd75e706552fefaae10b4daf0bf029853fc4a95263'},
    PUBLIC[ALLK]: {'bytes': 7331, 'sha256': 'e11f554ef351aa5ad4d2dfc6f6e11e8c1021af8078576424bd06f1e26a81851e'},
    PUBLIC[ADMISSIBLE]: {'bytes': 9425, 'sha256': '5b2fa610c5b691d9fe6b1acee5424f32128eda66d52509c5aeeca37109dc45cf'},
}
REMAINING = [TARGET, 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy', 'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment', 'ImbalancedChen.P5PrimeDivisorMeanCorrection',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis', 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode())


def pin(value):
    return {key: value[key] for key in ('bytes', 'sha256')}


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def file_fp(c, path):
    path = Path(path)
    return c.driver.regular_fingerprint(c.s, path) if os.path.lexists(path) else None


def tree_inventory(c):
    base = OLD_ROOT / Q
    need(base.is_dir() and base.resolve() == base, 'original Q evidence root differs')
    result = {}
    for path in sorted(base.rglob('*')):
        need(not path.is_symlink(), 'symlink in original Q evidence')
        result[str(path.relative_to(base))] = 'directory' if path.is_dir() else file_fp(c, path)
    return result


def source_inventory(c, modules):
    return {m: file_fp(c, PROJECT / c.s.h.module_path(m)) for m in sorted(modules)}


def artifact_inventory(c, modules):
    return {m: c.driver.module_artifacts(c.s, m) for m in sorted(modules)}


def normal_path(module):
    return OLD_ROOT / Q / module / 'normal' / module / 'NORMAL_PASS.json'


def require_preimage(c):
    path = PROJECT / SOURCE
    need(path.resolve() == path and file_fp(c, path) == BEFORE and path.read_bytes() == c.before,
         'Family source is not the exact Q preimage; source_after is held')


def load(commit):
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', commit), 'full S commit and unoptimized Python required')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
         subprocess.run(['git', 'merge-base', '--is-ancestor', R, commit], cwd=REPO).returncode == 0,
         'execution S must descend from repair R')
    script = Path(__file__)
    need(script.is_file() and not script.is_symlink(), 'updater is not a regular file')
    executed = script.read_bytes()
    need(executed == git_file(commit, SCRIPT), 'executed updater differs from S publication')
    docs = {}
    for path, expected in PINS.items():
        raw = git_file(R, path)
        need(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published R/S input differs: ' + path)
        docs[path] = json.loads(raw)
    before, after = git_file(Q, SOURCE), git_file(R, SOURCE)
    need(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
         'canonical Q/R/S Family source differs')
    repair = docs[REPAIR]
    need(repair['schema'] == 'p15_Family_exact_six_proof_splice_repair_v1' and
         repair['failed_source_commit'] == Q and repair['failed_job'] == FAILED_JOB and
         repair['module'] == TARGET and repair['canonical_path'] == SOURCE and
         repair['before'] == BEFORE and repair['after'] == AFTER and
         repair['failed_setup'] == {'path': SETUP, **SETUP_FP} and len(repair['splices']) == 6 and
         repair['new_Family_owner_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'published six-splice Family repair differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['original_byte_start'], splice['original_byte_end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before_utf8'].encode(),
             'original splice offset/bytes differ')
        pieces.extend((before[end:start], splice['after_utf8'].encode()))
        end = stop
    need(b''.join(pieces) + before[end:] == after, 'Family payload changes bytes outside six splices')
    raw = git_file(Q, DRIVER)
    entry = OLD_ROOT / Q / 'runs/attempt-00000/executed-driver.py'
    need(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw and
         raw_fp(git_file(Q, MANIFEST)) == MANIFEST_FP, 'original Q reader/manifest differs')
    driver = ModuleType('unchanged_Q_family_repair_reader')
    driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, OLD_ROOT, DRIVER, Q_ANCHOR), 'original Q reader environment differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(executed)},
        'repair_source_commit': R, 'failed_source_commit': Q, 'failed_job': FAILED_JOB,
        'module': TARGET, 'source_path': SOURCE, 'source_before': BEFORE, 'source_after': AFTER,
        'failed_setup': {'path': SETUP, **SETUP_FP}, 'published_R_inputs': PINS}
    return SimpleNamespace(commit=commit, driver=driver, s=driver.helpers(), docs=docs,
                           before=before, after=after, script=executed, identity=identity)


def read_originals(c, spec):
    s, driver = c.s, c.driver
    results, contexts, accepted = [], [], {}
    read = c.docs[READ]
    need(read['source_commit'] == Q and read['selected_owners_revalidated'] == ACCEPTED and
         read['normal_or_kernel_commands_executed'] == 0 and
         value_fp(spec.baseline) == read['current_read_snapshot'], 'R original accepted-prefix read differs')
    for index, module in enumerate(ACCEPTED):
        public = c.docs[PUBLIC[module]]
        need(public == read['public_summaries'][('ALLK' if index == 0 else 'ADMISSIBLE') + '_Q_PUBLIC_ACCEPTANCE'] and
             public['source_commit'] == Q and set(public['owners']) == {module} and
             public['original_run'] == 'runs/attempt-%05d' % index, 'Q owner public origin differs')
        run = OLD_ROOT / Q / public['original_run']
        need(file_fp(c, run / 'executed-driver.py') == DRIVER_FP and
             file_fp(c, run / 'RESULT.json') == public['original_result'] and
             file_fp(c, run / 'WORKER_RESULT.json') == public['original_worker_result'], 'Q run pins differ')
        result, worker = [s.api.read_json(run / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        need(all(result.get(key) == value for key, value in worker.items()) and result['source_commit'] == Q and
             result['accepted_owners'] == public['original_group_accepted_owners'] and
             result['targets'] == public['original_targets'], 'Q original RESULT/WORKER identity differs')
        for stem, pair in public['original_context_pairs'].items():
            need(stem in ('CONTEXT', 'GIT') and pair['before'] == pair['after'] and
                 all(file_fp(c, run / (stem + '_' + side.upper() + '.json')) == pair[side]
                     for side in ('before', 'after')), 'original Q context pair differs')
        driver.require_completed_existing_owner(s, Q, spec, module, spec.initial_owners[module])
        binding = driver.acceptance_binding(s, Q, module)
        need(binding == result['acceptance_bindings'][module], 'current Q acceptance differs from its original run')
        owner = public['owners'][module]
        paths = {key: Path(path) for key, path in owner['receipt_paths'].items()}
        need(set(paths) == {'normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence'} and
             {key: file_fp(c, path) for key, path in paths.items()} == owner['receipt_bindings'] and
             binding['normal_receipt'] == {'path': str(paths['normal']), **owner['receipt_bindings']['normal']} and
             binding['audits'] == [{'plan': {'path': str(paths['audit_plan']), **owner['receipt_bindings']['audit_plan']},
                                   'result': {'path': str(paths['audit_result']), **owner['receipt_bindings']['audit_result']}}],
             'original Q six-receipt acceptance binding differs')
        counted = s.api.read_json(paths['audit_result'])
        need((counted['total_owned_exports'], counted['total_public_exports']) ==
             (owner['owned_count'], owner['public_count']) == ((34, 31) if index == 0 else (42, 42)) and
             owner['source_commit'] == Q and owner['source_sha256'] == spec.sources[module], 'Q owner count/source differs')
        results.append(result)
        contexts.append(s.api.read_json(run / 'CONTEXT_BEFORE.json'))
        accepted[module] = binding
    first, later = results
    need(first['targets'] == first['accepted_owners'] == [ALLK] and first['worker_exit_code'] == 0 and
         first['all_selected_owners_accepted'] is True and later['targets'] == ACCEPTED + REMAINING and
         later['accepted_owners'] == ACCEPTED and later['reused_complete_selected_owners'] == [ALLK] and
         set(later['failures']) == {TARGET} and later['worker_exit_code'] == 1 and
         later['all_selected_owners_accepted'] is False and 'final_stock_readiness' not in later and
         accepted[ALLK] == later['acceptance_bindings'][ALLK], 'Q single success/partial thirteen-target scope differs')
    return later, contexts[1], accepted


def archive_binding(c, receipt):
    run = receipt.parent
    need(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
         receipt.resolve() == receipt, 'archive receipt is outside this Family/S repair')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    need(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
         record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
         record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
         record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
         record['new_lean_acceptance'] is False and archive.resolve() == archive and
         file_fp(c, archive) == SETUP_FP, 'archive is not the exact Q/R/S/script-bound Family setup')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}


def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    need(receipts, 'missing active setup without this Family/S archive receipt')
    result = {}
    for receipt in receipts:
        result.update(archive_binding(c, receipt))
    return result


def prepare(c):
    driver, s = c.driver, c.s
    git, evidence = s.d.original_git_state(REPO), tree_inventory(c)
    need(value_fp(evidence) == pin(c.docs[READ]['complete_original_Q_evidence_inventory']),
         'original Q evidence tree differs from the actual R acceptance read')
    spec = driver.preflight(s, Q, ACCEPTED)
    need(len(spec.active) == 74 and len(spec.dependency_pins) == 72 and
         set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'Q accepted-prefix scope differs')
    later, original_context, accepted = read_originals(c, spec)
    active = s.h.closure(spec.graph, REMAINING)
    watch = active | set(driver.TARGETS)
    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,
         'remaining11 source/watch scope differs')
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(R, row['path'])
        need(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and
             git_file(c.commit, row['path']) == raw and s.h.imports(raw) == row['all_imports'],
             'unrelated R/S published source or imports changed: ' + module)
    sources, artifacts = source_inventory(c, spec.graph), artifact_inventory(c, watch)
    require_preimage(c)
    graph, installed = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: spec.graph[m] for m in active} and
         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live Q graph differs')
    need(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
         all(value is None for path, value in artifacts[TARGET].items() if path != SETUP), 'Family artifacts are not setup only')
    for module in REMAINING:
        need(not os.path.lexists(normal_path(module)), 'remaining owner already has a Q normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    need(original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING) and
         all(artifacts[m] == fp for m, fp in original_context['preserved_dependency_artifacts'].items()) and
         all(original_context[k] == value for k, value in driver.environment(s, spec.review).items()),
         'original Q source/dependency/runtime context differs')
    metadata = c.docs[DIAGNOSTICS]
    need(metadata['source_commit'] == Q and metadata['compiler_job'] == FAILED_JOB, 'failure metadata identity differs')
    observed = [row[key] for row in metadata['records']
                for key in ('metadata', 'observed_file', 'original_run_record', 'admissible_audit') if key in row]
    need(len(observed) == 17, 'failure metadata inventory differs')
    for row in observed:
        path = Path(row['path'])
        need(path in (PROJECT / SOURCE, PROJECT / SETUP) or path.is_relative_to(OLD_ROOT / Q), 'failure metadata path differs')
        need(pin(row) == SETUP_FP if path == PROJECT / SETUP else file_fp(c, path) == pin(row), 'actual Q failure evidence differs')
    probe = c.docs[PROBE]
    need(probe['source_base_commit'] == Q and probe['exit_code'] == 0 and pin(probe['candidate']) == AFTER and
         probe['original_source'] == BEFORE and probe['whole_original_module_submitted'] is True and
         probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
         probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False,
         'Family whole-module no-output probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    retained = {**original_context['retained_original_evidence'], **archives,
        str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_FAMILY_PROBE_RESULT.json'): PINS[PROBE]}
    need(log.read_bytes() == probe['compiler_output'].encode() and
         all(file_fp(c, path) == expected for path, expected in retained.items()), 'retained original/probe evidence differs')
    state = SimpleNamespace(spec=spec, later=later, context=original_context, accepted=accepted,
        active=active, watch=watch, sources=sources, artifacts=artifacts, evidence=evidence,
        retained=retained, archives=archives, git=git)
    unchanged(c, state)
    return state


def unchanged(c, state, *, archived=False, installed=False):
    sources, artifacts = copy.deepcopy(state.sources), copy.deepcopy(state.artifacts)
    if installed:
        sources[TARGET] = AFTER
    if archived:
        artifacts[TARGET][SETUP] = None
    need(source_inventory(c, state.spec.graph) == sources and artifact_inventory(c, state.watch) == artifacts,
         'source360/artifact160 preservation differs')
    need(tree_inventory(c) == state.evidence and
         all(file_fp(c, path) == fp for path, fp in state.retained.items()), 'original Q/retained evidence changed')
    need(c.driver.snapshot(c.s, state.spec) == state.spec.baseline and
         {m: c.driver.acceptance_binding(c.s, Q, m) for m in ACCEPTED} == state.accepted and
         c.s.d.original_git_state(REPO) == state.git and
         all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'accepted Q context/runtime/Git changed')


def fsync_directory(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def archive_setup(c, state, run):
    if state.artifacts[TARGET][SETUP] is None:
        need(state.archives == prior_archive(c), 'resume archive changed')
        return {'action': 'ALREADY_ARCHIVED_AND_ABSENT', 'bindings': state.archives}
    path = PROJECT / SETUP
    need(path.resolve() == path and path.is_file() and not path.is_symlink(), 'Family setup is not the fixed regular path')
    original, raw = path.stat(), path.read_bytes()
    need(raw_fp(raw) == SETUP_FP, 'failed Family setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    need(archive.parent.resolve() == archive.parent, 'archive parent traverses a symlink')
    fd = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    need(file_fp(c, archive) == SETUP_FP, 'exclusive Family archive differs')
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
    need(not path.is_symlink() and path.resolve() == path and path.read_bytes() == raw and
         (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns) ==
         (original.st_dev, original.st_ino, original.st_size, original.st_mtime_ns), 'setup changed before authorized unlink')
    path.unlink()
    fsync_directory(path.parent)
    need(not os.path.lexists(path), 'Family setup remains active')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}


def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'source_slots': state.sources, 'artifact_slots': state.artifacts, 'original_Q_evidence': state.evidence,
        'retained_inputs': state.retained, 'accepted_Q_bindings': state.accepted,
        'accepted_prefix_context': state.spec.baseline, 'original_Q_context': state.context,
        'Git_before': state.git, 'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = archive_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, archived=True)
    # Actual Q preflight runs with the unchanged Family preimage, before install.
    fresh = driver.preflight(s, Q, REMAINING)
    need(fresh.active == state.active and fresh.graph == state.spec.graph and fresh.sources == state.spec.sources and
         fresh.order == REMAINING and len(fresh.dependency_pins) == 146 and
         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
             fresh.dependency_pins[m] == state.artifacts[m] for m in ACCEPTED) and
         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and
         len(fresh.supplier_evidence) == 18, 'unchanged Q eleven-target preflight differs')
    unchanged(c, state, archived=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_Q_PREFLIGHT.json', {'source_commit': Q, 'targets': fresh.order,
        'active_source_count': 157, 'preserved_dependency_count': 146,
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require_preimage(c)
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    backup = run / 'backups' / SOURCE
    need(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True and
         file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
         (PROJECT / SOURCE).read_bytes() == c.after, 'exact single Family installation/backup differs')
    post = copy.copy(fresh)
    post.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline)
    expected['selected_live_sources'][TARGET] = AFTER['sha256']
    need(driver.snapshot(s, post) == expected, 'post-install dependency/runtime context differs')
    unchanged(c, state, archived=True, installed=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: fresh.graph[m] for m in fresh.active} and
         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', {'status': 'EXACT_SINGLE_FAMILY_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'identity': c.identity, 'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_Q_eleven_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,
        'active_source_count': 157, 'preserved_dependency_count': 146,
        'AllK_Admissible_original_Q_acceptances_preserved': True,
        'original_Q_evidence_other_artifacts_runtime_and_Git_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True, help='updater publication S')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.check:
        need(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_FAMILY_PREFLIGHT_ONLY', 'identity': c.identity,
            'accepted_Q_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 74, 'accepted_prefix_dependencies': 72,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_Q_eleven_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        need(run.is_absolute() and run.resolve() == run and run.parent == runs and
             re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected Family worker path')
        try:
            apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_FAMILY_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
                     mutated_modules=[TARGET], new_lean_acceptance=False, path=str(run / 'SOURCE_REPAIR_RESULT.json'))
        return 0
    need(runs.resolve() == runs, 'evidence parent traverses a symlink')
    run = c.s.d.attempt(runs)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-repair.py'
    c.s.d.write_frozen(executed, c.script)
    try:
        command = c.s.ops.run(run, 'serialized-source-repair', c.s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--apply', '--inside-lane', str(run)]), relay=True)
        need(command['exit_code'] == 0 and command['actual_built_modules'] == [] and command['actual_failed_modules'] == [],
             'serialized Family repair held; inspect private failure evidence')
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(run / 'GIT_AFTER.json', after)
        need(after == before, 'original dirty Git state changed')
    return 0


if __name__ == '__main__':
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'EXACT_SINGLE_FAMILY_HELD', 'error_type': type(error).__name__,
                          'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
