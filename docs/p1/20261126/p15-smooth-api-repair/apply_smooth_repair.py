#!/usr/bin/env python3
"""Install one proof-only SmoothLicence repair under the original U acceptance gates.

Word and AllGroup keep their original U runs. Family stays S; AllK/Admissible stay Q.
An exact failed setup is durably archived before removal. No Lean command is run.
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
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
U_ANCHOR = '999510c460e6e026c8cabe46c5f35876f7201f8e'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-smooth-api-repair-v1')
SCRIPT = 'docs/p1/20261126/p15-smooth-api-repair/apply_smooth_repair.py'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 152370, 'sha256': '9d9c2e467b3fd6271b7b0101812094ca6ff768f1ea831812b6de4c95a0dd9c7a'}
MANIFEST_FP = {'bytes': 349643, 'sha256': 'ae3f6bb915e0ed2dc799fd6bfed2b906aab3efac3df9186c9c1d54da4b53a1af'}
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
ALLGROUP = 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'
ACCEPTED = [WORD, ALLGROUP]
TARGET = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
SOURCE = 'ImbalancedChen/P1OriginalSingletonSmoothLicence.lean'
SETUP = '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.setup.json'
ARCHIVE_NAME = 'P1OriginalSingletonSmoothLicence.setup.json'
BEFORE = {'bytes': 4358, 'sha256': 'f74c3c51c0b1de7b493f9fe7e883d89a4b5c163624bb5be1f6901fbec3424011'}
SETUP_FP = {'bytes': 6423922, 'sha256': '963197a94a0370d47ee383bb103770b7af29e692df06b8195d72906e1cc0fff7'}
PREFIX = 'docs/p1/20261126/p15-smooth-first-compile-repair/'
REPAIR, PROBE = PREFIX + 'REPAIR_CANDIDATE.json', PREFIX + 'ACTUAL_SMOOTH_PROBE_RESULT.json'
DIAGNOSTICS, READ = PREFIX + 'ACTUAL_U_METADATA.json', PREFIX + 'ACTUAL_U_ACCEPTANCE_READ.json'
COLLECTOR = PREFIX + 'collect_u_acceptance.py'
PUBLIC_WORD = 'docs/p1/20261125/p15-current-public-acceptance/WORD_U_PUBLIC_ACCEPTANCE.json'
PUBLIC_ALLGROUP = 'docs/p1/20261125/p15-current-public-acceptance/ALLGROUP_U_PUBLIC_ACCEPTANCE.json'
REMAINING = [TARGET, 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']


FROZEN = {'repair_source_commit': 'f23c4f3308b471350064bf0d6ad1bdb0fce0d6fb',
 'after': {'bytes': 4739, 'sha256': 'f82bb240dc2bc7172b6f9978dadb1b166ed9be1905167c813c088bd2c09f14e4'},
 'document_pins': {'docs/p1/20261126/p15-smooth-first-compile-repair/REPAIR_CANDIDATE.json': {'bytes': 3943,
                                                                                              'sha256': '1f645e41217eccd8b20b30a24d50f61eebb8c1d19cf2916fa69259f484346039'},
                   'docs/p1/20261126/p15-smooth-first-compile-repair/ACTUAL_SMOOTH_PROBE_RESULT.json': {'bytes': 2306,
                                                                                                        'sha256': 'd259a1eee659ce5e30678c3ebab59563fa65827d619f04c0d3323835c960006c'},
                   'docs/p1/20261126/p15-smooth-first-compile-repair/ACTUAL_U_METADATA.json': {'bytes': 15231,
                                                                                               'sha256': '17e8ab9821764406b1ae1dc0dd5008e679fd31c807c00f2b3dccb8ed12a21ca2'},
                   'docs/p1/20261126/p15-smooth-first-compile-repair/ACTUAL_U_ACCEPTANCE_READ.json': {'bytes': 43665,
                                                                                                      'sha256': '6898ac83a71339590540bd765690ff4a08bc45db589b6be849b647cdb21558af'},
                   'docs/p1/20261126/p15-smooth-first-compile-repair/collect_u_acceptance.py': {'bytes': 32718,
                                                                                                'sha256': 'ed5629f0f950daffff3d82fb241c5c10c37a2697dcd658e9da3b20238e039496'},
                   'docs/p1/20261125/p15-current-public-acceptance/WORD_U_PUBLIC_ACCEPTANCE.json': {'bytes': 13061,
                                                                                                    'sha256': 'efa15b29f13cdef9ede740c4fc66f1c810ae1136f284f003d3c1df5f30fb7d03'},
                   'docs/p1/20261125/p15-current-public-acceptance/ALLGROUP_U_PUBLIC_ACCEPTANCE.json': {'bytes': 8771,
                                                                                                        'sha256': '40813f4ab82bb3751834fbbd29bfecf9aa79f109e875db4a430be0799cb91b83'}}}
V = FROZEN['repair_source_commit']
AFTER = FROZEN['after']
PINS = FROZEN['document_pins']

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


def source_inventory(c, modules):
    return {m: file_fp(c, PROJECT / c.s.h.module_path(m)) for m in sorted(modules)}


def artifact_inventory(c, modules):
    return {m: c.driver.module_artifacts(c.s, m) for m in sorted(modules)}


def normal_path(module):
    return OLD_ROOT / U / module / 'normal' / module / 'NORMAL_PASS.json'


def require_preimage(c):
    path = PROJECT / SOURCE
    need(path.resolve() == path and file_fp(c, path) == BEFORE and path.read_bytes() == c.before,
         'SmoothLicence source is not the exact U preimage; source_after is held')


def archive_binding(c, receipt):
    run = receipt.parent
    need(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
         receipt.resolve() == receipt, 'archive receipt is outside this SmoothLicence/U repair')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    need(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
         record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
         record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
         record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
         record['new_lean_acceptance'] is False and archive.resolve() == archive and
         file_fp(c, archive) == SETUP_FP, 'archive is not the exact U/V/W/script-bound SmoothLicence setup')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}


def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    need(receipts, 'missing active setup without this SmoothLicence/U archive receipt')
    result = {}
    for receipt in receipts:
        result.update(archive_binding(c, receipt))
    return result


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
    need(path.resolve() == path and path.is_file() and not path.is_symlink(), 'SmoothLicence setup is not the fixed regular path')
    original, raw = path.stat(), path.read_bytes()
    need(raw_fp(raw) == SETUP_FP, 'failed SmoothLicence setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    need(archive.parent.resolve() == archive.parent, 'archive parent traverses a symlink')
    fd = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    need(file_fp(c, archive) == SETUP_FP, 'exclusive SmoothLicence archive differs')
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
    need(not os.path.lexists(path), 'SmoothLicence setup remains active')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}


def tree_inventory(c):
    return {commit: c.reader.tree_inventory(OLD_ROOT / commit) for commit in (U, S, Q)}


def load(commit):
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', commit) and re.fullmatch('[0-9a-f]{40}', V),
         'fixed V/W publication and unoptimized Python required')
    need(set(PINS) == {REPAIR, PROBE, DIAGNOSTICS, READ, COLLECTOR, PUBLIC_WORD, PUBLIC_ALLGROUP},
         'fixed publication input set differs')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
         subprocess.run(['git', 'merge-base', '--is-ancestor', V, commit], cwd=REPO).returncode == 0,
         'execution W must descend from repair V')
    script = Path(__file__)
    need(script.is_file() and not script.is_symlink(), 'updater is not a regular file')
    executed = script.read_bytes()
    need(executed == git_file(commit, SCRIPT), 'executed updater differs from W publication')
    docs, raw_docs = {}, {}
    for path, expected in PINS.items():
        raw = git_file(V, path)
        need(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published V/W input differs: ' + path)
        raw_docs[path] = raw
        if path != COLLECTOR:
            docs[path] = json.loads(raw)
    before, after = git_file(U, SOURCE), git_file(V, SOURCE)
    need(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
         'canonical U/V/W SmoothLicence source differs')
    repair = docs[REPAIR]
    need(repair['schema'] == 'p15_smooth_licence_five_proof_splices_candidate_v1' and
         repair['source_base_commit'] == U and repair['source'] == SOURCE and
         repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 5 and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['declaration_count'] == 9 and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe'] == {
             'path': str(Path(docs[PROBE]['candidate']['path']).parent / 'ACTUAL_SMOOTH_PROBE_RESULT.json'),
             **PINS[PROBE], 'compiler_job': 'job_73a4c21270084d40b7e5c0ed397bdea4', 'exit_code': 0} and
         repair['axioms_or_sorry_added'] is False and repair['new_lean_acceptance'] is False and
         repair['whole_P1_5_complete'] is False, 'published proof-only repair differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'original proof splice offset/bytes differ')
        pieces.extend((before[end:start], splice['after'].encode()))
        end = stop
    need(b''.join(pieces) + before[end:] == after, 'bytes changed outside the five proof splices')
    raw = git_file(U, DRIVER)
    entry = OLD_ROOT / U / 'runs/attempt-00000/executed-driver.py'
    need(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw and
         raw_fp(git_file(U, MANIFEST)) == MANIFEST_FP, 'original U reader/manifest differs')
    driver = ModuleType('unchanged_U_smooth_repair_reader'); driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, OLD_ROOT, DRIVER, U_ANCHOR), 'original U environment differs')
    reader = ModuleType('frozen_U_collector_helpers'); reader.__file__ = COLLECTOR
    exec(compile(raw_docs[COLLECTOR], COLLECTOR, 'exec'), reader.__dict__)
    need((reader.U, reader.T, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,
          reader.DRIVER_FP, reader.MANIFEST_FP) ==
         (U, U_ANCHOR, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP) and
         reader.PINNED['schema'] == 'p15_U_fixed_actual_collection_inputs_v1' and
         value_fp(reader.PINNED) == docs[READ]['frozen_actual_input_binding'],
         'frozen U collector helper identity differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(executed)},
        'repair_source_commit': V, 'failed_source_commit': U, 'failed_job': 'job_78ea387bf32d4c57b60346dcf7451e50',
        'module': TARGET, 'source_path': SOURCE, 'source_before': BEFORE, 'source_after': AFTER,
        'failed_setup': {'path': SETUP, **SETUP_FP}, 'published_V_inputs': PINS}
    return SimpleNamespace(commit=commit, driver=driver, reader=reader, s=driver.helpers(), docs=docs,
        before=before, after=after, script=executed, identity=identity)


def read_originals(c, spec):
    reader, driver, s = c.reader, c.driver, c.s
    read = c.docs[READ]
    need(read['schema'] == 'p15_U_original_accepted_prefix_read_v1' and read['source_commit'] == U and
         read['source_anchor_commit'] == U_ANCHOR and read['selected_owners_revalidated'] == ACCEPTED and
         read['current_read_live_source_count'] == 139 and read['current_read_preserved_dependency_count'] == 137 and
         read['normal_or_kernel_commands_executed'] == 0 and value_fp(spec.baseline) == read['current_read_snapshot'],
         'published U accepted-prefix read differs')
    runs = [reader.read_run(driver, s, spec.graph, i, fixed) for i, fixed in enumerate(reader.PINNED['runs'])]
    need(reader.accepting_runs(runs) == {WORD: 0, ALLGROUP: 1} and
         [r[2] for r in runs] == read['original_runs'], 'original U first and partial-run provenance differs')
    common = reader.identity(spec, ACCEPTED)
    bindings = {}
    for module, index, path in [(WORD, 0, PUBLIC_WORD), (ALLGROUP, 1, PUBLIC_ALLGROUP)]:
        fixed = reader.PINNED['owners'][module]
        owner = reader.read_owner(driver, s, spec, runs, module, index, fixed)
        public = reader.flat_summary(runs, index, module, owner, common)
        need(public == c.docs[path] == read['public_summaries'][fixed['public_name']] and
             (owner['owned_count'], owner['public_count']) == (15, 15),
             'original U public owner/count/six-receipt binding differs')
        bindings[module] = driver.acceptance_binding(s, U, module)
    return runs[1][0], runs[1][1], bindings


def prepare(c):
    driver, s = c.driver, c.s
    git, evidence = s.d.original_git_state(REPO), tree_inventory(c)
    need(value_fp(git) == c.docs[READ]['current_dirty_Git_state'], 'original U dirty Git identity differs')
    need({commit: {'entry_count': len(tree), **value_fp(tree)} for commit, tree in evidence.items()} ==
         c.docs[READ]['complete_original_U_S_Q_evidence_inventory'], 'original U/S/Q evidence trees differ')
    spec = driver.preflight(s, U, ACCEPTED)
    need(len(spec.active) == 139 and len(spec.dependency_pins) == 137 and
         set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'U accepted-prefix scope differs')
    later, original_context, accepted = read_originals(c, spec)
    active = s.h.closure(spec.graph, REMAINING); watch = active | set(driver.TARGETS)
    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,
         'remaining8 source/watch scope differs')
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(V, row['path'])
        need(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and
             git_file(c.commit, row['path']) == raw and s.h.imports(raw) == row['all_imports'],
             'unrelated V/W source or imports changed: ' + module)
    sources, artifacts = source_inventory(c, spec.graph), artifact_inventory(c, watch)
    require_preimage(c)
    graph, installed = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: spec.graph[m] for m in active} and
         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live U graph differs')
    need(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
         all(value is None for path, value in artifacts[TARGET].items() if path != SETUP), 'failed artifacts are not setup only')
    for module in REMAINING:
        need(not os.path.lexists(normal_path(module)), 'remaining owner already has a U normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    need(original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING) and
         all(artifacts[m] == fp for m, fp in original_context['preserved_dependency_artifacts'].items()) and
         all(original_context[k] == value for k, value in driver.environment(s, spec.review).items()),
         'original U source/dependency/runtime context differs')
    metadata = c.docs[DIAGNOSTICS]
    failure = metadata['failures'][TARGET]
    need(metadata['source_commit'] == U and set(metadata['failures']) == {TARGET} and
         set(metadata['accepted_owners']) == set(ACCEPTED) and failure['source'] == {'path': str(PROJECT / SOURCE), **BEFORE} and
         failure['artifact_slots'][str(PROJECT / SETUP)] == {'path': str(PROJECT / SETUP), **SETUP_FP},
         'actual U failure metadata/source/setup scope differs')
    expected_normal = OLD_ROOT / U / TARGET / 'normal' / TARGET / 'attempt-00000/normal-command.json'
    need(failure['normal_metadata']['path'] == str(expected_normal) and
         file_fp(c, expected_normal) == pin(failure['normal_metadata']) and
         s.api.read_json(expected_normal) == failure['normal_command'], 'original failed command metadata differs')
    normal = failure['normal_command']
    normal_log = {'path': normal['log'], 'bytes': normal['log_bytes'], 'sha256': normal['log_sha256']}
    probe = c.docs[PROBE]
    need(probe['source_base_commit'] == U and probe['exit_code'] == 0 and pin(probe['candidate']) == AFTER and
         probe['original_source'] == BEFORE and probe['whole_original_module_submitted'] is True and
         probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
         probe['original_serializer_and_guard_used'] is True and probe['lake_no_build_env_lean'] is True and
         probe['accepted_prefix_live_source_count'] == 139 and probe['accepted_prefix_dependency_count'] == 137 and
         probe['watched_source_slots'] == 360 and probe['watched_modules'] == 160 and
         probe['watched_artifact_slots'] == 3360 and probe['U_original_Word_AllGroup_acceptances_preserved'] == ACCEPTED and
         probe['original_source_and_failed_setup_preserved'] is True and
         probe['all_original_U_S_Q_evidence_runtime_and_Git_preserved'] is True and
         probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False,
         'whole-module no-output probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    # These two exact mutable paths have separate preimage/archive/install checks.
    # All other frozen U inputs remain byte-for-byte fixed through the operation.
    mutable = {str(PROJECT / SOURCE), str(PROJECT / SETUP)}
    extras = {**{p: fp for p, fp in c.reader.PINNED['extra_pins'].items() if p not in mutable},
        str(expected_normal): pin(failure['normal_metadata']),
        normal_log['path']: pin(normal_log), str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_SMOOTH_PROBE_RESULT.json'): PINS[PROBE]}
    retained = {**original_context['retained_original_evidence'], **archives, **extras}
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
         all(file_fp(c, path) == fp for path, fp in state.retained.items()), 'original U/S/Q/retained evidence changed')
    need(c.driver.snapshot(c.s, state.spec) == state.spec.baseline and
         {m: c.driver.acceptance_binding(c.s, U, m) for m in ACCEPTED} == state.accepted and
         c.s.d.original_git_state(REPO) == state.git and
         all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'accepted U context/runtime/Git changed')


def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'source_slots': state.sources, 'artifact_slots': state.artifacts, 'original_U_S_Q_evidence': state.evidence,
        'retained_inputs': state.retained, 'accepted_U_bindings': state.accepted,
        'accepted_prefix_context': state.spec.baseline, 'original_U_context': state.context,
        'Git_before': state.git, 'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = archive_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, archived=True)
    fresh = driver.preflight(s, U, REMAINING)
    need(fresh.active == state.active and fresh.graph == state.spec.graph and fresh.sources == state.spec.sources and
         fresh.order == REMAINING and len(fresh.dependency_pins) == 149 and
         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
             fresh.dependency_pins[m] == state.artifacts[m] for m in ACCEPTED) and
         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and
         len(fresh.supplier_evidence) == 21, 'unchanged U eight-target preflight differs')
    unchanged(c, state, archived=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_U_PREFLIGHT.json', {'source_commit': U, 'targets': fresh.order,
        'active_source_count': 157, 'preserved_dependency_count': 149,
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require_preimage(c)
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    backup = run / 'backups' / SOURCE
    need(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True and
         file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
         (PROJECT / SOURCE).read_bytes() == c.after, 'exact single SmoothLicence installation/backup differs')
    post = copy.copy(fresh); post.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline); expected['selected_live_sources'][TARGET] = AFTER['sha256']
    need(driver.snapshot(s, post) == expected, 'post-install dependency/runtime context differs')
    unchanged(c, state, archived=True, installed=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: fresh.graph[m] for m in fresh.active} and
         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', {'status': 'EXACT_SINGLE_SMOOTH_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'identity': c.identity, 'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_U_eight_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,
        'active_source_count': 157, 'preserved_dependency_count': 149,
        'Word_AllGroup_U_and_all_eight_earlier_prior_acceptances_preserved': True,
        'original_U_S_Q_evidence_other_artifacts_runtime_and_Git_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False})


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-commit', required=True, help='updater publication W')
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--apply', action='store_true')
    p.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = p.parse_args(); c = load(args.source_commit)
    if args.check:
        need(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_SMOOTH_PREFLIGHT_ONLY', 'identity': c.identity,
            'accepted_U_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 139, 'accepted_prefix_dependencies': 137,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_U_eight_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        need(run.is_absolute() and run.resolve() == run and run.parent == runs and
             re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected SmoothLicence worker path')
        try:
            apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_SMOOTH_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
            mutated_modules=[TARGET], new_lean_acceptance=False, path=str(run / 'SOURCE_REPAIR_RESULT.json'))
        return 0
    need(runs.resolve() == runs, 'evidence parent traverses a symlink')
    run = c.s.d.attempt(runs); before = c.s.d.original_git_state(REPO)
    c.s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-source-repair.py'; c.s.d.write_frozen(executed, c.script)
    try:
        command = c.s.ops.run(run, 'serialized-source-repair', c.s.h.serialize(0, run / 'SOURCE_REPAIR_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--apply', '--inside-lane', str(run)]), relay=True)
        need(command['exit_code'] == 0 and command['actual_built_modules'] == [] and command['actual_failed_modules'] == [],
             'serialized SmoothLicence repair held; inspect private failure evidence')
    finally:
        after = c.s.d.original_git_state(REPO); c.s.d.save(run / 'GIT_AFTER.json', after)
        need(after == before, 'original dirty Git state changed')
    return 0


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'EXACT_SINGLE_SMOOTH_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
