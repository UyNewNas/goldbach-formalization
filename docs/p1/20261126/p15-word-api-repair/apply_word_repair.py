#!/usr/bin/env python3
"""Install only the T WordDictionary repair after durable archival and S preflight.

U publishes this updater. S owns Family and the failed WordDictionary attempt;
AllK and Admissible remain Q owners. T binds the two-splice repair and evidence.
This wrapper uses the original S reader and installer without Lean execution.
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
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
T = '999510c460e6e026c8cabe46c5f35876f7201f8e'
S_ANCHOR = '0935516b9bd978a61248c81b59776d1eb47f6044'
FIRST_JOB = 'job_bf1ad9f0adbc4c8a9fe4b05e99addf4d'
FAILED_JOB = 'job_fe03565fc9d94e01a9f87ba314af1933'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-word-api-repair-v1')
SCRIPT = 'docs/p1/20261126/p15-word-api-repair/apply_word_repair.py'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 130643, 'sha256': 'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'}
MANIFEST_FP = {'bytes': 346806, 'sha256': '1c6d8499822f69f35469c4bbc222f85d1e46d6a5c977bd4f5c4cdd649520ba86'}
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
ACCEPTED = [FAMILY]
TARGET = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
SOURCE = 'ImbalancedChen/P5IndependentPrimeSourceWordDictionary.lean'
SETUP = '.lake/build/ir/ImbalancedChen/P5IndependentPrimeSourceWordDictionary.setup.json'
ARCHIVE_NAME = 'P5IndependentPrimeSourceWordDictionary.setup.json'
BEFORE = {'bytes': 5613, 'sha256': '8fd465024656d9cc3998b7f810d92ab6316f50c1817f0736e6bb0f88021d49b1'}
AFTER = {'bytes': 5672, 'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'}
SETUP_FP = {'bytes': 6329802, 'sha256': '0ab1595e7cb434fea199eefea3f7e041db1e24f030858dbfa50304c4ba07c6bf'}
PREFIX = 'docs/p1/20261126/p15-word-first-compile-repair/'
REPAIR, PROBE = PREFIX + 'REPAIR_CANDIDATE.json', PREFIX + 'ACTUAL_WORD_PROBE_RESULT.json'
DIAGNOSTICS, READ = PREFIX + 'ACTUAL_S_METADATA.json', PREFIX + 'ACTUAL_S_ACCEPTANCE_READ.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/FAMILY_S_PUBLIC_ACCEPTANCE.json'
PINS = {
    REPAIR: {'bytes': 1622, 'sha256': '0b34bf1a5a9c18bd81842b02d6fc7a2413beb013e0de53bb17cc9f1c17152aa4'},
    PROBE: {'bytes': 1718, 'sha256': 'eaae995a5a5bbdcaefb8e05ce34839c44dcd6bf9c7a08b8aa7ea726a13d4c884'},
    DIAGNOSTICS: {'bytes': 23200, 'sha256': 'f834468c953f2956b84175fde3c4af531f691b88c95a5036d190bcdd2c9e9118'},
    READ: {'bytes': 35862, 'sha256': '526bd18331d0a15f1e3acb3fa1305bc23b9eea1dc6850f0b0bbaf187a3e5fe60'},
    PUBLIC: {'bytes': 13244, 'sha256': '12f18cc8e6160e645c17a7b7f5ae94f616d7c940a97289080698aaaee973fcfa'},
}
REMAINING = [TARGET, 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection', 'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid', 'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']


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
    result = {}
    for commit in (S, Q):
        base = OLD_ROOT / commit
        need(base.is_dir() and base.resolve() == base, 'original S/Q evidence root differs')
        files = {}
        for path in sorted(base.rglob('*')):
            need(not path.is_symlink(), 'symlink in original S/Q evidence')
            files[str(path.relative_to(base))] = 'directory' if path.is_dir() else file_fp(c, path)
        result[commit] = files
    return result


def source_inventory(c, modules):
    return {m: file_fp(c, PROJECT / c.s.h.module_path(m)) for m in sorted(modules)}


def artifact_inventory(c, modules):
    return {m: c.driver.module_artifacts(c.s, m) for m in sorted(modules)}


def normal_path(module):
    return OLD_ROOT / S / module / 'normal' / module / 'NORMAL_PASS.json'


def require_preimage(c):
    path = PROJECT / SOURCE
    need(path.resolve() == path and file_fp(c, path) == BEFORE and path.read_bytes() == c.before,
         'WordDictionary source is not the exact S preimage; source_after is held')


def load(commit):
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', commit) and re.fullmatch('[0-9a-f]{40}', T) and
         set(PINS) == {REPAIR, PROBE, DIAGNOSTICS, READ, PUBLIC}, 'exact T/U publications and unoptimized Python required')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
         subprocess.run(['git', 'merge-base', '--is-ancestor', T, commit], cwd=REPO).returncode == 0,
         'execution U must descend from repair T')
    script = Path(__file__)
    need(script.is_file() and not script.is_symlink(), 'updater is not a regular file')
    executed = script.read_bytes()
    need(executed == git_file(commit, SCRIPT), 'executed updater differs from U publication')
    docs = {}
    for path, expected in PINS.items():
        raw = git_file(T, path)
        need(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published T/U input differs: ' + path)
        docs[path] = json.loads(raw)
    before, after = git_file(S, SOURCE), git_file(T, SOURCE)
    need(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
         'canonical S/T/U WordDictionary source differs')
    repair = docs[REPAIR]
    need(repair['schema'] == 'p15_word_dictionary_two_proof_splices_candidate_v1' and
         repair['source_base_commit'] == S and repair['source'] == SOURCE and
         repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 2 and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['declaration_count'] == 9 and repair['axioms_or_sorry_added'] is False and
         repair['compiler_probe_performed'] is True and repair['actual_whole_module_probe'] == {
             'path': str(Path(docs[PROBE]['candidate']['path']).parent / 'ACTUAL_WORD_PROBE_RESULT.json'),
             **PINS[PROBE], 'compiler_job': 'job_9c4192ff119349909fe379179bb9447f', 'exit_code': 0} and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'published two-splice WordDictionary repair differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'original splice offset/bytes differ')
        pieces.extend((before[end:start], splice['after'].encode()))
        end = stop
    need(b''.join(pieces) + before[end:] == after, 'WordDictionary payload changes bytes outside two splices')
    raw = git_file(S, DRIVER)
    entry = OLD_ROOT / S / 'runs/attempt-00000/executed-driver.py'
    need(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw and
         raw_fp(git_file(S, MANIFEST)) == MANIFEST_FP, 'original S reader/manifest differs')
    driver = ModuleType('unchanged_S_word_repair_reader')
    driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, OLD_ROOT, DRIVER, S_ANCHOR), 'original S reader environment differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(executed)},
        'repair_source_commit': T, 'failed_source_commit': S, 'failed_job': FAILED_JOB,
        'module': TARGET, 'source_path': SOURCE, 'source_before': BEFORE, 'source_after': AFTER,
        'failed_setup': {'path': SETUP, **SETUP_FP}, 'published_T_inputs': PINS}
    return SimpleNamespace(commit=commit, driver=driver, s=driver.helpers(), docs=docs,
                           before=before, after=after, script=executed, identity=identity)


def read_originals(c, spec):
    s, driver = c.s, c.driver
    read, public, metadata = c.docs[READ], c.docs[PUBLIC], c.docs[DIAGNOSTICS]
    need(read['schema'] == 'p15_S_original_family_acceptance_read_v1' and read['source_commit'] == S and
         read['source_anchor_commit'] == S_ANCHOR and read['selected_owners_revalidated'] == ACCEPTED and
         read['current_read_live_source_count'] == 75 and read['current_read_preserved_dependency_count'] == 74 and
         read['normal_or_kernel_commands_executed'] == 0 and
         value_fp(spec.baseline) == read['current_read_snapshot'] and
         public == read['public_summaries']['FAMILY_S_PUBLIC_ACCEPTANCE'], 'T accepted-prefix read differs')
    need(public['source_commit'] == S and public['source_anchor_commit'] == S_ANCHOR and
         set(public['owners']) == {FAMILY} and public['compiler_job'] == FIRST_JOB and
         public['original_run'] == 'runs/attempt-00000' and
         public['driver'] == {'commit': S, 'path': DRIVER, **DRIVER_FP} and
         public['source_manifest'] == {'commit': S, 'path': MANIFEST, **MANIFEST_FP},
         'Family original S public origin differs')
    results, contexts = [], []
    for index in (0, 1):
        attempt = 'attempt-%05d' % index
        run = OLD_ROOT / S / 'runs' / attempt
        pins, record = metadata[attempt], read['original_runs'][index]
        need(record['source_commit'] == S and record['compiler_job'] == (FIRST_JOB if index == 0 else FAILED_JOB) and
             record['original_run'] == str(run) and file_fp(c, run / 'executed-driver.py') == DRIVER_FP,
             'original S run/public job differs')
        need(set(pins) == {'RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
                           'GIT_BEFORE.json', 'GIT_AFTER.json'}, 'S metadata run inventory differs')
        for name, row in pins.items():
            need(row['path'] == str(run / name) and file_fp(c, run / name) == pin(row) and
                 record['evidence_bindings'][name] == row, 'original S evidence pin differs: ' + name)
        result, worker, context = [s.api.read_json(run / name) for name in
                                  ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json')]
        targets = ACCEPTED if index == 0 else ACCEPTED + REMAINING
        for item in (result, worker):
            need(item['source_commit'] == S and item['targets'] == targets and item['accepted_owners'] == ACCEPTED and
                 set(item['acceptance_bindings']) == {FAMILY} and
                 item['reused_complete_selected_owners'] == ([] if index == 0 else ACCEPTED) and
                 set(item['failures']) == (set() if index == 0 else {TARGET}) and
                 item['published_source_count'] == 360 and item['selected_live_source_count'] == (75 if index == 0 else 157) and
                 all(item[key] is False for key in ('whole_P1_complete', 'whole_P1_5_complete',
                    'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                    'old_receipts_rebound', 'old_P3_REUSE_changed')) and
                 not any(key in item for key in ('context_error', 'final_context_error', 'git_error')),
                 'original S accepted/failed scope differs')
        need(all(result.get(key) == value for key, value in worker.items()) and
             result['worker_exit_code'] == index and result['all_selected_owners_accepted'] is (index == 0),
             'original S RESULT/WORKER terminal identity differs')
        for stem in ('CONTEXT', 'GIT'):
            need(pin(pins[stem + '_BEFORE.json']) == pin(pins[stem + '_AFTER.json']), 'original S context pair differs')
        need(context['committed_inputs']['source_commit'] == S and
             context['committed_inputs']['source_anchor_commit'] == S_ANCHOR and
             s.d.compile_order([], context['committed_inputs']['selected_targets'], spec.graph) == targets,
             'original S requested/executed source scope differs')
        results.append(result)
        contexts.append(context)
    first, later = results
    need('dispatch_error' not in first and first['final_stock_readiness']['exit_code'] == 0 and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         public['original_result'] == pin(metadata['attempt-00000']['RESULT.json']) and
         public['original_worker_result'] == pin(metadata['attempt-00000']['WORKER_RESULT.json']) and
         public['later_same_source_reuse'] == read['original_runs'][1], 'S success/partial provenance differs')
    driver.require_completed_existing_owner(s, S, spec, FAMILY, spec.initial_owners[FAMILY])
    binding = driver.acceptance_binding(s, S, FAMILY)
    need(binding == first['acceptance_bindings'][FAMILY] == later['acceptance_bindings'][FAMILY],
         'current S Family acceptance differs from first acceptance/later reuse')
    owner = public['owners'][FAMILY]
    paths = {key: Path(path) for key, path in owner['receipt_paths'].items()}
    need(set(paths) == {'normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence'} and
         {key: file_fp(c, path) for key, path in paths.items()} == owner['receipt_bindings'] and
         binding['normal_receipt'] == {'path': str(paths['normal']), **owner['receipt_bindings']['normal']} and
         binding['audits'] == [{'plan': {'path': str(paths['audit_plan']), **owner['receipt_bindings']['audit_plan']},
                               'result': {'path': str(paths['audit_result']), **owner['receipt_bindings']['audit_result']}}],
         'original S six-receipt acceptance binding differs')
    counted = s.api.read_json(paths['audit_result'])
    need((counted['total_owned_exports'], counted['total_public_exports']) ==
         (owner['owned_count'], owner['public_count']) == (27, 27) and
         owner['audit_id'] == 'b2f9953a401fa5dd488b' and owner['compiler_job'] == FIRST_JOB and
         owner['source_commit'] == S and owner['source_sha256'] == spec.sources[FAMILY], 'Family audit/source differs')
    return later, contexts[1], {FAMILY: binding}


def archive_binding(c, receipt):
    run = receipt.parent
    need(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
         receipt.resolve() == receipt, 'archive receipt is outside this WordDictionary/U repair')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    need(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
         record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
         record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
         record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
         record['new_lean_acceptance'] is False and archive.resolve() == archive and
         file_fp(c, archive) == SETUP_FP, 'archive is not the exact S/T/U/script-bound WordDictionary setup')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}


def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    need(receipts, 'missing active setup without this WordDictionary/U archive receipt')
    result = {}
    for receipt in receipts:
        result.update(archive_binding(c, receipt))
    return result


def prepare(c):
    driver, s = c.driver, c.s
    git, evidence = s.d.original_git_state(REPO), tree_inventory(c)
    need({commit: {'entry_count': len(tree), **value_fp(tree)} for commit, tree in evidence.items()} ==
         c.docs[READ]['complete_original_S_and_Q_evidence_inventory'],
         'original S/Q evidence trees differ from the actual T acceptance read')
    spec = driver.preflight(s, S, ACCEPTED)
    need(len(spec.active) == 75 and len(spec.dependency_pins) == 74 and
         set(spec.initial_owners) == {FAMILY} and TARGET not in spec.active, 'S accepted-prefix scope differs')
    later, original_context, accepted = read_originals(c, spec)
    active = s.h.closure(spec.graph, REMAINING)
    watch = active | set(driver.TARGETS)
    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,
         'remaining10 source/watch scope differs')
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(T, row['path'])
        need(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and
             git_file(c.commit, row['path']) == raw and s.h.imports(raw) == row['all_imports'],
             'unrelated T/U published source or imports changed: ' + module)
    sources, artifacts = source_inventory(c, spec.graph), artifact_inventory(c, watch)
    require_preimage(c)
    graph, installed = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: spec.graph[m] for m in active} and
         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live S graph differs')
    need(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
         all(value is None for path, value in artifacts[TARGET].items() if path != SETUP), 'WordDictionary artifacts are not setup only')
    for module in REMAINING:
        need(not os.path.lexists(normal_path(module)), 'remaining owner already has an S normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    need(original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING) and
         all(artifacts[m] == fp for m, fp in original_context['preserved_dependency_artifacts'].items()) and
         all(original_context[k] == value for k, value in driver.environment(s, spec.review).items()),
         'original S source/dependency/runtime context differs')
    metadata = c.docs[DIAGNOSTICS]
    need(set(metadata) == {'attempt-00000', 'attempt-00001', 'word_source', 'failed_word_setup',
                           'word_normal', 'family_audit', 'family_install'} and
         metadata['word_source'] == {'path': str(PROJECT / SOURCE), **BEFORE} and
         metadata['failed_word_setup'] == {'path': str(PROJECT / SETUP), **SETUP_FP},
         'actual S failure metadata/source/setup scope differs')
    observed_paths = {
        'word_normal': OLD_ROOT / S / TARGET / 'normal' / TARGET / 'attempt-00000/normal-command.json',
        'family_audit': Path(c.docs[PUBLIC]['owners'][FAMILY]['receipt_paths']['audit_result']),
        'family_install': Path('/workspace/p1-complete-proof/20261126-p15-family-api-repair-v1') /
                          S / 'runs/attempt-00000/SOURCE_REPAIR_RESULT.json'}
    observed = [metadata[key] for key in observed_paths]
    for key, path in observed_paths.items():
        need(metadata[key]['path'] == str(path) and file_fp(c, path) == pin(metadata[key]),
             'actual S failure/acceptance/installation evidence differs')
    probe = c.docs[PROBE]
    need(probe['source_base_commit'] == S and probe['exit_code'] == 0 and pin(probe['candidate']) == AFTER and
         probe['original_source'] == BEFORE and probe['whole_original_module_submitted'] is True and
         probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
         probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False and
         probe['S_original_Family_acceptance_preserved'] == ACCEPTED and
         probe['all_original_S_and_Q_evidence_runtime_and_Git_preserved'] is True,
         'WordDictionary whole-module no-output probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    retained = {**original_context['retained_original_evidence'], **archives,
        **{row['path']: pin(row) for row in observed}, str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_WORD_PROBE_RESULT.json'): PINS[PROBE]}
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
         all(file_fp(c, path) == fp for path, fp in state.retained.items()), 'original S/Q/retained evidence changed')
    need(c.driver.snapshot(c.s, state.spec) == state.spec.baseline and
         {m: c.driver.acceptance_binding(c.s, S, m) for m in ACCEPTED} == state.accepted and
         c.s.d.original_git_state(REPO) == state.git and
         all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'accepted S context/runtime/Git changed')


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
    need(path.resolve() == path and path.is_file() and not path.is_symlink(), 'WordDictionary setup is not the fixed regular path')
    original, raw = path.stat(), path.read_bytes()
    need(raw_fp(raw) == SETUP_FP, 'failed WordDictionary setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    need(archive.parent.resolve() == archive.parent, 'archive parent traverses a symlink')
    fd = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    need(file_fp(c, archive) == SETUP_FP, 'exclusive WordDictionary archive differs')
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
    need(not os.path.lexists(path), 'WordDictionary setup remains active')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}


def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'source_slots': state.sources, 'artifact_slots': state.artifacts, 'original_S_Q_evidence': state.evidence,
        'retained_inputs': state.retained, 'accepted_S_bindings': state.accepted,
        'accepted_prefix_context': state.spec.baseline, 'original_S_context': state.context,
        'Git_before': state.git, 'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = archive_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, archived=True)
    # Actual S preflight runs with the unchanged WordDictionary preimage, before install.
    fresh = driver.preflight(s, S, REMAINING)
    need(fresh.active == state.active and fresh.graph == state.spec.graph and fresh.sources == state.spec.sources and
         fresh.order == REMAINING and len(fresh.dependency_pins) == 147 and
         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
         fresh.initial_owners[FAMILY]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
         fresh.dependency_pins[FAMILY] == state.artifacts[FAMILY] and
         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and
         len(fresh.supplier_evidence) == 20, 'unchanged S ten-target preflight differs')
    unchanged(c, state, archived=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_S_PREFLIGHT.json', {'source_commit': S, 'targets': fresh.order,
        'active_source_count': 157, 'preserved_dependency_count': 147,
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require_preimage(c)
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    backup = run / 'backups' / SOURCE
    need(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True and
         file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
         (PROJECT / SOURCE).read_bytes() == c.after, 'exact single WordDictionary installation/backup differs')
    post = copy.copy(fresh)
    post.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline)
    expected['selected_live_sources'][TARGET] = AFTER['sha256']
    need(driver.snapshot(s, post) == expected, 'post-install dependency/runtime context differs')
    unchanged(c, state, archived=True, installed=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: fresh.graph[m] for m in fresh.active} and
         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', {'status': 'EXACT_SINGLE_WORD_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'identity': c.identity, 'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_S_ten_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,
        'active_source_count': 157, 'preserved_dependency_count': 147,
        'Family_original_S_acceptance_and_AllK_Admissible_Q_acceptances_preserved': True,
        'original_S_Q_evidence_other_artifacts_runtime_and_Git_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True, help='updater publication U')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--apply', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.check:
        need(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_WORD_PREFLIGHT_ONLY', 'identity': c.identity,
            'accepted_S_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 75, 'accepted_prefix_dependencies': 74,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_S_ten_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        need(run.is_absolute() and run.resolve() == run and run.parent == runs and
             re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected WordDictionary worker path')
        try:
            apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_WORD_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
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
             'serialized WordDictionary repair held; inspect private failure evidence')
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
        print(json.dumps({'status': 'EXACT_SINGLE_WORD_HELD', 'error_type': type(error).__name__,
                          'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
