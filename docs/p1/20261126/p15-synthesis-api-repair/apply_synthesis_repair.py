#!/usr/bin/env python3
"""Install one proof-only SharpPrimeSynthesis repair under the original AA gates.

Mean keeps its original AA acceptance and same-AA reuse. All older owners retain
Y/W/U/S/Q or their earlier identities. Only the failed setup and source may change.
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
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
AA_ANCHOR = 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
FAILED_JOB = 'job_2d377894edb64660880d7f3e8783b2ee'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1')
SCRIPT = 'docs/p1/20261126/p15-synthesis-api-repair/apply_synthesis_repair.py'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 251538, 'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}
MANIFEST_FP = {'bytes': 359729, 'sha256': '39eaeca8207c7f387d6b5c6e44d85b38836c721c3c7b1cf1172bbe4c7f95d6c3'}
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ACCEPTED = [MEAN]
TARGET = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
SOURCE = 'ImbalancedChen/P5OriginalSharpPrimeSynthesis.lean'
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.setup.json'
ARCHIVE_NAME = 'P5OriginalSharpPrimeSynthesis.setup.json'
BEFORE = {'bytes': 14458, 'sha256': '9d8b3b273ade3bf3a35aff7469e16f5fac24d9896eb31171c48c0f04328a8cd7'}
AFTER = {'bytes': 14462, 'sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322'}
SETUP_FP = {'bytes': 6417017, 'sha256': '42acce65ed6a2b300809309fd909236cd4de13bfb9b5abe1cf27baac10dca87e'}
PREFIX = 'docs/p1/20261126/p15-synthesis-first-compile-repair/'
REPAIR, PROBE = PREFIX + 'REPAIR_CANDIDATE.json', PREFIX + 'ACTUAL_SYNTHESIS_PROBE_RESULT.json'
DIAGNOSTICS, READ = PREFIX + 'ACTUAL_AA_METADATA.json', PREFIX + 'ACTUAL_AA_ACCEPTANCE_READ.json'
COLLECTOR = PREFIX + 'collect_aa_acceptance.py'
PUBLIC_MEAN = 'docs/p1/20261125/p15-current-public-acceptance/MEAN_AA_PUBLIC_ACCEPTANCE.json'
REMAINING = [TARGET, 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']

# Exact AB publication, six raw inputs and actual successful probe identity.
INPUTS = {'repair_source_commit': '60e6b6e18fbda5f6b0e997d15392b32100e854d9',
 'probe_job': 'job_d98b1db30a4d406887de810840109325',
 'after': {'bytes': 14462, 'sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322'},
 'document_pins': {'docs/p1/20261126/p15-synthesis-first-compile-repair/REPAIR_CANDIDATE.json': {'bytes': 2371,
                                                                                                 'sha256': '6a64e01ee06cbe340e151d66de8916143bf7c5b43e32c495650004e1e860bcec'},
                   'docs/p1/20261126/p15-synthesis-first-compile-repair/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 3645,
                                                                                                              'sha256': '42c93650259a85f6709d46c80286168f59ec60489f9d19b02816ff4c30d06a1b'},
                   'docs/p1/20261126/p15-synthesis-first-compile-repair/ACTUAL_AA_METADATA.json': {'bytes': 12121,
                                                                                                   'sha256': '8ed51ed62a58c41efb5cb58be6dc8ec61dddca46ce80fd87c424106646660d07'},
                   'docs/p1/20261126/p15-synthesis-first-compile-repair/ACTUAL_AA_ACCEPTANCE_READ.json': {'bytes': 37016,
                                                                                                          'sha256': '6e850427d91c24550cbc7b3f3764435514d7b8cc83cd29a149c7949c196b15c8'},
                   'docs/p1/20261126/p15-synthesis-first-compile-repair/collect_aa_acceptance.py': {'bytes': 33407,
                                                                                                    'sha256': '6ce8532a749cceb7247df18fd0fecc5cd4c288888a82215e64cab65722d7bdb7'},
                   'docs/p1/20261125/p15-current-public-acceptance/MEAN_AA_PUBLIC_ACCEPTANCE.json': {'bytes': 11979,
                                                                                                     'sha256': '6d13eca3d7080946540ce94e98c169a2c38c1a5e7b0232294ae5557b67a5ced7'}}}
AB = INPUTS['repair_source_commit'] if isinstance(INPUTS, dict) else None
PINS = INPUTS['document_pins'] if isinstance(INPUTS, dict) else {}
PROBE_JOB = INPUTS['probe_job'] if isinstance(INPUTS, dict) else None


PRIOR_FAILED_PROBES = [{'candidate': {'bytes': 14464, 'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
  'compiler_job': 'job_2cfa137d1e284d9da5e3470f88cb0438',
  'exit_code': 1,
  'result': {'bytes': 5727,
             'path': '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json',
             'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'}}]
FAILED_PROBE_RETAINED = {'/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                        'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                       'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                     'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'}}

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
    return OLD_ROOT / AA / module / 'normal' / module / 'NORMAL_PASS.json'

def require_preimage(c):
    path = PROJECT / SOURCE
    need(path.resolve() == path and file_fp(c, path) == BEFORE and path.read_bytes() == c.before,
         'SharpPrimeSynthesis source is not the exact AA preimage; source_after is held')

def archive_binding(c, receipt):
    run = receipt.parent
    need(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
         receipt.resolve() == receipt, 'archive receipt is outside this SharpPrimeSynthesis/AC repair')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    need(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
         record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
         record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
         record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
         record['new_lean_acceptance'] is False and archive.resolve() == archive and
         file_fp(c, archive) == SETUP_FP, 'archive is not the exact AA/AB/AC/script-bound SharpPrimeSynthesis setup')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}

def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    need(receipts, 'missing active setup without this SharpPrimeSynthesis/AC archive receipt')
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
    need(path.resolve() == path and path.is_file() and not path.is_symlink(), 'SharpPrimeSynthesis setup is not the fixed regular path')
    original, raw = path.stat(), path.read_bytes()
    need(raw_fp(raw) == SETUP_FP, 'failed SharpPrimeSynthesis setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    need(archive.parent.resolve() == archive.parent, 'archive parent traverses a symlink')
    fd = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    need(file_fp(c, archive) == SETUP_FP, 'exclusive SharpPrimeSynthesis archive differs')
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
    need(not os.path.lexists(path), 'SharpPrimeSynthesis setup remains active')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}

def tree_inventory(c):
    return {commit: c.reader.tree_inventory(OLD_ROOT / commit) for commit in (AA, Y, W, U, S, Q)}

def load(commit):
    need(__debug__ and isinstance(INPUTS, dict) and re.fullmatch('[0-9a-f]{40}', commit) and
         isinstance(AB, str) and re.fullmatch('[0-9a-f]{40}', AB) and
         isinstance(PROBE_JOB, str) and re.fullmatch('job_[0-9a-f]{32}', PROBE_JOB),
         'actual AB/AC publications and probe identity must be frozen before any access')
    need(INPUTS['after'] == AFTER and set(PINS) == {REPAIR, PROBE, DIAGNOSTICS, READ, COLLECTOR, PUBLIC_MEAN},
         'fixed publication input set differs')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
         subprocess.run(['git', 'merge-base', '--is-ancestor', AB, commit], cwd=REPO).returncode == 0,
         'execution AC must descend from repair AB')
    script = Path(__file__)
    need(script.is_file() and not script.is_symlink(), 'updater is not a regular file')
    executed = script.read_bytes()
    need(executed == git_file(commit, SCRIPT), 'executed updater differs from AC publication')
    docs, raw_docs = {}, {}
    for path, expected in PINS.items():
        raw = git_file(AB, path)
        need(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published AB/AC input differs: ' + path)
        raw_docs[path] = raw
        if path != COLLECTOR:
            docs[path] = json.loads(raw)
    before, after = git_file(AA, SOURCE), git_file(AB, SOURCE)
    need(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
         'canonical AA/AB/AC SharpPrimeSynthesis source differs')
    repair = docs[REPAIR]
    need(repair['schema'] == 'p15_sharp_prime_synthesis_one_proof_splice_candidate_v1' and
         repair['source_base_commit'] == AA and repair['source'] == SOURCE and
         repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 1 and
         repair['original_failure_metadata'] == PINS[DIAGNOSTICS] and
         repair['prior_failed_whole_module_probes'] == PRIOR_FAILED_PROBES and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['declaration_count'] == 18 and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe'] == {
             'path': str(Path(docs[PROBE]['candidate']['path']).parent / 'ACTUAL_SYNTHESIS_PROBE_RESULT.json'),
             **PINS[PROBE], 'compiler_job': PROBE_JOB, 'exit_code': 0} and
         repair['axioms_or_sorry_added'] is False and repair['new_lean_acceptance'] is False and
         repair['whole_P1_5_complete'] is False, 'published proof-only repair differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'original proof splice offset/bytes differ')
        pieces.extend((before[end:start], splice['after'].encode()))
        end = stop
    need(b''.join(pieces) + before[end:] == after, 'bytes changed outside the one proof splice')
    raw = git_file(AA, DRIVER)
    entry = OLD_ROOT / AA / 'runs/attempt-00000/executed-driver.py'
    need(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw and
         raw_fp(git_file(AA, MANIFEST)) == MANIFEST_FP, 'original AA reader/manifest differs')
    driver = ModuleType('unchanged_AA_synthesis_repair_reader'); driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, OLD_ROOT, DRIVER, AA_ANCHOR), 'original AA environment differs')
    reader = ModuleType('frozen_AA_collector_helpers'); reader.__file__ = COLLECTOR
    exec(compile(raw_docs[COLLECTOR], COLLECTOR, 'exec'), reader.__dict__)
    need((reader.AA, reader.Z, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,
          reader.DRIVER_FP, reader.MANIFEST_FP) ==
         (AA, AA_ANCHOR, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP) and
         reader.PINNED['schema'] == 'p15_AA_fixed_actual_collection_inputs_v1' and
         reader.PINNED['runs'][1]['compiler_job'] == FAILED_JOB and
         value_fp(reader.PINNED) == docs[READ]['frozen_actual_input_binding'],
         'frozen AA collector helper identity differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(executed)},
        'repair_source_commit': AB, 'failed_source_commit': AA, 'failed_job': FAILED_JOB,
        'module': TARGET, 'source_path': SOURCE, 'source_before': BEFORE, 'source_after': AFTER,
        'failed_setup': {'path': SETUP, **SETUP_FP}, 'published_AB_inputs': PINS}
    return SimpleNamespace(commit=commit, driver=driver, reader=reader, s=driver.helpers(), docs=docs,
        before=before, after=after, script=executed, identity=identity)

def read_originals(c, spec):
    reader, driver, s = c.reader, c.driver, c.s
    read = c.docs[READ]
    need(read['schema'] == 'p15_AA_original_accepted_prefix_read_v1' and read['source_commit'] == AA and
         read['source_anchor_commit'] == AA_ANCHOR and read['selected_owners_revalidated'] == ACCEPTED and
         read['current_read_live_source_count'] == 108 and read['current_read_preserved_dependency_count'] == 107 and
         read['normal_or_kernel_commands_executed'] == 0 and value_fp(spec.baseline) == read['current_read_snapshot'],
         'published AA accepted-prefix read differs')
    runs = [reader.read_run(driver, s, spec.graph, i, fixed) for i, fixed in enumerate(reader.PINNED['runs'])]
    need(reader.accepting_runs(runs) == {MEAN: 0} and
         [r[2] for r in runs] == read['original_runs'], 'original AA first and partial-run provenance differs')
    common = reader.identity(spec, ACCEPTED)
    bindings = {}
    for module, index, path in [(MEAN, 0, PUBLIC_MEAN)]:
        fixed = reader.PINNED['owners'][module]
        owner = reader.read_owner(driver, s, spec, runs, module, index, fixed)
        public = reader.flat_summary(runs, index, module, owner, common)
        need(public == c.docs[path] == read['public_summaries'][fixed['public_name']] and
             (owner['owned_count'], owner['public_count']) == (22, 22),
             'original AA public owner/count/six-receipt binding differs')
        bindings[module] = driver.acceptance_binding(s, AA, module)
    return runs[1][0], runs[1][1], bindings

def prepare(c):
    driver, s = c.driver, c.s
    git, evidence = s.d.original_git_state(REPO), tree_inventory(c)
    need(value_fp(git) == c.docs[READ]['current_dirty_Git_state'], 'original AA dirty Git identity differs')
    need({commit: {'entry_count': len(tree), **value_fp(tree)} for commit, tree in evidence.items()} ==
         c.docs[READ]['complete_original_AA_Y_W_U_S_Q_evidence_inventory'], 'original AA/Y/W/U/S/Q evidence trees differ')
    spec = driver.preflight(s, AA, ACCEPTED)
    need(len(spec.active) == 108 and len(spec.dependency_pins) == 107 and
         set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'AA accepted-prefix scope differs')
    later, original_context, accepted = read_originals(c, spec)
    active = s.h.closure(spec.graph, REMAINING); watch = active | set(driver.TARGETS)
    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,
         'remaining5 source/watch scope differs')
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(AB, row['path'])
        need(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and
             git_file(c.commit, row['path']) == raw and s.h.imports(raw) == row['all_imports'],
             'unrelated AB/AC source or imports changed: ' + module)
    sources, artifacts = source_inventory(c, spec.graph), artifact_inventory(c, watch)
    require_preimage(c)
    graph, installed = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: spec.graph[m] for m in active} and
         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live AA graph differs')
    need(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
         all(value is None for path, value in artifacts[TARGET].items() if path != SETUP), 'failed artifacts are not setup only')
    for module in REMAINING:
        need(not os.path.lexists(normal_path(module)), 'remaining owner already has a AA normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    need(original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING) and
         all(artifacts[m] == fp for m, fp in original_context['preserved_dependency_artifacts'].items()) and
         all(original_context[k] == value for k, value in driver.environment(s, spec.review).items()),
         'original AA source/dependency/runtime context differs')
    metadata = c.docs[DIAGNOSTICS]
    failure = metadata['failures'][TARGET]
    need(metadata['source_commit'] == AA and set(metadata['failures']) == {TARGET} and
         set(metadata['accepted_owners']) == set(ACCEPTED) and failure['source'] == {'path': str(PROJECT / SOURCE), **BEFORE} and
         failure['artifact_slots'][str(PROJECT / SETUP)] == {'path': str(PROJECT / SETUP), **SETUP_FP},
         'actual AA failure metadata/source/setup scope differs')
    expected_normal = OLD_ROOT / AA / TARGET / 'normal' / TARGET / 'attempt-00000/normal-command.json'
    need(failure['normal_metadata']['path'] == str(expected_normal) and
         file_fp(c, expected_normal) == pin(failure['normal_metadata']) and
         s.api.read_json(expected_normal) == failure['normal_command'], 'original failed command metadata differs')
    normal = failure['normal_command']
    normal_log = {'path': normal['log'], 'bytes': normal['log_bytes'], 'sha256': normal['log_sha256']}
    probe = c.docs[PROBE]
    need(probe['source_base_commit'] == AA and probe['exit_code'] == 0 and pin(probe['candidate']) == AFTER and
         probe['original_source'] == BEFORE and probe['whole_original_module_submitted'] is True and
         probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
         probe['original_serializer_and_guard_used'] is True and probe['lake_no_build_env_lean'] is True and
         probe['accepted_prefix_live_source_count'] == 108 and probe['accepted_prefix_dependency_count'] == 107 and
         probe['watched_source_slots'] == 360 and probe['watched_modules'] == 160 and
         probe['watched_artifact_slots'] == 3360 and probe['AA_original_Mean_acceptance_preserved'] == ACCEPTED and
         probe['original_twelve_prior_identities_and_later_retained_receipts_preserved'] is True and
         probe['original_source_and_failed_setup_preserved'] is True and
         probe['all_original_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved'] is True and
         probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False,
         'whole-module no-output probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    # These two exact mutable paths have separate preimage/archive/install checks.
    # All other frozen AA inputs remain byte-for-byte fixed through the operation.
    mutable = {str(PROJECT / SOURCE), str(PROJECT / SETUP)}
    extras = {**FAILED_PROBE_RETAINED,
        **{p: fp for p, fp in c.reader.PINNED['extra_pins'].items() if p not in mutable},
        str(expected_normal): pin(failure['normal_metadata']),
        normal_log['path']: pin(normal_log), str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_SYNTHESIS_PROBE_RESULT.json'): PINS[PROBE]}
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
         all(file_fp(c, path) == fp for path, fp in state.retained.items()), 'original AA/Y/W/U/S/Q/retained evidence changed')
    need(c.driver.snapshot(c.s, state.spec) == state.spec.baseline and
         {m: c.driver.acceptance_binding(c.s, AA, m) for m in ACCEPTED} == state.accepted and
         c.s.d.original_git_state(REPO) == state.git and
         all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'accepted AA context/runtime/Git changed')

def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'source_slots': state.sources, 'artifact_slots': state.artifacts, 'original_AA_Y_W_U_S_Q_evidence': state.evidence,
        'retained_inputs': state.retained, 'accepted_AA_bindings': state.accepted,
        'accepted_prefix_context': state.spec.baseline, 'original_AA_context': state.context,
        'Git_before': state.git, 'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = archive_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, archived=True)
    fresh = driver.preflight(s, AA, REMAINING)
    need(fresh.active == state.active and fresh.graph == state.spec.graph and fresh.sources == state.spec.sources and
         fresh.order == REMAINING and len(fresh.dependency_pins) == 152 and
         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
             fresh.dependency_pins[m] == state.artifacts[m] for m in ACCEPTED) and
         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and
         len(fresh.supplier_evidence) == 25, 'unchanged AA five-target preflight differs')
    unchanged(c, state, archived=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_AA_PREFLIGHT.json', {'source_commit': AA, 'targets': fresh.order,
        'active_source_count': 157, 'preserved_dependency_count': 152,
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require_preimage(c)
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    backup = run / 'backups' / SOURCE
    need(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True and
         file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
         (PROJECT / SOURCE).read_bytes() == c.after, 'exact single SharpPrimeSynthesis installation/backup differs')
    post = copy.copy(fresh); post.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline); expected['selected_live_sources'][TARGET] = AFTER['sha256']
    need(driver.snapshot(s, post) == expected, 'post-install dependency/runtime context differs')
    unchanged(c, state, archived=True, installed=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: fresh.graph[m] for m in fresh.active} and
         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', {'status': 'EXACT_SINGLE_SYNTHESIS_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'identity': c.identity, 'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_AA_five_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,
        'active_source_count': 157, 'preserved_dependency_count': 152,
        'Mean_AA_and_all_twelve_earlier_prior_acceptances_preserved': True,
        'original_AA_Y_W_U_S_Q_evidence_other_artifacts_runtime_and_Git_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False})

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-commit', required=True, help='updater publication AC')
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--apply', action='store_true')
    p.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = p.parse_args(); c = load(args.source_commit)
    if args.check:
        need(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_SYNTHESIS_PREFLIGHT_ONLY', 'identity': c.identity,
            'accepted_AA_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 108, 'accepted_prefix_dependencies': 107,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_AA_five_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        need(run.is_absolute() and run.resolve() == run and run.parent == runs and
             re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected SharpPrimeSynthesis worker path')
        try:
            apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_SYNTHESIS_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
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
             'serialized SharpPrimeSynthesis repair held; inspect private failure evidence')
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
        print(json.dumps({'status': 'EXACT_SINGLE_SYNTHESIS_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)

