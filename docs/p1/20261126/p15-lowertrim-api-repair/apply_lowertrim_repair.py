#!/usr/bin/env python3
"""Install one proof-only LowerTrimPaid repair under the original AC gates.

Synthesis keeps its original AC acceptance and same-AC reuse. All older owners retain
AA/Y/W/U/S/Q or their earlier identities. Only the failed setup and source may change.
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
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AC_ANCHOR = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
FAILED_JOB = 'job_a108c4d7e2594e1fb5a674382db6600f'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OLD_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-lowertrim-api-repair-v1')
SCRIPT = 'docs/p1/20261126/p15-lowertrim-api-repair/apply_lowertrim_repair.py'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 278990, 'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'}
MANIFEST_FP = {'bytes': 362316, 'sha256': 'b56ca98e7c46d9e6ab9244b2fe32f15717db95a325a0ca5e52ee965d900f44c9'}
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
ACCEPTED = [SYNTHESIS]
TARGET = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
SOURCE = 'ImbalancedChen/P5OriginalSingletonLowerTrimPaid.lean'
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.setup.json'
ARCHIVE_NAME = 'P5OriginalSingletonLowerTrimPaid.setup.json'
BEFORE = {'bytes': 14601, 'sha256': '82cfc7b75510076d0ded95130504639cde2ee39d38cff4133964a092d5cbcf54'}
AFTER = {'bytes': 14655, 'sha256': 'f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106'}
SETUP_FP = {'bytes': 6418102, 'sha256': '52a798bfd6ca48dbc188b265337d85a0cc50380481227a416514480adf048f2f'}
PREFIX = 'docs/p1/20261126/p15-lowertrim-first-compile-repair/'
REPAIR, PROBE = PREFIX + 'REPAIR_CANDIDATE.json', PREFIX + 'ACTUAL_LOWERTRIM_PROBE_RESULT.json'
DIAGNOSTICS, READ = PREFIX + 'ACTUAL_AC_METADATA.json', PREFIX + 'ACTUAL_AC_ACCEPTANCE_READ.json'
COLLECTOR = PREFIX + 'collect_ac_acceptance.py'
PUBLIC_SYNTHESIS = 'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json'
REMAINING = [TARGET,
    'ImbalancedChen.P1OriginalSingletonAtlasTrim', 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']

# Exact AD publication, six raw inputs and actual successful probe identity.
INPUTS = {'repair_source_commit': 'e91af3a5c407bdeea243af7dd3c4248949d83e9b',
 'probe_job': 'job_abfb9ce81e7749c290d6f61c385aa749',
 'after': {'bytes': 14655, 'sha256': 'f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106'},
 'document_pins': {'docs/p1/20261126/p15-lowertrim-first-compile-repair/REPAIR_CANDIDATE.json': {'bytes': 1596,
                                                                                                 'sha256': '45592035ce29e584e6b4783163e93edbb70d6495a1e0b94e46a06c8c7fb33d73'},
                   'docs/p1/20261126/p15-lowertrim-first-compile-repair/ACTUAL_LOWERTRIM_PROBE_RESULT.json': {'bytes': 2221,
                                                                                                              'sha256': '4693fdd4efc7e5b5dbc96dfb4f660d81c0dfed4247c5c1225f0ab9c4d9ebab3b'},
                   'docs/p1/20261126/p15-lowertrim-first-compile-repair/ACTUAL_AC_METADATA.json': {'bytes': 15785,
                                                                                                   'sha256': '5103c9d5d04a3c37c68e0bff7043f6ad8d9d8727bf12cd44c1c2dd6c9a7124d2'},
                   'docs/p1/20261126/p15-lowertrim-first-compile-repair/ACTUAL_AC_ACCEPTANCE_READ.json': {'bytes': 37703,
                                                                                                          'sha256': 'be82048b4039cc6e0368528c01972a85c9d4ae11a0e40e0c77f471eade1a80fa'},
                   'docs/p1/20261126/p15-lowertrim-first-compile-repair/collect_ac_acceptance.py': {'bytes': 33648,
                                                                                                    'sha256': '4136dc7723c040c92bf276e28020bece2851b6baa1317b56d8b7a431dea20660'},
                   'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json': {'bytes': 11788,
                                                                                                          'sha256': '1f2c0a0c1c00f3ac76eb2d0255ff480581438d624129f673b9f4e4e194ae37d7'}}}
AD = INPUTS['repair_source_commit'] if isinstance(INPUTS, dict) else None
PINS = INPUTS['document_pins'] if isinstance(INPUTS, dict) else {}
PROBE_JOB = INPUTS['probe_job'] if isinstance(INPUTS, dict) else None


INHERITED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                        'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                        'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                       'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                     'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 539949,
                                                                                                                                                             'sha256': '1f0815dbb5409e66f4b890eed13a3ad3ebd919130c5544aee37adf3da3d50bbd'}}

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
    return OLD_ROOT / AC / module / 'normal' / module / 'NORMAL_PASS.json'

def require_preimage(c):
    path = PROJECT / SOURCE
    need(path.resolve() == path and file_fp(c, path) == BEFORE and path.read_bytes() == c.before,
         'LowerTrimPaid source is not the exact AC preimage; source_after is held')

def archive_binding(c, receipt):
    run = receipt.parent
    need(run.parent == ROOT / c.commit / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
         receipt.resolve() == receipt, 'archive receipt is outside this LowerTrimPaid/AE repair')
    record = c.s.api.read_json(receipt)
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    need(record['status'] == 'EXACT_FAILED_SETUP_ARCHIVED_FSYNC_VERIFIED' and
         record['identity'] == c.identity and record['active_path'] == str(PROJECT / SETUP) and
         record['archive_path'] == str(archive) and record['fingerprint'] == SETUP_FP and
         record['archive_fsync_verified'] is True and record['active_removal_planned'] is True and
         record['new_lean_acceptance'] is False and archive.resolve() == archive and
         file_fp(c, archive) == SETUP_FP, 'archive is not the exact AC/AD/AE/script-bound LowerTrimPaid setup')
    return {str(receipt): file_fp(c, receipt), str(archive): SETUP_FP}

def prior_archive(c):
    receipts = sorted((ROOT / c.commit / 'runs').glob('attempt-*/FAILED_SETUP_ARCHIVE.json'))
    need(receipts, 'missing active setup without this LowerTrimPaid/AE archive receipt')
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
    need(path.resolve() == path and path.is_file() and not path.is_symlink(), 'LowerTrimPaid setup is not the fixed regular path')
    original, raw = path.stat(), path.read_bytes()
    need(raw_fp(raw) == SETUP_FP, 'failed LowerTrimPaid setup bytes differ')
    archive = run / 'failed-artifacts' / ARCHIVE_NAME
    archive.parent.mkdir(parents=True, exist_ok=True)
    need(archive.parent.resolve() == archive.parent, 'archive parent traverses a symlink')
    fd = os.open(archive, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'wb') as output:
        output.write(raw)
        output.flush()
        os.fsync(output.fileno())
    need(file_fp(c, archive) == SETUP_FP, 'exclusive LowerTrimPaid archive differs')
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
    need(not os.path.lexists(path), 'LowerTrimPaid setup remains active')
    return {'action': 'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED', 'bindings': bindings}

def tree_inventory(c):
    return {commit: c.reader.tree_inventory(OLD_ROOT / commit) for commit in (AC, AA, Y, W, U, S, Q)}

def load(commit):
    need(__debug__ and isinstance(INPUTS, dict) and re.fullmatch('[0-9a-f]{40}', commit) and
         isinstance(AD, str) and re.fullmatch('[0-9a-f]{40}', AD) and
         isinstance(PROBE_JOB, str) and re.fullmatch('job_[0-9a-f]{32}', PROBE_JOB),
         'actual AD/AE publications and probe identity must be frozen before any access')
    need(INPUTS['after'] == AFTER and set(PINS) == {REPAIR, PROBE, DIAGNOSTICS, READ, COLLECTOR, PUBLIC_SYNTHESIS},
         'fixed publication input set differs')
    need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit' and
         subprocess.run(['git', 'merge-base', '--is-ancestor', AD, commit], cwd=REPO).returncode == 0,
         'execution AE must descend from repair AD')
    script = Path(__file__)
    need(script.is_file() and not script.is_symlink(), 'updater is not a regular file')
    executed = script.read_bytes()
    need(executed == git_file(commit, SCRIPT), 'executed updater differs from AE publication')
    docs, raw_docs = {}, {}
    for path, expected in PINS.items():
        raw = git_file(AD, path)
        need(raw_fp(raw) == expected and git_file(commit, path) == raw, 'published AD/AE input differs: ' + path)
        raw_docs[path] = raw
        if path != COLLECTOR:
            docs[path] = json.loads(raw)
    before, after = git_file(AC, SOURCE), git_file(AD, SOURCE)
    need(raw_fp(before) == BEFORE and raw_fp(after) == AFTER and git_file(commit, SOURCE) == after,
         'canonical AC/AD/AE LowerTrimPaid source differs')
    repair = docs[REPAIR]
    need(repair['schema'] == 'p15_singleton_lower_trim_paid_one_proof_splice_candidate_v1' and
         repair['source_base_commit'] == AC and repair['source'] == SOURCE and
         repair['before'] == BEFORE and repair['after'] == AFTER and len(repair['splices']) == 1 and
         repair['original_failure_metadata'] == PINS[DIAGNOSTICS] and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['declaration_count'] == 8 and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe'] == {
             'path': str(Path(docs[PROBE]['candidate']['path']).parent / 'ACTUAL_LOWERTRIM_PROBE_RESULT.json'),
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
    raw = git_file(AC, DRIVER)
    entry = OLD_ROOT / AC / 'runs/attempt-00000/executed-driver.py'
    need(raw_fp(raw) == DRIVER_FP and entry.is_file() and not entry.is_symlink() and entry.read_bytes() == raw and
         raw_fp(git_file(AC, MANIFEST)) == MANIFEST_FP, 'original AC reader/manifest differs')
    driver = ModuleType('unchanged_AC_lowertrim_repair_reader'); driver.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, OLD_ROOT, DRIVER, AC_ANCHOR), 'original AC environment differs')
    reader = ModuleType('frozen_AC_collector_helpers'); reader.__file__ = COLLECTOR
    exec(compile(raw_docs[COLLECTOR], COLLECTOR, 'exec'), reader.__dict__)
    need((reader.AC, reader.AB, reader.AA, reader.Y, reader.W, reader.U, reader.S, reader.Q, reader.REPO, reader.PROJECT, reader.ROOT,
          reader.DRIVER_FP, reader.MANIFEST_FP) ==
         (AC, AC_ANCHOR, AA, Y, W, U, S, Q, REPO, PROJECT, OLD_ROOT, DRIVER_FP, MANIFEST_FP) and
         reader.PINNED['schema'] == 'p15_AC_fixed_actual_collection_inputs_v1' and
         reader.PINNED['runs'][1]['compiler_job'] == FAILED_JOB and
         value_fp(reader.PINNED) == docs[READ]['frozen_actual_input_binding'],
         'frozen AC collector helper identity differs')
    identity = {'execution_commit': commit, 'script': {'path': SCRIPT, **raw_fp(executed)},
        'repair_source_commit': AD, 'failed_source_commit': AC, 'failed_job': FAILED_JOB,
        'module': TARGET, 'source_path': SOURCE, 'source_before': BEFORE, 'source_after': AFTER,
        'failed_setup': {'path': SETUP, **SETUP_FP}, 'published_AD_inputs': PINS}
    return SimpleNamespace(commit=commit, driver=driver, reader=reader, s=driver.helpers(), docs=docs,
        before=before, after=after, script=executed, identity=identity)

def read_originals(c, spec):
    reader, driver, s = c.reader, c.driver, c.s
    read = c.docs[READ]
    need(read['schema'] == 'p15_AC_original_accepted_prefix_read_v1' and read['source_commit'] == AC and
         read['source_anchor_commit'] == AC_ANCHOR and read['selected_owners_revalidated'] == ACCEPTED and
         read['current_read_live_source_count'] == 112 and read['current_read_preserved_dependency_count'] == 111 and
         read['normal_or_kernel_commands_executed'] == 0 and value_fp(spec.baseline) == read['current_read_snapshot'],
         'published AC accepted-prefix read differs')
    runs = [reader.read_run(driver, s, spec.graph, i, fixed) for i, fixed in enumerate(reader.PINNED['runs'])]
    need(reader.accepting_runs(runs) == {SYNTHESIS: 0} and
         [r[2] for r in runs] == read['original_runs'], 'original AC first and partial-run provenance differs')
    common = reader.identity(spec, ACCEPTED)
    bindings = {}
    for module, index, path in [(SYNTHESIS, 0, PUBLIC_SYNTHESIS)]:
        fixed = reader.PINNED['owners'][module]
        owner = reader.read_owner(driver, s, spec, runs, module, index, fixed)
        public = reader.flat_summary(runs, index, module, owner, common)
        need(public == c.docs[path] == read['public_summaries'][fixed['public_name']] and
             (owner['owned_count'], owner['public_count']) == (28, 28),
             'original AC public owner/count/six-receipt binding differs')
        bindings[module] = driver.acceptance_binding(s, AC, module)
    return runs[1][0], runs[1][1], bindings

def prepare(c):
    driver, s = c.driver, c.s
    git, evidence = s.d.original_git_state(REPO), tree_inventory(c)
    need(value_fp(git) == c.docs[READ]['current_dirty_Git_state'], 'original AC dirty Git identity differs')
    need({commit: {'entry_count': len(tree), **value_fp(tree)} for commit, tree in evidence.items()} ==
         c.docs[READ]['complete_original_AC_AA_Y_W_U_S_Q_evidence_inventory'], 'original AC/AA/Y/W/U/S/Q evidence trees differ')
    spec = driver.preflight(s, AC, ACCEPTED)
    need(len(spec.active) == 112 and len(spec.dependency_pins) == 111 and
         set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'AC accepted-prefix scope differs')
    later, original_context, accepted = read_originals(c, spec)
    active = s.h.closure(spec.graph, REMAINING); watch = active | set(driver.TARGETS)
    need(len(spec.graph) == 360 and len(active) == 157 and len(watch) == 160 and spec.active <= active,
         'remaining4 source/watch scope differs')
    for module, row in spec.manifest['project_sources'].items():
        raw = git_file(AD, row['path'])
        need(raw_fp(raw) == (AFTER if module == TARGET else pin(row)) and
             git_file(c.commit, row['path']) == raw and s.h.imports(raw) == row['all_imports'],
             'unrelated AD/AE source or imports changed: ' + module)
    sources, artifacts = source_inventory(c, spec.graph), artifact_inventory(c, watch)
    require_preimage(c)
    graph, installed = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: spec.graph[m] for m in active} and
         {m: row['sha256'] for m, row in installed.items()} == {m: spec.sources[m] for m in active}, 'live AC graph differs')
    need(len(artifacts[TARGET]) == 21 and artifacts[TARGET].get(SETUP) in (None, SETUP_FP) and
         all(value is None for path, value in artifacts[TARGET].items() if path != SETUP), 'failed artifacts are not setup only')
    for module in REMAINING:
        need(not os.path.lexists(normal_path(module)), 'remaining owner already has a AC normal receipt')
        if module != TARGET:
            driver.require_fresh_owner(module, artifacts[module])
    archives = prior_archive(c) if artifacts[TARGET][SETUP] is None else {}
    need(original_context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
         set(original_context['preserved_dependency_artifacts']) == active - set(ACCEPTED + REMAINING) and
         all(artifacts[m] == fp for m, fp in original_context['preserved_dependency_artifacts'].items()) and
         all(original_context[k] == value for k, value in driver.environment(s, spec.review).items()),
         'original AC source/dependency/runtime context differs')
    metadata = c.docs[DIAGNOSTICS]
    failure = metadata['failures'][TARGET]
    need(metadata['source_commit'] == AC and set(metadata['failures']) == {TARGET} and
         set(metadata['accepted_owners']) == set(ACCEPTED) and failure['source'] == {'path': str(PROJECT / SOURCE), **BEFORE} and
         failure['artifact_slots'][str(PROJECT / SETUP)] == {'path': str(PROJECT / SETUP), **SETUP_FP},
         'actual AC failure metadata/source/setup scope differs')
    expected_normal = OLD_ROOT / AC / TARGET / 'normal' / TARGET / 'attempt-00000/normal-command.json'
    need(failure['normal_metadata']['path'] == str(expected_normal) and
         file_fp(c, expected_normal) == pin(failure['normal_metadata']) and
         s.api.read_json(expected_normal) == failure['normal_command'], 'original failed command metadata differs')
    normal = failure['normal_command']
    normal_log = {'path': normal['log'], 'bytes': normal['log_bytes'], 'sha256': normal['log_sha256']}
    probe = c.docs[PROBE]
    need(probe['source_base_commit'] == AC and probe['exit_code'] == 0 and pin(probe['candidate']) == AFTER and
         probe['original_source'] == BEFORE and probe['whole_original_module_submitted'] is True and
         probe['Lean_typecheck_commands'] == 1 and probe['output_object_requested'] is False and
         probe['original_serializer_and_guard_used'] is True and probe['lake_no_build_env_lean'] is True and
         probe['accepted_prefix_live_source_count'] == 112 and probe['accepted_prefix_dependency_count'] == 111 and
         probe['watched_source_slots'] == 360 and probe['watched_modules'] == 160 and
         probe['watched_artifact_slots'] == 3360 and probe['AC_original_Synthesis_acceptance_preserved'] == ACCEPTED and
         probe['original_thirteen_prior_identities_and_later_retained_receipts_preserved'] is True and
         probe['original_source_and_failed_setup_preserved'] is True and
         probe['all_original_AC_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved'] is True and
         probe['existing_project_modules_rebuilt'] == [] and probe['normal_or_kernel_acceptance_claimed'] is False,
         'whole-module no-output probe differs')
    candidate, log = Path(probe['candidate']['path']), Path(probe['log']['path'])
    # These two exact mutable paths have separate preimage/archive/install checks.
    # All other frozen AC inputs remain byte-for-byte fixed through the operation.
    mutable = {str(PROJECT / SOURCE), str(PROJECT / SETUP)}
    extras = {**INHERITED_EXTRA_PINS,
        **{p: fp for p, fp in c.reader.PINNED['extra_pins'].items() if p not in mutable},
        str(expected_normal): pin(failure['normal_metadata']),
        normal_log['path']: pin(normal_log), str(candidate): AFTER, str(log): pin(probe['log']),
        str(candidate.parent / 'ACTUAL_LOWERTRIM_PROBE_RESULT.json'): PINS[PROBE]}
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
         all(file_fp(c, path) == fp for path, fp in state.retained.items()), 'original AC/AA/Y/W/U/S/Q/retained evidence changed')
    need(c.driver.snapshot(c.s, state.spec) == state.spec.baseline and
         {m: c.driver.acceptance_binding(c.s, AC, m) for m in ACCEPTED} == state.accepted and
         c.s.d.original_git_state(REPO) == state.git and
         all(not os.path.lexists(normal_path(m)) for m in REMAINING), 'accepted AC context/runtime/Git changed')

def apply_repair(c, run):
    driver, s = c.driver, c.s
    s.d.verify_lane(s.h)
    state = prepare(c)
    update = {'module': TARGET, 'path': SOURCE, 'before_sha256': BEFORE['sha256'],
              'after_sha256': AFTER['sha256'], 'cloud_source_mutation_required': True}
    s.d.save(run / 'SOURCE_REPAIR_PLAN.json', {'identity': c.identity, 'update': update,
        'source_slots': state.sources, 'artifact_slots': state.artifacts, 'original_AC_AA_Y_W_U_S_Q_evidence': state.evidence,
        'retained_inputs': state.retained, 'accepted_AC_bindings': state.accepted,
        'accepted_prefix_context': state.spec.baseline, 'original_AC_context': state.context,
        'Git_before': state.git, 'new_lean_acceptance': False})
    unchanged(c, state)
    preservation = archive_setup(c, state, run)
    state.retained.update(preservation['bindings'])
    unchanged(c, state, archived=True)
    fresh = driver.preflight(s, AC, REMAINING)
    need(fresh.active == state.active and fresh.graph == state.spec.graph and fresh.sources == state.spec.sources and
         fresh.order == REMAINING and len(fresh.dependency_pins) == 153 and
         set(fresh.initial_owners) == set(ACCEPTED + REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'MISSING_WITHOUT_NORMAL_RECEIPT' for m in REMAINING) and
         all(fresh.initial_owners[m]['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT' and
             fresh.dependency_pins[m] == state.artifacts[m] for m in ACCEPTED) and
         fresh.supplier_evidence == state.later['original_supplier_acceptance_bindings'] and
         len(fresh.supplier_evidence) == 26, 'unchanged AC four-target preflight differs')
    unchanged(c, state, archived=True)
    s.d.save(run / 'UNCHANGED_ORIGINAL_AC_PREFLIGHT.json', {'source_commit': AC, 'targets': fresh.order,
        'active_source_count': 157, 'preserved_dependency_count': 153,
        'initial_owner_status': {m: row['status'] for m, row in fresh.initial_owners.items()},
        'context': fresh.baseline, 'normal_or_kernel_executed': False})
    s.d.save(run / 'FAILED_SETUP_MOVE.json', preservation)
    require_preimage(c)
    records = s.h.install_sources(PROJECT, [update], {SOURCE: c.after}, run / 'backups')
    backup = run / 'backups' / SOURCE
    need(len(records) == 1 and records[0]['module'] == TARGET and records[0]['mutated'] is True and
         file_fp(c, backup) == BEFORE and backup.read_bytes() == c.before and
         (PROJECT / SOURCE).read_bytes() == c.after, 'exact single LowerTrimPaid installation/backup differs')
    post = copy.copy(fresh); post.sources = {**fresh.sources, TARGET: AFTER['sha256']}
    expected = copy.deepcopy(fresh.baseline); expected['selected_live_sources'][TARGET] = AFTER['sha256']
    need(driver.snapshot(s, post) == expected, 'post-install dependency/runtime context differs')
    unchanged(c, state, archived=True, installed=True)
    graph, sources = s.h.project_graph(PROJECT, REMAINING)
    need(graph == {m: fresh.graph[m] for m in fresh.active} and
         {m: row['sha256'] for m, row in sources.items()} == {m: post.sources[m] for m in fresh.active}, 'post-install graph differs')
    s.d.save(run / 'SOURCE_REPAIR_RESULT.json', {'status': 'EXACT_SINGLE_LOWERTRIM_SOURCE_REPAIR_VERIFIED_NOT_COMPILED',
        'identity': c.identity, 'repair_records': records, 'failed_setup_preservation': preservation,
        'source_backup': {'path': str(backup), **BEFORE}, 'context_after': expected,
        'original_AC_four_target_preflight_passed_with_preimage': True,
        'published_source_count': 360, 'other_source_slots_preserved': 359, 'watched_module_count': 160,
        'active_source_count': 157, 'preserved_dependency_count': 153,
        'Synthesis_AC_and_all_thirteen_earlier_prior_acceptances_preserved': True,
        'original_AC_AA_Y_W_U_S_Q_evidence_other_artifacts_runtime_and_Git_unchanged': True,
        'normal_or_kernel_executed': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False})

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-commit', required=True, help='updater publication AE')
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--apply', action='store_true')
    p.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = p.parse_args(); c = load(args.source_commit)
    if args.check:
        need(args.inside_lane is None, 'read-only check does not use a lane')
        state = prepare(c)
        print(json.dumps({'status': 'EXACT_SINGLE_LOWERTRIM_PREFLIGHT_ONLY', 'identity': c.identity,
            'accepted_AC_owners_revalidated': ACCEPTED, 'accepted_prefix_sources': 112, 'accepted_prefix_dependencies': 111,
            'active_source_count': 157, 'watched_module_count': 160,
            'setup_archive_required': state.artifacts[TARGET][SETUP] is not None,
            'original_AC_four_target_preflight_performed': False,
            'source_or_artifact_mutations': 0, 'new_lean_acceptance': False}), flush=True)
        return 0
    runs = ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        need(run.is_absolute() and run.resolve() == run and run.parent == runs and
             re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected LowerTrimPaid worker path')
        try:
            apply_repair(c, run)
        except Exception as error:
            c.s.d.save(run / 'SOURCE_REPAIR_FAILURE.json', {'identity': c.identity,
                'error_type': type(error).__name__, 'error': str(error), 'new_lean_acceptance': False})
            return 1
        c.s.ops.emit('EXACT_SINGLE_LOWERTRIM_SOURCE_REPAIR_VERIFIED', source_commit=c.commit,
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
             'serialized LowerTrimPaid repair held; inspect private failure evidence')
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
        print(json.dumps({'status': 'EXACT_SINGLE_LOWERTRIM_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_lean_acceptance': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)

