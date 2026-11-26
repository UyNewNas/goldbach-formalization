#!/usr/bin/env python3
"""Typecheck the five-splice SmoothLicence repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
T = '999510c460e6e026c8cabe46c5f35876f7201f8e'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-smooth-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 152370, 'sha256': '9d9c2e467b3fd6271b7b0101812094ca6ff768f1ea831812b6de4c95a0dd9c7a'}
MANIFEST_FP = {'bytes': 349643, 'sha256': 'ae3f6bb915e0ed2dc799fd6bfed2b906aab3efac3df9186c9c1d54da4b53a1af'}
TARGET = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
ALLGROUP = 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'
ACCEPTED = [WORD, ALLGROUP]
BEFORE = {'bytes': 4358, 'sha256': 'f74c3c51c0b1de7b493f9fe7e883d89a4b5c163624bb5be1f6901fbec3424011'}
AFTER = {'bytes': 4739, 'sha256': 'f82bb240dc2bc7172b6f9978dadb1b166ed9be1905167c813c088bd2c09f14e4'}
SETUP = '.lake/build/ir/ImbalancedChen/P1OriginalSingletonSmoothLicence.setup.json'
SETUP_FP = {'bytes': 6423922, 'sha256': '963197a94a0370d47ee383bb103770b7af29e692df06b8195d72906e1cc0fff7'}
ACCEPTED_SOURCE_PINS = {'ImbalancedChen.P5IndependentPrimeSourceWordDictionary': {'bytes': 5672,
                                                           'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'},
 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy': {'bytes': 9345,
                                                         'sha256': '089dac23d8ce96fde4f5fcb129c3b525955a919d7665937821a5ee31d11ab8be'}}

ORIGINAL_RUN_SUMMARIES = [{'accepted_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
  'all_selected_owners_accepted': True,
  'failures': {},
  'reused_complete_selected_owners': [],
  'source_commit': '2779eb7b2b0433bea10d523ef976317893f8429d',
  'targets': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
  'worker_exit_code': 0},
 {'accepted_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
                      'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'],
  'all_selected_owners_accepted': False,
  'failures': {'ImbalancedChen.P1OriginalSingletonSmoothLicence': 'normal failed/scope differs: '
                                                                  'ImbalancedChen.P1OriginalSingletonSmoothLicence'},
  'reused_complete_selected_owners': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary'],
  'source_commit': '2779eb7b2b0433bea10d523ef976317893f8429d',
  'targets': ['ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
              'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
              'ImbalancedChen.P1OriginalSingletonSmoothLicence',
              'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
              'ImbalancedChen.P5PrimeDivisorMeanCorrection',
              'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
              'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
              'ImbalancedChen.P1OriginalSingletonAtlasTrim',
              'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'worker_exit_code': 1}]

RETAINED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-word-api-repair-v1/2779eb7b2b0433bea10d523ef976317893f8429d/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 497566,
                                                                                                                                                        'sha256': 'c55080bf18d46c0612ef805a8b1c5915fbb65cadbcc6763f683598e69b579e47'}}

RUN_PINS = {'attempt-00000': {'CONTEXT_AFTER.json': {'bytes': 271784,
                                          'sha256': '7022d734b1650644e56e48e06563ea5b04cb2d08accb53170d9af06ac25dcbb3'},
                   'CONTEXT_BEFORE.json': {'bytes': 271784,
                                           'sha256': '7022d734b1650644e56e48e06563ea5b04cb2d08accb53170d9af06ac25dcbb3'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 40734,
                                   'sha256': '2e35df4747d247f46509520b5c749e06c8c55156433d8343a1c784e7f4d90ee1'},
                   'WORKER_RESULT.json': {'bytes': 40669,
                                          'sha256': 'a30618e83784765df9b6522f36d6193356c7d03c694ff94baf82595777c8cffb'}},
 'attempt-00001': {'CONTEXT_AFTER.json': {'bytes': 483194,
                                          'sha256': '5721f6257fe6090b63584ebb1bfa496e6c5822eb09bd529a3ffba0a4e35f1e20'},
                   'CONTEXT_BEFORE.json': {'bytes': 483194,
                                           'sha256': '5721f6257fe6090b63584ebb1bfa496e6c5822eb09bd529a3ffba0a4e35f1e20'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 52560,
                                   'sha256': '02c712e2179b51dd6ba1e73ca3398250ed7070f14714b5312365c29b20386af3'},
                   'WORKER_RESULT.json': {'bytes': 52444,
                                          'sha256': 'f21cfc35c5796567e4a229561bb46dc3350ee3f8c60335583cf7f28c001f8317'}}}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def fp(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    require(path.is_file() and not path.is_symlink(), 'nonregular observed file: ' + str(path))
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size,
                'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def evidence_trees():
    trees = {}
    for commit in (U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees


def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', U + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / U / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original U driver/manifest differs')
    d = ModuleType('unchanged_U_smooth_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT, d.RUNNER, d.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, T), 'U reader environment differs')
    s = d.helpers()
    originals = {}
    for index, (attempt, pins) in enumerate(RUN_PINS.items()):
        folder = ROOT / U / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original U run evidence differs')
        require(fp(folder / 'executed-driver.py') == DRIVER_FP, 'executed U reader differs')
        result, worker = [s.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        summary = ORIGINAL_RUN_SUMMARIES[index]
        require(all(result.get(key) == value for key, value in summary.items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original U RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original U context pair differs')
        originals[attempt] = result
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == [WORD] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:3] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [WORD] and set(later['failures']) == {TARGET} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original U first success/later partial scopes differ')
    spec = d.preflight(s, U, ACCEPTED)
    require(len(spec.active) == 139 and len(spec.dependency_pins) == 137 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'accepted-prefix scope differs')
    accepted_bindings, accepted_counts = {}, {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, U, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, U, module)
        require(binding == later['acceptance_bindings'][module] and
                fp(PROJECT / s.h.module_path(module)) == ACCEPTED_SOURCE_PINS[module],
                'complete original U accepted binding/source differs')
        require(len(binding['audits']) == 1, 'original U owner audit count differs')
        audit = s.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == {'owned_count': 15, 'public_count': 15}, 'original U owner export counts differ')
        accepted_bindings[module], accepted_counts[module] = binding, counts
    require(accepted_bindings[WORD] == first['acceptance_bindings'][WORD], 'Word first U acceptance differs from later reuse')
    source = PROJECT / s.h.module_path(TARGET)
    require(fp(source) == BEFORE and d.git_file(U, s.h.module_path(TARGET)) == source.read_bytes(),
            'SmoothLicence original source differs')
    active = s.h.closure(spec.graph, later['targets'])
    watch = active | set(d.TARGETS)
    require(len(active) == 157 and len(watch) == 160 and len(spec.graph) == 360, 'source/watch scope differs')

    def sources():
        return {module: fp(PROJECT / s.h.module_path(module)) for module in sorted(spec.graph)}

    def artifacts():
        return {module: d.module_artifacts(s, module) for module in sorted(watch)}

    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence_trees()
    before_git = s.d.original_git_state(REPO)
    require(len(before_artifacts[TARGET]) == 21 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(value is None for path, value in before_artifacts[TARGET].items() if path != SETUP),
            'SmoothLicence failed artifacts differ')
    require(all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
            'original Word installation receipt differs')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, U, module) == binding for module, binding in accepted_bindings.items()) and
                all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
                'project/runtime/original acceptance changed during probe')

    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / U / 'runs')
    probe = run_dir / 'OriginalSingletonSmoothLicenceProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = s.ops.run(run_dir, 'serialized-whole-smooth-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_SmoothLicence_actual_whole_module_api_probe_v1', 'source_base_commit': U,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'failed_setup': {'path': str(PROJECT / SETUP), **SETUP_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'U_original_Word_AllGroup_acceptances_preserved': ACCEPTED, 'original_accepted_counts': accepted_counts,
        'accepted_prefix_live_source_count': 139, 'accepted_prefix_dependency_count': 137,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_source_and_failed_setup_preserved': True,
        'all_original_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_SMOOTH_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'SMOOTH_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_SMOOTH_PROBE_RESULT.json'), **result}), flush=True)
    return outcome['exit_code']


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    args = parser.parse_args()
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
        'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(run(args.candidate))
    except Exception as error:
        print(json.dumps({'status': 'SMOOTH_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
