#!/usr/bin/env python3
"""Typecheck the one-splice ReserveBranches repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-reservebranches-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
TARGET = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ATLASTRIM = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
ACCEPTED = [LOWERTRIM, ATLASTRIM]
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.setup.json'

DRIVER_FP = {'bytes': 306454, 'sha256': '2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e'}

MANIFEST_FP = {'bytes': 364863, 'sha256': '6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5'}

BEFORE = {'bytes': 8183, 'sha256': '8b8987b5208aa0ed201adeb84a03076119519ff2880fb442175de2385b3ad049'}

AFTER = {'bytes': 8197, 'sha256': 'd5945aa39ab54bc5c4aeb529a96299e7ab3bcf0c4fcb946296d3a697753a2bb7'}

SETUP_FP = {'bytes': 6425657, 'sha256': '9f9cf6315445e223e6a920e5e686e21a86d9a4a4ee26729f7740bf8fafcee3e3'}

ACCEPTED_SOURCE_PINS = {'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': {'bytes': 14655,
                                                     'sha256': 'f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106'},
 'ImbalancedChen.P1OriginalSingletonAtlasTrim': {'bytes': 8493,
                                                 'sha256': '82d283e23ed857c134b9bd628a6711c24df8432796f55d7fb2a1a2a16d9f252a'}}

RUN_PINS = {'attempt-00000': {'RESULT.json': {'bytes': 13666,
                                   'sha256': 'b15f809241e1a6d9e47294ca4b92fcea0ed77a16c7e2da1b9396926ca9491243'},
                   'WORKER_RESULT.json': {'bytes': 13601,
                                          'sha256': '918fb5a375a6624c792a6fbe573250f3daa414da8f52eabdcd17e855b6cb9f4a'},
                   'CONTEXT_BEFORE.json': {'bytes': 350763,
                                           'sha256': '9d74828ab53a3ad56d011c8d0b50e9cf6634be33bcb937979f41282c20aaba6c'},
                   'CONTEXT_AFTER.json': {'bytes': 350763,
                                          'sha256': '9d74828ab53a3ad56d011c8d0b50e9cf6634be33bcb937979f41282c20aaba6c'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
 'attempt-00001': {'RESULT.json': {'bytes': 62238,
                                   'sha256': '62f3e218a0eb3266eb06327692e4b5f1a86e236c51ca9b2957b688cd29e4a460'},
                   'WORKER_RESULT.json': {'bytes': 62122,
                                          'sha256': '933a47c3c87403b85b7506425406cb9878f2aa9334c5d9151b808701323fe8c5'},
                   'CONTEXT_BEFORE.json': {'bytes': 533346,
                                           'sha256': '0d8d8eb6b587dafa0f8af6d7cf113af19bae6860cef16e64b5095c9408f5ff63'},
                   'CONTEXT_AFTER.json': {'bytes': 533346,
                                          'sha256': '0d8d8eb6b587dafa0f8af6d7cf113af19bae6860cef16e64b5095c9408f5ff63'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}}}

ORIGINAL_RUN_SUMMARIES = [{'source_commit': 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2',
  'targets': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
  'accepted_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
  'failures': {},
  'reused_complete_selected_owners': [],
  'worker_exit_code': 0,
  'all_selected_owners_accepted': True},
 {'source_commit': 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2',
  'targets': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
              'ImbalancedChen.P1OriginalSingletonAtlasTrim',
              'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'accepted_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
                      'ImbalancedChen.P1OriginalSingletonAtlasTrim'],
  'failures': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': 'normal failed/scope differs: '
                                                                     'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'},
  'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalSingletonLowerTrimPaid'],
  'worker_exit_code': 1,
  'all_selected_owners_accepted': False}]

RETAINED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                        'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                        'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                       'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                     'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-repair-v1/9f2013ad9cb9caac9cec03cb213d9949c4443c65/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 539949,
                                                                                                                                                             'sha256': '1f0815dbb5409e66f4b890eed13a3ad3ebd919130c5544aee37adf3da3d50bbd'},
 '/workspace/p1-complete-proof/20261126-p15-lowertrim-api-repair-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 549208,
                                                                                                                                                             'sha256': '73cf0272db2e0e33c40462de795e6dc97c0c7b6ae4703b96fb0c94e1d4f31b03'}}


ACCEPTED_COUNTS = {'ImbalancedChen.P1OriginalSingletonAtlasTrim': {'owned_count': 11, 'public_count': 9},
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': {'owned_count': 10, 'public_count': 10}}
ACCEPTED_FIRST_RUN = {'ImbalancedChen.P1OriginalSingletonAtlasTrim': 1, 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': 0}

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
    for commit in (AE, AC, AA, Y, W, U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original AE/AC/AA/Y/W/U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees

def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AE + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / AE / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original AE driver/manifest differs')
    d = ModuleType('unchanged_AE_reservebranches_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT, d.RUNNER, d.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, AD), 'AE reader environment differs')
    s = d.helpers()
    originals = {}
    for index, (attempt, pins) in enumerate(RUN_PINS.items()):
        folder = ROOT / AE / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original AE run evidence differs')
        require(fp(folder / 'executed-driver.py') == DRIVER_FP, 'executed AE reader differs')
        result, worker = [s.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        summary = ORIGINAL_RUN_SUMMARIES[index]
        require(all(result.get(key) == value for key, value in summary.items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original AE RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original AE context pair differs')
        originals[attempt] = result
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == [LOWERTRIM] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:3] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [LOWERTRIM] and set(later['failures']) == {TARGET} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original AE first success/later partial scopes differ')
    spec = d.preflight(s, AE, ACCEPTED)
    require(len(spec.active) == 153 and len(spec.dependency_pins) == 151 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'accepted-prefix scope differs')
    require(len(spec.manifest['previously_accepted_targets']) == 14 and
            spec.manifest['previously_accepted_targets'] == d.PREVIOUSLY_ACCEPTED_TARGETS,
            'original fourteen prior identities differ')
    accepted_bindings, accepted_counts = {}, {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, AE, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, AE, module)
        require(binding == later['acceptance_bindings'][module] and
                fp(PROJECT / s.h.module_path(module)) == ACCEPTED_SOURCE_PINS[module],
                'complete original AE accepted binding/source differs')
        require(len(binding['audits']) == 1, 'original AE owner audit count differs')
        audit = s.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == ACCEPTED_COUNTS[module], 'original AE owner export counts differ')
        accepted_bindings[module], accepted_counts[module] = binding, counts
    for module, index in ACCEPTED_FIRST_RUN.items():
        original = originals['attempt-' + str(index).zfill(5)]
        require(accepted_bindings[module] == original['acceptance_bindings'][module],
                'original AE first-accepting-run owner identity differs')
    prefix_suppliers = spec.active & (set(spec.manifest['previously_accepted_targets']) |
                                     set(spec.manifest['accepted_suppliers']))
    require(len(prefix_suppliers) == 25 and spec.supplier_evidence ==
            {module: later['original_supplier_acceptance_bindings'][module] for module in prefix_suppliers} and
            all(spec.supplier_evidence.get(module) == binding
                for module, binding in first['original_supplier_acceptance_bindings'].items()),
            'original AE accepted-prefix supplier bindings differ')
    source = PROJECT / s.h.module_path(TARGET)
    require(fp(source) == BEFORE and d.git_file(AE, s.h.module_path(TARGET)) == source.read_bytes(),
            'ReserveBranches original source differs')
    active = s.h.closure(spec.graph, later['targets'])
    watch = active | set(d.TARGETS)
    require(len(active) == 157 and len(watch) == 160 and len(spec.graph) == 360, 'source/watch scope differs')

    def sources():
        return {module: fp(PROJECT / s.h.module_path(module)) for module in sorted(spec.graph)}

    def artifacts():
        return {module: d.module_artifacts(s, module) for module in sorted(watch)}

    later_context = s.api.read_json(ROOT / AE / 'runs/attempt-00001/CONTEXT_BEFORE.json')
    retained_prior_inputs = later_context['retained_original_evidence']
    require(all(fp(path) == expected for path, expected in retained_prior_inputs.items()),
            'original later-context prior receipts differ')
    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence_trees()
    before_git = s.d.original_git_state(REPO)
    require(sum(len(rows) for rows in before_artifacts.values()) == 3360,
            'original 160-module artifact inventory differs')
    require(len(before_artifacts[TARGET]) == 21 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(value is None for path, value in before_artifacts[TARGET].items() if path != SETUP),
            'ReserveBranches failed artifacts differ')
    require(all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
            'retained earlier installation/probe receipts differ')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, AE, module) == binding for module, binding in accepted_bindings.items()) and
                all(fp(path) == expected for path, expected in retained_prior_inputs.items()) and
                all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
                'project/runtime/original acceptance changed during probe')

    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / AE / 'runs')
    probe = run_dir / 'OriginalPrimeAtlasReserveBranchesProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = s.ops.run(run_dir, 'serialized-whole-reservebranches-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_OriginalPrimeAtlasReserveBranches_actual_whole_module_api_probe_v1', 'source_base_commit': AE,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'failed_setup': {'path': str(PROJECT / SETUP), **SETUP_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'AE_original_LowerTrim_and_AtlasTrim_acceptance_preserved': ACCEPTED, 'original_accepted_counts': accepted_counts,
        'accepted_prefix_live_source_count': 153, 'accepted_prefix_dependency_count': 151,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_fourteen_prior_identities_and_later_retained_receipts_preserved': True,
        'original_source_and_failed_setup_preserved': True,
        'all_original_AE_AC_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_RESERVEBRANCHES_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'RESERVEBRANCHES_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_RESERVEBRANCHES_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'RESERVEBRANCHES_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
