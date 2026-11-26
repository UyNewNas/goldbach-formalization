#!/usr/bin/env python3
"""Typecheck the two-splice EndpointLogPayment repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
V = 'f23c4f3308b471350064bf0d6ad1bdb0fce0d6fb'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-endpoint-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
TARGET = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
SMOOTH = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
ACCEPTED = [SMOOTH]
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalPrimeEndpointLogPayment.setup.json'
DRIVER_FP = {'bytes': 194954, 'sha256': '2d53b4d52e3e9a9c8fa5a4853837993dfcfe47aa47f8577f776b59e2ac6ab52f'}

MANIFEST_FP = {'bytes': 354491, 'sha256': '0a8d1e86f3783bf264eee4d23bc219834537a0ded653aa035eda4e5874c8d41d'}

BEFORE = {'bytes': 13623, 'sha256': '73c45c9e3418847e4a2e2a685429ff3a44053fff055f99bc91460da59d23364a'}

AFTER = {'bytes': 13668, 'sha256': '1a9baa44f798fba58671d473f3be4def2eaefd6c758413e0f7d60b3238edef3c'}

SETUP_FP = {'bytes': 6416695, 'sha256': 'fb564ed695e8eefdf9bf6fa1b1607e65ee5eba7d6abad6fa468861f93ae46553'}

ACCEPTED_SOURCE_PINS = {'ImbalancedChen.P1OriginalSingletonSmoothLicence': {'bytes': 4739,
                                                     'sha256': 'f82bb240dc2bc7172b6f9978dadb1b166ed9be1905167c813c088bd2c09f14e4'}}

RUN_PINS = {'attempt-00000': {'RESULT.json': {'bytes': 27971,
                                   'sha256': '32990e4d664b35e87e640e589bc055709fac04ff44521351144639cc42fb08f5'},
                   'WORKER_RESULT.json': {'bytes': 27906,
                                          'sha256': 'e661a87f62c6a35e2b18e44d98230ae024768babd0b77b34ad41b06901b7678b'},
                   'CONTEXT_BEFORE.json': {'bytes': 390652,
                                           'sha256': 'caa347a83b0700d6a3d664b012b562937690cfa8f049671805894dfbcff87426'},
                   'CONTEXT_AFTER.json': {'bytes': 390652,
                                          'sha256': 'caa347a83b0700d6a3d664b012b562937690cfa8f049671805894dfbcff87426'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}},
 'attempt-00001': {'RESULT.json': {'bytes': 49090,
                                   'sha256': '187e363dd2f6293bf473197ef4066b2fdeb321028b3edeb876071632d47db42f'},
                   'WORKER_RESULT.json': {'bytes': 48974,
                                          'sha256': 'f0acf4caf66f35897dd091265bcda2e18549936b864f6a4c95e3dc674275175c'},
                   'CONTEXT_BEFORE.json': {'bytes': 497329,
                                           'sha256': '657059bb2a4759b9f7aa9e8a3591d1f51b89488f1f614f0746499292211ec2a0'},
                   'CONTEXT_AFTER.json': {'bytes': 497329,
                                          'sha256': '657059bb2a4759b9f7aa9e8a3591d1f51b89488f1f614f0746499292211ec2a0'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'}}}

ORIGINAL_RUN_SUMMARIES = [{'source_commit': '6484b348b82d8ca6221262bb53f255fa92e9adc8',
  'targets': ['ImbalancedChen.P1OriginalSingletonSmoothLicence'],
  'accepted_owners': ['ImbalancedChen.P1OriginalSingletonSmoothLicence'],
  'failures': {},
  'reused_complete_selected_owners': [],
  'worker_exit_code': 0,
  'all_selected_owners_accepted': True},
 {'source_commit': '6484b348b82d8ca6221262bb53f255fa92e9adc8',
  'targets': ['ImbalancedChen.P1OriginalSingletonSmoothLicence',
              'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
              'ImbalancedChen.P5PrimeDivisorMeanCorrection',
              'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
              'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
              'ImbalancedChen.P1OriginalSingletonAtlasTrim',
              'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'accepted_owners': ['ImbalancedChen.P1OriginalSingletonSmoothLicence'],
  'failures': {'ImbalancedChen.P5OriginalPrimeEndpointLogPayment': 'normal failed/scope differs: '
                                                                   'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'},
  'reused_complete_selected_owners': ['ImbalancedChen.P1OriginalSingletonSmoothLicence'],
  'worker_exit_code': 1,
  'all_selected_owners_accepted': False}]

RETAINED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-smooth-api-repair-v1/6484b348b82d8ca6221262bb53f255fa92e9adc8/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 510128,
                                                                                                                                                          'sha256': '6996fa4aac6c9ca9eab9806d637c2bfc525b490db70ec18df8b61bba0ad4893c'}}


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
    for commit in (W, U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original W/U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees

def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', W + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / W / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original W driver/manifest differs')
    d = ModuleType('unchanged_W_endpoint_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT, d.RUNNER, d.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, V), 'W reader environment differs')
    s = d.helpers()
    originals = {}
    for index, (attempt, pins) in enumerate(RUN_PINS.items()):
        folder = ROOT / W / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original W run evidence differs')
        require(fp(folder / 'executed-driver.py') == DRIVER_FP, 'executed W reader differs')
        result, worker = [s.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        summary = ORIGINAL_RUN_SUMMARIES[index]
        require(all(result.get(key) == value for key, value in summary.items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original W RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original W context pair differs')
        originals[attempt] = result
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == [SMOOTH] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:2] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [SMOOTH] and set(later['failures']) == {TARGET} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original W first success/later partial scopes differ')
    spec = d.preflight(s, W, ACCEPTED)
    require(len(spec.active) == 130 and len(spec.dependency_pins) == 129 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'accepted-prefix scope differs')
    accepted_bindings, accepted_counts = {}, {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, W, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, W, module)
        require(binding == later['acceptance_bindings'][module] and
                fp(PROJECT / s.h.module_path(module)) == ACCEPTED_SOURCE_PINS[module],
                'complete original W accepted binding/source differs')
        require(len(binding['audits']) == 1, 'original W owner audit count differs')
        audit = s.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == {'owned_count': 11, 'public_count': 11}, 'original W owner export counts differ')
        accepted_bindings[module], accepted_counts[module] = binding, counts
    require(accepted_bindings[SMOOTH] == first['acceptance_bindings'][SMOOTH], 'Smooth first W acceptance differs from later reuse')
    source = PROJECT / s.h.module_path(TARGET)
    require(fp(source) == BEFORE and d.git_file(W, s.h.module_path(TARGET)) == source.read_bytes(),
            'EndpointLogPayment original source differs')
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
            'EndpointLogPayment failed artifacts differ')
    require(all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
            'original Smooth installation receipt differs')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, W, module) == binding for module, binding in accepted_bindings.items()) and
                all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
                'project/runtime/original acceptance changed during probe')

    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / W / 'runs')
    probe = run_dir / 'OriginalPrimeEndpointLogPaymentProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = s.ops.run(run_dir, 'serialized-whole-endpoint-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_EndpointLogPayment_actual_whole_module_api_probe_v1', 'source_base_commit': W,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'failed_setup': {'path': str(PROJECT / SETUP), **SETUP_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'W_original_Smooth_acceptance_preserved': ACCEPTED, 'original_accepted_counts': accepted_counts,
        'accepted_prefix_live_source_count': 130, 'accepted_prefix_dependency_count': 129,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_source_and_failed_setup_preserved': True,
        'all_original_W_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_ENDPOINT_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'ENDPOINT_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_ENDPOINT_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'ENDPOINT_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
