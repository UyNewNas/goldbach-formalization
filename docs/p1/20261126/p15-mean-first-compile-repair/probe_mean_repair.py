#!/usr/bin/env python3
"""Typecheck the three-splice MeanCorrection repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
X = '09bf8a02b4c96798930abe2826cfb27529c01ad3'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-mean-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
TARGET = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
ACCEPTED = [ENDPOINT]
SETUP = '.lake/build/ir/ImbalancedChen/P5PrimeDivisorMeanCorrection.setup.json'

DRIVER_FP = {'bytes': 223361, 'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'}

MANIFEST_FP = {'bytes': 357110, 'sha256': '25eef56e95dee4c5ef7308b49b35bf125dc79af032fd5bef0e658bed8001a04a'}

BEFORE = {'bytes': 17065, 'sha256': '1da7fe8cde7360ba7748bf1c3f85e00ad1da470a15638eb8cf4b6a32ffdfc3ee'}

AFTER = {'bytes': 17171, 'sha256': 'efb2138a0a1837c60ab5484afee7d884364dbf118f2753a3690881baebb4c02d'}

SETUP_FP = {'bytes': 6416378, 'sha256': 'e51ad84eea0a873a4414e09a754beaaf1eb4caca2632d7c56a8bc2a0921d4675'}

ACCEPTED_SOURCE_PINS = {'ImbalancedChen.P5OriginalPrimeEndpointLogPayment': {'bytes': 13668,
                                                      'sha256': '1a9baa44f798fba58671d473f3be4def2eaefd6c758413e0f7d60b3238edef3c'}}

RUN_PINS = {'attempt-00000': {'CONTEXT_AFTER.json': {'bytes': 306206,
                                          'sha256': 'c897d7f14b6c6cef66c7ccbbbd2905d13f7539af2990c3ccceaf898d0eb0dfb0'},
                   'CONTEXT_BEFORE.json': {'bytes': 306206,
                                           'sha256': 'c897d7f14b6c6cef66c7ccbbbd2905d13f7539af2990c3ccceaf898d0eb0dfb0'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 8702,
                                   'sha256': 'ee4f055634e6e56673e586fe3db1998ff10d7a45c8f99907481461292b8edb58'},
                   'WORKER_RESULT.json': {'bytes': 8637,
                                          'sha256': '744a42fc02e4fb9d9134b7a15bf38b552b0e6d51e7dbc2732baa7a85f5af3965'}},
 'attempt-00001': {'CONTEXT_AFTER.json': {'bytes': 506374,
                                          'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                   'CONTEXT_BEFORE.json': {'bytes': 506374,
                                           'sha256': 'cd603957864771e99195597935aebc1e822970c36ce4c02d88a4d621ef2ba22d'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 50678,
                                   'sha256': '11fe73336284239346394cd6c1480cc9cfc94a883dddfcacd71230ab3492a53d'},
                   'WORKER_RESULT.json': {'bytes': 50562,
                                          'sha256': '4a12b1cacaaa5fa6db440b79b34e9ac4b7e5c0208f2dd3dd9ac5e8340e65575b'}}}

ORIGINAL_RUN_SUMMARIES = [{'accepted_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
  'all_selected_owners_accepted': True,
  'failures': {},
  'reused_complete_selected_owners': [],
  'source_commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
  'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
  'worker_exit_code': 0},
 {'accepted_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
  'all_selected_owners_accepted': False,
  'failures': {'ImbalancedChen.P5PrimeDivisorMeanCorrection': 'normal failed/scope differs: '
                                                              'ImbalancedChen.P5PrimeDivisorMeanCorrection'},
  'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment'],
  'source_commit': 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa',
  'targets': ['ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
              'ImbalancedChen.P5PrimeDivisorMeanCorrection',
              'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
              'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
              'ImbalancedChen.P1OriginalSingletonAtlasTrim',
              'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'worker_exit_code': 1}]

RETAINED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-endpoint-api-repair-v1/f6e63d1b9785be30a607fb0ff55151ca95d1a6aa/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 521383,
                                                                                                                                                            'sha256': '4395d60e039a34e91693b327246d2b349390d3d1242b16dfbe7714b6f2ca9846'}}


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
    for commit in (Y, W, U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original Y/W/U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees

def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', Y + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / Y / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original Y driver/manifest differs')
    d = ModuleType('unchanged_Y_mean_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT, d.RUNNER, d.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, X), 'Y reader environment differs')
    s = d.helpers()
    originals = {}
    for index, (attempt, pins) in enumerate(RUN_PINS.items()):
        folder = ROOT / Y / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original Y run evidence differs')
        require(fp(folder / 'executed-driver.py') == DRIVER_FP, 'executed Y reader differs')
        result, worker = [s.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        summary = ORIGINAL_RUN_SUMMARIES[index]
        require(all(result.get(key) == value for key, value in summary.items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original Y RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original Y context pair differs')
        originals[attempt] = result
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == [ENDPOINT] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:2] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [ENDPOINT] and set(later['failures']) == {TARGET} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original Y first success/later partial scopes differ')
    spec = d.preflight(s, Y, ACCEPTED)
    require(len(spec.active) == 110 and len(spec.dependency_pins) == 109 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'accepted-prefix scope differs')
    accepted_bindings, accepted_counts = {}, {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, Y, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, Y, module)
        require(binding == later['acceptance_bindings'][module] and
                fp(PROJECT / s.h.module_path(module)) == ACCEPTED_SOURCE_PINS[module],
                'complete original Y accepted binding/source differs')
        require(len(binding['audits']) == 1, 'original Y owner audit count differs')
        audit = s.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == {'owned_count': 24, 'public_count': 24}, 'original Y owner export counts differ')
        accepted_bindings[module], accepted_counts[module] = binding, counts
    require(accepted_bindings[ENDPOINT] == first['acceptance_bindings'][ENDPOINT], 'Endpoint first Y acceptance differs from later reuse')
    require(spec.supplier_evidence == first['original_supplier_acceptance_bindings'] and
            all(later['original_supplier_acceptance_bindings'].get(module) == binding
                for module, binding in spec.supplier_evidence.items()),
            'original Y accepted-prefix supplier bindings differ')
    source = PROJECT / s.h.module_path(TARGET)
    require(fp(source) == BEFORE and d.git_file(Y, s.h.module_path(TARGET)) == source.read_bytes(),
            'MeanCorrection original source differs')
    active = s.h.closure(spec.graph, later['targets'])
    watch = active | set(d.TARGETS)
    require(len(active) == 157 and len(watch) == 160 and len(spec.graph) == 360, 'source/watch scope differs')

    def sources():
        return {module: fp(PROJECT / s.h.module_path(module)) for module in sorted(spec.graph)}

    def artifacts():
        return {module: d.module_artifacts(s, module) for module in sorted(watch)}

    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence_trees()
    before_git = s.d.original_git_state(REPO)
    require(sum(len(rows) for rows in before_artifacts.values()) == 3360,
            'original 160-module artifact inventory differs')
    require(len(before_artifacts[TARGET]) == 21 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(value is None for path, value in before_artifacts[TARGET].items() if path != SETUP),
            'MeanCorrection failed artifacts differ')
    require(all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
            'original Endpoint installation receipt differs')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, Y, module) == binding for module, binding in accepted_bindings.items()) and
                all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
                'project/runtime/original acceptance changed during probe')

    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / Y / 'runs')
    probe = run_dir / 'PrimeDivisorMeanCorrectionProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = s.ops.run(run_dir, 'serialized-whole-mean-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_PrimeDivisorMeanCorrection_actual_whole_module_api_probe_v1', 'source_base_commit': Y,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'failed_setup': {'path': str(PROJECT / SETUP), **SETUP_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'Y_original_Endpoint_acceptance_preserved': ACCEPTED, 'original_accepted_counts': accepted_counts,
        'accepted_prefix_live_source_count': 110, 'accepted_prefix_dependency_count': 109,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_source_and_failed_setup_preserved': True,
        'all_original_Y_W_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_MEAN_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'MEAN_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_MEAN_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'MEAN_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
