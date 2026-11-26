#!/usr/bin/env python3
"""Typecheck the exact six-splice Family repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-family-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 101219, 'sha256': 'c168664e6350f79a77c7b07d22db09167ac9a3906b18a251c4c308b773cfbce5'}
TARGET = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
ACCEPTED = ['ImbalancedChen.Part3AllKLambdaChartCorrection',
            'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily']
BEFORE = {'bytes': 19242, 'sha256': '5f78dd9a9bdb228388e4b219845ab0d6a0385513695fff58dd27596f8fe703b6'}
AFTER = {'bytes': 19563, 'sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109'}
SETUP = '.lake/build/ir/ImbalancedChen/Part3AllKFamilyLambdaCorrectionBound.setup.json'
SETUP_FP = {'bytes': 6329450, 'sha256': 'e060890186321528c208f648e9cf39c37359677dafba97fdbd79ab0424e100ef'}
RUN_PINS = {
    'attempt-00000': {
        'RESULT.json': {'bytes': 33421, 'sha256': '1d53e27318da9580b417ae8bc3925d31b23a043f82d3c52e611b3bb3ad824362'},
        'WORKER_RESULT.json': {'bytes': 33356, 'sha256': '007d6ed0cfc78c08669dd616ac9b428b88e43efbd7e137bdda1e83bdc247c625'}},
    'attempt-00001': {
        'RESULT.json': {'bytes': 47299, 'sha256': '4edbb82b0d72d025a415a7d9f532112c80b7bae7d4f7279c5514900ea56450ec'},
        'WORKER_RESULT.json': {'bytes': 47183, 'sha256': '1cfc84b483e31ed1f500b2e56ac4fb9dbbd60187f40ac5603f7c0892dcccf2db'}}}


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
    return raw_fp(path.read_bytes())


def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw = subprocess.check_output(['git', 'show', Q + ':' + DRIVER], cwd=REPO)
    entry = ROOT / Q / 'published-entrypoints/run_selected.py'
    require(raw_fp(raw) == DRIVER_FP and fp(entry) == DRIVER_FP, 'original Q driver differs')
    d = ModuleType('unchanged_Q_family_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT) == (REPO, PROJECT, ROOT), 'Q environment differs')
    s = d.helpers()
    originals = {}
    for attempt, pins in RUN_PINS.items():
        folder = ROOT / Q / 'runs' / attempt
        for name, pin in pins.items():
            require(fp(folder / name) == pin, 'original Q receipt differs')
        originals[attempt] = json.loads((folder / 'RESULT.json').read_bytes())
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == ACCEPTED[:1] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:3] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == ACCEPTED[:1] and
            set(later['failures']) == {TARGET} and later['worker_exit_code'] == 1 and
            later['all_selected_owners_accepted'] is False, 'original Q success/partial scopes differ')
    spec = d.preflight(s, Q, ACCEPTED)
    require(len(spec.active) == 74 and len(spec.dependency_pins) == 72 and TARGET not in spec.active,
            'accepted-prefix scope differs')
    accepted_bindings = {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, Q, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, Q, module)
        require(binding == later['acceptance_bindings'][module], 'Q complete accepted binding differs')
        accepted_bindings[module] = binding
    require(accepted_bindings[ACCEPTED[0]] == first['acceptance_bindings'][ACCEPTED[0]],
            'AllK original single-owner acceptance differs')
    source = PROJECT / (TARGET.replace('.', '/') + '.lean')
    require(fp(source) == BEFORE and d.git_file(Q, TARGET.replace('.', '/') + '.lean') == source.read_bytes(),
            'Family original source differs')
    watch = s.h.closure(spec.graph, later['targets']) | set(d.TARGETS)
    require(len(watch) == 160, 'watched module scope differs')
    def sources():
        return {m: fp(PROJECT / s.h.module_path(m)) for m in sorted(spec.graph)}
    def artifacts():
        return {m: d.module_artifacts(s, m) for m in sorted(watch)}
    def evidence():
        result = {}
        for path in sorted((ROOT / Q).rglob('*')):
            require(not path.is_symlink(), 'symlink in original Q evidence')
            if path.is_file():
                result[str(path)] = fp(path)
        return result
    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence()
    before_git = s.d.original_git_state(REPO)
    require(len(before_sources) == 360 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(v is None for p, v in before_artifacts[TARGET].items() if p != SETUP),
            'Family failed artifacts differ')
    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, Q, m) == b for m, b in accepted_bindings.items()),
                'project/runtime/original acceptance changed during probe')
    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / Q / 'runs')
    probe = run_dir / 'AllKFamilyLambdaCorrectionBoundProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.c', '.bc', '.o']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    outcome = s.ops.run(run_dir, 'serialized-whole-family-probe', command, cwd=PROJECT, relay=False)
    unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_Family_actual_whole_module_api_probe_v1', 'source_base_commit': Q,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'whole_original_module_submitted': True,
        'Lean_typecheck_commands': 1, 'original_serializer_and_guard_used': True,
        'lake_no_build_env_lean': True, 'output_object_requested': False,
        'existing_project_modules_rebuilt': [], 'log': {'path': str(log), **fp(log)},
        'compiler_output': log.read_text(), 'Q_original_full_acceptances_preserved': ACCEPTED,
        'accepted_prefix_live_source_count': 74, 'accepted_prefix_dependency_count': 72,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_source_and_failed_setup_preserved': True,
        'all_original_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_FAMILY_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'FAMILY_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_FAMILY_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'FAMILY_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
