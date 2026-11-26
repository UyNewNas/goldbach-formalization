#!/usr/bin/env python3
"""Typecheck the exact two-splice WordDictionary repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
Q = '18e41c4a1c01ca22e5537acb934e04891279b616'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-word-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 130643, 'sha256': 'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'}
TARGET = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
ACCEPTED = ['ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound']
BEFORE = {'bytes': 5613, 'sha256': '8fd465024656d9cc3998b7f810d92ab6316f50c1817f0736e6bb0f88021d49b1'}
AFTER = {'bytes': 5672, 'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'}
SETUP = '.lake/build/ir/ImbalancedChen/P5IndependentPrimeSourceWordDictionary.setup.json'
SETUP_FP = {'bytes': 6329802, 'sha256': '0ab1595e7cb434fea199eefea3f7e041db1e24f030858dbfa50304c4ba07c6bf'}
RUN_PINS = {'attempt-00000': {'RESULT.json': {'bytes': 37042, 'sha256': '554af002bced1b2b2fcfa71834dfc3412684d9214106742d5d0a927dd57546f7'}, 'WORKER_RESULT.json': {'bytes': 36977, 'sha256': 'a456196896172094854f8f6d22dfcd0afa32afd3329e503620c9e4a5623e6548'}}, 'attempt-00001': {'RESULT.json': {'bytes': 43984, 'sha256': '5e909125e1e23eeca59699eb4ff834e2abde2ce148a8530863283101e2586bfc'}, 'WORKER_RESULT.json': {'bytes': 43868, 'sha256': 'f3bc0dbb2fe93c8b1090b34da8ad81f37bcce1192dd137cafe2912c83e08fc4b'}}}


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
    require(raw_fp(raw) == DRIVER_FP and fp(entry) == DRIVER_FP, 'original S driver differs')
    d = ModuleType('unchanged_S_word_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT) == (REPO, PROJECT, ROOT), 'Q environment differs')
    s = d.helpers()
    originals = {}
    for attempt, pins in RUN_PINS.items():
        folder = ROOT / Q / 'runs' / attempt
        for name, pin in pins.items():
            require(fp(folder / name) == pin, 'original S receipt differs')
        originals[attempt] = json.loads((folder / 'RESULT.json').read_bytes())
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == ACCEPTED[:1] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:2] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == ACCEPTED[:1] and
            set(later['failures']) == {TARGET} and later['worker_exit_code'] == 1 and
            later['all_selected_owners_accepted'] is False, 'original S success/partial scopes differ')
    spec = d.preflight(s, Q, ACCEPTED)
    require(len(spec.active) == 75 and len(spec.dependency_pins) == 74 and TARGET not in spec.active,
            'accepted-prefix scope differs')
    accepted_bindings = {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, Q, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, Q, module)
        require(binding == later['acceptance_bindings'][module], 'Q complete accepted binding differs')
        accepted_bindings[module] = binding
    require(accepted_bindings[ACCEPTED[0]] == first['acceptance_bindings'][ACCEPTED[0]],
            'Family original single-owner acceptance differs')
    source = PROJECT / (TARGET.replace('.', '/') + '.lean')
    require(fp(source) == BEFORE and d.git_file(Q, TARGET.replace('.', '/') + '.lean') == source.read_bytes(),
            'WordDictionary original source differs')
    watch = s.h.closure(spec.graph, later['targets']) | set(d.TARGETS)
    require(len(watch) == 160, 'watched module scope differs')
    def sources():
        return {m: fp(PROJECT / s.h.module_path(m)) for m in sorted(spec.graph)}
    def artifacts():
        return {m: d.module_artifacts(s, m) for m in sorted(watch)}
    def evidence():
        result = {}
        for path in sorted([p for commit in (Q, '445201674271f9d9d6b846ecc634a10c4a0c6043') for p in (ROOT / commit).rglob('*')]):
            require(not path.is_symlink(), 'symlink in original S evidence')
            if path.is_file():
                result[str(path)] = fp(path)
        return result
    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence()
    before_git = s.d.original_git_state(REPO)
    require(len(before_sources) == 360 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(v is None for p, v in before_artifacts[TARGET].items() if p != SETUP),
            'WordDictionary failed artifacts differ')
    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, Q, m) == b for m, b in accepted_bindings.items()),
                'project/runtime/original acceptance changed during probe')
    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / Q / 'runs')
    probe = run_dir / 'IndependentPrimeSourceWordDictionaryProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.c', '.bc', '.o']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    outcome = s.ops.run(run_dir, 'serialized-whole-word-probe', command, cwd=PROJECT, relay=False)
    unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_WordDictionary_actual_whole_module_api_probe_v1', 'source_base_commit': Q,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'whole_original_module_submitted': True,
        'Lean_typecheck_commands': 1, 'original_serializer_and_guard_used': True,
        'lake_no_build_env_lean': True, 'output_object_requested': False,
        'existing_project_modules_rebuilt': [], 'log': {'path': str(log), **fp(log)},
        'compiler_output': log.read_text(), 'S_original_Family_acceptance_preserved': ACCEPTED,
        'accepted_prefix_live_source_count': 75, 'accepted_prefix_dependency_count': 74,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_source_and_failed_setup_preserved': True,
        'all_original_S_and_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_WORD_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'WORD_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_WORD_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'WORD_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
