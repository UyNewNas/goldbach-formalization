#!/usr/bin/env python3
"""Typecheck the one-splice SharpPrimeSynthesis repair without project outputs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Z = 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2'
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
TARGET = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ACCEPTED = [MEAN]
SETUP = '.lake/build/ir/ImbalancedChen/P5OriginalSharpPrimeSynthesis.setup.json'

DRIVER_FP = {'bytes': 251538, 'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}

MANIFEST_FP = {'bytes': 359729, 'sha256': '39eaeca8207c7f387d6b5c6e44d85b38836c721c3c7b1cf1172bbe4c7f95d6c3'}

BEFORE = {'bytes': 14458, 'sha256': '9d8b3b273ade3bf3a35aff7469e16f5fac24d9896eb31171c48c0f04328a8cd7'}

AFTER = {'bytes': 14462, 'sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322'}

SETUP_FP = {'bytes': 6417017, 'sha256': '42acce65ed6a2b300809309fd909236cd4de13bfb9b5abe1cf27baac10dca87e'}

ACCEPTED_SOURCE_PINS = {'ImbalancedChen.P5PrimeDivisorMeanCorrection': {'bytes': 17171,
                                                 'sha256': 'efb2138a0a1837c60ab5484afee7d884364dbf118f2753a3690881baebb4c02d'}}

RUN_PINS = {'attempt-00000': {'CONTEXT_AFTER.json': {'bytes': 300455,
                                          'sha256': '4ab18f4fe977dfef04b51c9138ee34a31a190030f4a45e265d25d000c81a13bc'},
                   'CONTEXT_BEFORE.json': {'bytes': 300455,
                                           'sha256': '4ab18f4fe977dfef04b51c9138ee34a31a190030f4a45e265d25d000c81a13bc'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 8391,
                                   'sha256': '6256690daae433327b6ef7543891ff829397bda1b15b92ae90096eb104bd9acb'},
                   'WORKER_RESULT.json': {'bytes': 8326,
                                          'sha256': '81e3d09172c6d6e4ba8fcb6af9979553c3b81cbcc22bff92c8b4774e838f2201'}},
 'attempt-00001': {'CONTEXT_AFTER.json': {'bytes': 515448,
                                          'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                   'CONTEXT_BEFORE.json': {'bytes': 515448,
                                           'sha256': '257662bbd5d7c94ec64762a9956bbfd75e3e8f1e41a982f3439f4873041b901b'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 52166,
                                   'sha256': 'cdc4c244088aaf3ca473a2d470c71bd303f72babb301246852e99ad6aa803230'},
                   'WORKER_RESULT.json': {'bytes': 52050,
                                          'sha256': '0bef1c288b0bfd2ee471667b383e09a1b1d6172946e2665b575753525cbf00c1'}}}

ORIGINAL_RUN_SUMMARIES = [{'accepted_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
  'all_selected_owners_accepted': True,
  'failures': {},
  'reused_complete_selected_owners': [],
  'source_commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
  'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
  'worker_exit_code': 0},
 {'accepted_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
  'all_selected_owners_accepted': False,
  'failures': {'ImbalancedChen.P5OriginalSharpPrimeSynthesis': 'normal failed/scope differs: '
                                                               'ImbalancedChen.P5OriginalSharpPrimeSynthesis'},
  'reused_complete_selected_owners': ['ImbalancedChen.P5PrimeDivisorMeanCorrection'],
  'source_commit': 'ae373b971d2b88f97532dc883d835751dd10c67b',
  'targets': ['ImbalancedChen.P5PrimeDivisorMeanCorrection',
              'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
              'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
              'ImbalancedChen.P1OriginalSingletonAtlasTrim',
              'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'worker_exit_code': 1}]

RETAINED_EXTRA_PINS = {'/workspace/p1-complete-proof/20261126-p15-mean-api-repair-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 530642,
                                                                                                                                                        'sha256': '32861aa7155d2e3f2e7a85bfed7d340759d2a0730784ef67134c24e21af8b363'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/OriginalSharpPrimeSynthesisProbe.lean': {'bytes': 14464,
                                                                                                                                                                        'sha256': '40b0bc9e5680cf83cd0769b299f19c1d7fcc2332ef11f5504a6b5617290ebd1e'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/serialized-whole-synthesis-probe.log': {'bytes': 3579,
                                                                                                                                                                       'sha256': 'c722c9da32531e45ad53be48753c8dad2bb52434c392588bf2b90bd23b2bf398'},
 '/workspace/p1-complete-proof/20261126-p15-synthesis-api-probe-v1/ae373b971d2b88f97532dc883d835751dd10c67b/runs/attempt-00000/ACTUAL_SYNTHESIS_PROBE_RESULT.json': {'bytes': 5727,
                                                                                                                                                                     'sha256': '1d3e329e727ce232308131b0b510b8732b34c4241cce44800774735547390e5c'}}


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
    for commit in (AA, Y, W, U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original AA/Y/W/U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees

def run(candidate_path):
    require(__debug__ and fp(candidate_path) == AFTER, 'candidate identity differs')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AA + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / AA / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original AA driver/manifest differs')
    d = ModuleType('unchanged_AA_synthesis_probe_reader')
    d.__file__ = str(entry)
    exec(compile(raw, str(entry), 'exec'), d.__dict__)
    require((d.REPO, d.PROJECT, d.ROOT, d.RUNNER, d.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, Z), 'AA reader environment differs')
    s = d.helpers()
    originals = {}
    for index, (attempt, pins) in enumerate(RUN_PINS.items()):
        folder = ROOT / AA / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original AA run evidence differs')
        require(fp(folder / 'executed-driver.py') == DRIVER_FP, 'executed AA reader differs')
        result, worker = [s.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        summary = ORIGINAL_RUN_SUMMARIES[index]
        require(all(result.get(key) == value for key, value in summary.items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original AA RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original AA context pair differs')
        originals[attempt] = result
    first, later = originals['attempt-00000'], originals['attempt-00001']
    require(first['targets'] == first['accepted_owners'] == [MEAN] and
            first['all_selected_owners_accepted'] is True and first['worker_exit_code'] == 0 and
            later['targets'][:2] == ACCEPTED + [TARGET] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [MEAN] and set(later['failures']) == {TARGET} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original AA first success/later partial scopes differ')
    spec = d.preflight(s, AA, ACCEPTED)
    require(len(spec.active) == 108 and len(spec.dependency_pins) == 107 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and TARGET not in spec.active, 'accepted-prefix scope differs')
    require(len(spec.manifest['previously_accepted_targets']) == 12 and
            spec.manifest['previously_accepted_targets'] == d.PREVIOUSLY_ACCEPTED_TARGETS,
            'original twelve prior identities differ')
    accepted_bindings, accepted_counts = {}, {}
    for module in ACCEPTED:
        d.require_completed_existing_owner(s, AA, spec, module, spec.initial_owners[module])
        binding = d.acceptance_binding(s, AA, module)
        require(binding == later['acceptance_bindings'][module] and
                fp(PROJECT / s.h.module_path(module)) == ACCEPTED_SOURCE_PINS[module],
                'complete original AA accepted binding/source differs')
        require(len(binding['audits']) == 1, 'original AA owner audit count differs')
        audit = s.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == {'owned_count': 22, 'public_count': 22}, 'original AA owner export counts differ')
        accepted_bindings[module], accepted_counts[module] = binding, counts
    require(accepted_bindings[MEAN] == first['acceptance_bindings'][MEAN], 'Mean first AA acceptance differs from later reuse')
    require(spec.supplier_evidence == first['original_supplier_acceptance_bindings'] and
            all(later['original_supplier_acceptance_bindings'].get(module) == binding
                for module, binding in spec.supplier_evidence.items()),
            'original AA accepted-prefix supplier bindings differ')
    source = PROJECT / s.h.module_path(TARGET)
    require(fp(source) == BEFORE and d.git_file(AA, s.h.module_path(TARGET)) == source.read_bytes(),
            'SharpPrimeSynthesis original source differs')
    active = s.h.closure(spec.graph, later['targets'])
    watch = active | set(d.TARGETS)
    require(len(active) == 157 and len(watch) == 160 and len(spec.graph) == 360, 'source/watch scope differs')

    def sources():
        return {module: fp(PROJECT / s.h.module_path(module)) for module in sorted(spec.graph)}

    def artifacts():
        return {module: d.module_artifacts(s, module) for module in sorted(watch)}

    later_context = s.api.read_json(ROOT / AA / 'runs/attempt-00001/CONTEXT_BEFORE.json')
    retained_prior_inputs = later_context['retained_original_evidence']
    require(all(fp(path) == expected for path, expected in retained_prior_inputs.items()),
            'original later-context prior receipts differ')
    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence_trees()
    before_git = s.d.original_git_state(REPO)
    require(sum(len(rows) for rows in before_artifacts.values()) == 3360,
            'original 160-module artifact inventory differs')
    require(len(before_artifacts[TARGET]) == 21 and before_artifacts[TARGET][SETUP] == SETUP_FP and
            all(value is None for path, value in before_artifacts[TARGET].items() if path != SETUP),
            'SharpPrimeSynthesis failed artifacts differ')
    require(all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
            'original Mean installation receipt differs')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and s.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and
                all(d.acceptance_binding(s, AA, module) == binding for module, binding in accepted_bindings.items()) and
                all(fp(path) == expected for path, expected in retained_prior_inputs.items()) and
                all(fp(path) == expected for path, expected in RETAINED_EXTRA_PINS.items()),
                'project/runtime/original acceptance changed during probe')

    unchanged()
    run_dir = s.d.attempt(PROBE_ROOT / AA / 'runs')
    probe = run_dir / 'OriginalSharpPrimeSynthesisProbe.lean'
    s.d.write_frozen(probe, candidate_path.read_bytes())
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = s.h.serialize(0, run_dir / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = s.ops.run(run_dir, 'serialized-whole-synthesis-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == AFTER and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_SharpPrimeSynthesis_actual_whole_module_api_probe_v1', 'source_base_commit': AA,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **AFTER},
        'original_source': BEFORE, 'failed_setup': {'path': str(PROJECT / SETUP), **SETUP_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'AA_original_Mean_acceptance_preserved': ACCEPTED, 'original_accepted_counts': accepted_counts,
        'accepted_prefix_live_source_count': 108, 'accepted_prefix_dependency_count': 107,
        'watched_source_slots': 360, 'watched_modules': 160, 'watched_artifact_slots': 3360,
        'original_twelve_prior_identities_and_later_retained_receipts_preserved': True,
        'original_source_and_failed_setup_preserved': True,
        'all_original_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(run_dir / 'ACTUAL_SYNTHESIS_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'SYNTHESIS_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_SYNTHESIS_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'SYNTHESIS_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
