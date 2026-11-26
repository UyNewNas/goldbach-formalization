#!/usr/bin/env python3
"""Typecheck the exact published AD TrimLog draft under preserved AE/AG acceptances."""
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
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-trimlog-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
RESERVEBRANCHES = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ATLASTRIM = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
ACCEPTED = [LOWERTRIM, ATLASTRIM]


DRIVER_FP = {'bytes': 306454, 'sha256': '2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e'}

MANIFEST_FP = {'bytes': 364863, 'sha256': '6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5'}







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
                                                                                                                                                             'sha256': '73cf0272db2e0e33c40462de795e6dc97c0c7b6ae4703b96fb0c94e1d4f31b03'},
 '/workspace/p1-complete-proof/20261126-p15-reservebranches-api-repair-v1/63ad8bf4c52caed9f4e199834ae1d2b0b18f971b/runs/attempt-00000/SOURCE_REPAIR_RESULT.json': {'bytes': 503796,
                                                                                                                                                                   'sha256': 'b3ab010937a2baafd2a4b1b46e7a9a62c867bbb47d1ef5fbd84202f806fbb9cc'}}


ACCEPTED_COUNTS = {'ImbalancedChen.P1OriginalSingletonAtlasTrim': {'owned_count': 11, 'public_count': 9},
 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': {'owned_count': 10, 'public_count': 10}}
ACCEPTED_FIRST_RUN = {'ImbalancedChen.P1OriginalSingletonAtlasTrim': 1, 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid': 0}

AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'

AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'

DRAFT_MODULE = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'

DRAFT_SOURCE = 'ImbalancedChen/P1OriginalSingletonAtlasTrimLogAccuracy.lean'

PUBLISHED_CANDIDATE = 'docs/source-only/20261126/p1-atlas-trim-log-accuracy-budget-sum/P1OriginalSingletonAtlasTrimLogAccuracy.lean'

CANDIDATE_FP = {'bytes': 4303, 'sha256': 'b0786de15bf78fed3751fc408735482b807e39931e87056d3d60780fa2123bb4'}

AG_DRIVER_FP = {'bytes': 343325, 'sha256': '0440906dfc3caa894ff7226e53ad42be54adda1d5879bd1a72cad578a3b3612d'}

AG_MANIFEST_FP = {'bytes': 369103, 'sha256': '21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9'}

CURRENT_ACCEPTED = ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']

CURRENT_COUNTS = {'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': {'owned_count': 6, 'public_count': 6},
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': {'owned_count': 13, 'public_count': 13}}

CURRENT_SOURCES = {'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': {'bytes': 7431,
                                                       'sha256': 'dca0a3c5eab650f5329c2cf1159af676d4d3c44d1b86dd2ee158e596aa55a57d'},
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': {'bytes': 8197,
                                                        'sha256': 'd5945aa39ab54bc5c4aeb529a96299e7ab3bcf0c4fcb946296d3a697753a2bb7'}}

CURRENT_FIRST_RUN = {'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': 1,
 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': 0}

AG_RUN_PINS = {'attempt-00000': {'CONTEXT_AFTER.json': {'bytes': 459769,
                                          'sha256': 'ad53842b6a0189acb2357b63ce3fcc4552c85c00f6b0284e4c56c36719656b93'},
                   'CONTEXT_BEFORE.json': {'bytes': 459769,
                                           'sha256': 'ad53842b6a0189acb2357b63ce3fcc4552c85c00f6b0284e4c56c36719656b93'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 45791,
                                   'sha256': '8df860c46e8442267591dad3356f5610deee849d9c959fad38037274bf81536a'},
                   'WORKER_RESULT.json': {'bytes': 45726,
                                          'sha256': '989e9500f604e54cde2dcc0f1bc862b3b27c0da77e987219a90a5fc3c7ef4190'}},
 'attempt-00001': {'CONTEXT_AFTER.json': {'bytes': 482694,
                                          'sha256': 'b6ea4ef3477db7dfbb6c6e961a467e5104127f3cb66ce58ef4ab7b76e2f5676f'},
                   'CONTEXT_BEFORE.json': {'bytes': 482694,
                                           'sha256': 'b6ea4ef3477db7dfbb6c6e961a467e5104127f3cb66ce58ef4ab7b76e2f5676f'},
                   'GIT_AFTER.json': {'bytes': 1157,
                                      'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'GIT_BEFORE.json': {'bytes': 1157,
                                       'sha256': 'be7b38573ef04d4652abfb70c65dd27931915dfee99b3371f11a6ce86f45901e'},
                   'RESULT.json': {'bytes': 57039,
                                   'sha256': '17770f8bf394c41f6e9ea650b9a0ee7545dcc0dfe3a82c1a6902db8486661a7e'},
                   'WORKER_RESULT.json': {'bytes': 56974,
                                          'sha256': 'a48a65e07effd868d4769ef4630bb696c4c55662572c74fdc57763d4091552c5'}}}

AG_RUN_SUMMARIES = [{'accepted_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
  'all_selected_owners_accepted': True,
  'failures': {},
  'reused_complete_selected_owners': [],
  'source_commit': '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b',
  'targets': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
  'worker_exit_code': 0},
 {'accepted_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
                      'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'all_selected_owners_accepted': True,
  'failures': {},
  'reused_complete_selected_owners': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'],
  'source_commit': '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b',
  'targets': ['ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
              'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'],
  'worker_exit_code': 0}]

AE_FAILURE_EVIDENCE_PINS = {'/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal-command.json': {'bytes': 1318,
                                                                                                                                                                                                                                                              'sha256': 'a450854359288c2c10eb99178c44fc12b57ed86bfb13597f1cc99ccb6d2876a6'},
 '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/ca13f51c65d37870b96a6b1eb32ac30e92019fa2/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/normal/ImbalancedChen.P5OriginalPrimeAtlasReserveBranches/attempt-00000/normal.log': {'bytes': 196840,
                                                                                                                                                                                                                                                     'sha256': 'ba220ef31dbefca82c4bd3e1297980cb99d70d22024daf93d30ab09cdb7b7a92'}}

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
    for commit in (AG, AE, AC, AA, Y, W, U, S, Q):
        base = ROOT / commit
        require(base.is_dir() and base.resolve() == base, 'original evidence root differs')
        records = {}
        for path in sorted(base.rglob('*')):
            require(not path.is_symlink(), 'symlink in original AG/AE/AC/AA/Y/W/U/S/Q evidence')
            records[str(path.relative_to(base))] = 'directory' if path.is_dir() else fp(path)
        trees[commit] = records
    return trees


def require_runtime_scopes(ae_spec, ag_spec):
    require(ag_spec.graph == ae_spec.graph and len(ag_spec.graph) == 360 and
            len(ae_spec.active) == 153 and len(ae_spec.dependency_pins) == 151 and
            len(ag_spec.active) == 144 and len(ag_spec.dependency_pins) == 142 and
            all(ag_spec.sources[m] == ae_spec.sources[m] for m in ae_spec.active) and
            DRAFT_MODULE not in ag_spec.graph and RESERVEBRANCHES not in ae_spec.active,
            'separate AE prefix/current AG scopes or unchanged dependency sources differ')

def require_current_sources(observed, manifest):
    expected = {m: {k: row[k] for k in ('bytes', 'sha256')}
                for m, row in manifest['project_sources'].items()}
    require(len(expected) == 360 and observed == expected,
            'current AG source inventory differs; old AE failed preimage is not current')

def require_uninstalled_draft(source, artifacts):
    require(source is None and len(artifacts) == 21 and all(value is None for value in artifacts.values()),
            'unregistered draft canonical source or project output already exists')

def run(candidate_path):
    require(__debug__ and fp(candidate_path) == CANDIDATE_FP, 'exact AD candidate identity differs')
    published = subprocess.check_output(['git', 'show', AD + ':' + PUBLISHED_CANDIDATE], cwd=REPO)
    require(raw_fp(published) == CANDIDATE_FP and candidate_path.read_bytes() == published,
            'candidate differs from its exact AD source-only publication')
    raw, manifest_raw = [subprocess.check_output(['git', 'show', AE + ':' + path], cwd=REPO)
                         for path in (DRIVER, MANIFEST)]
    entry = ROOT / AE / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP and
            fp(entry) == DRIVER_FP and entry.read_bytes() == raw, 'original AE driver/manifest differs')
    d = ModuleType('unchanged_AE_trimlog_probe_reader')
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
            later['targets'][:3] == ACCEPTED + [RESERVEBRANCHES] and later['accepted_owners'] == ACCEPTED and
            later['reused_complete_selected_owners'] == [LOWERTRIM] and set(later['failures']) == {RESERVEBRANCHES} and
            later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            'final_stock_readiness' not in later, 'original AE first success/later partial scopes differ')
    spec = d.preflight(s, AE, ACCEPTED)
    require(len(spec.active) == 153 and len(spec.dependency_pins) == 151 and spec.order == ACCEPTED and
            set(spec.initial_owners) == set(ACCEPTED) and RESERVEBRANCHES not in spec.active, 'accepted-prefix scope differs')
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

    raw_ag, manifest_ag = [subprocess.check_output(['git', 'show', AG + ':' + path], cwd=REPO)
                           for path in (DRIVER, MANIFEST)]
    entry_ag = ROOT / AG / 'runs/attempt-00000/executed-driver.py'
    require(raw_fp(raw_ag) == AG_DRIVER_FP and raw_fp(manifest_ag) == AG_MANIFEST_FP and
            fp(entry_ag) == AG_DRIVER_FP and entry_ag.read_bytes() == raw_ag, 'original AG reader/manifest differs')
    g = ModuleType('unchanged_AG_trimlog_probe_reader'); g.__file__ = str(entry_ag)
    exec(compile(raw_ag, str(entry_ag), 'exec'), g.__dict__)
    require((g.REPO, g.PROJECT, g.ROOT, g.RUNNER, g.SOURCE_ANCHOR) ==
            (REPO, PROJECT, ROOT, DRIVER, AF), 'AG reader environment differs')
    sg = g.helpers()
    ag_runs = {}
    for index, (attempt, pins) in enumerate(AG_RUN_PINS.items()):
        folder = ROOT / AG / 'runs' / attempt
        for name, expected in pins.items():
            require(fp(folder / name) == expected, 'original AG run evidence differs')
        require(fp(folder / 'executed-driver.py') == AG_DRIVER_FP, 'executed AG reader differs')
        result, worker = [sg.api.read_json(folder / name) for name in ('RESULT.json', 'WORKER_RESULT.json')]
        require(all(result.get(key) == value for key, value in AG_RUN_SUMMARIES[index].items()) and
                all(result.get(key) == value for key, value in worker.items()), 'original AG RESULT/WORKER scope differs')
        for stem in ('CONTEXT', 'GIT'):
            require(pins[stem + '_BEFORE.json'] == pins[stem + '_AFTER.json'], 'original AG context pair differs')
        require(result['all_selected_owners_accepted'] is True and result['worker_exit_code'] == 0 and
                result['failures'] == {} and result['final_stock_readiness']['exit_code'] == 0,
                'original AG success/final-stock identity differs')
        ag_runs[attempt] = result
    current = g.preflight(sg, AG, CURRENT_ACCEPTED)
    require(current.order == CURRENT_ACCEPTED and set(current.initial_owners) == set(CURRENT_ACCEPTED) and
            len(current.manifest['previously_accepted_targets']) == 16 and
            current.manifest['previously_accepted_targets'] == g.PREVIOUSLY_ACCEPTED_TARGETS,
            'current AG accepted-owner/prior scope differs')
    require_runtime_scopes(spec, current)
    current_bindings, current_counts = {}, {}
    for module in CURRENT_ACCEPTED:
        g.require_completed_existing_owner(sg, AG, current, module, current.initial_owners[module])
        binding = g.acceptance_binding(sg, AG, module)
        original = ag_runs['attempt-' + str(CURRENT_FIRST_RUN[module]).zfill(5)]
        require(binding == original['acceptance_bindings'][module] ==
                ag_runs['attempt-00001']['acceptance_bindings'][module] and
                fp(PROJECT / sg.h.module_path(module)) == CURRENT_SOURCES[module] and len(binding['audits']) == 1,
                'current AG original owner identity/source differs')
        audit = sg.api.read_json(Path(binding['audits'][0]['result']['path']))
        counts = {'owned_count': audit['total_owned_exports'], 'public_count': audit['total_public_exports']}
        require(counts == CURRENT_COUNTS[module], 'current AG accepted export counts differ')
        current_bindings[module], current_counts[module] = binding, counts
    require(len(current.supplier_evidence) == 24 and
            current.supplier_evidence == ag_runs['attempt-00001']['original_supplier_acceptance_bindings'] and
            all(current.supplier_evidence.get(module) == binding
                for module, binding in ag_runs['attempt-00000']['original_supplier_acceptance_bindings'].items()),
            'current AG original supplier bindings differ')
    union = spec.active | current.active
    watch = union | set(g.TARGETS)
    require(len(union) == 157 and len(watch) == 160 and DRAFT_MODULE not in g.TARGETS and
            not (spec.active & set(current.manifest['unaccepted_p3_dependencies'])),
            'combined preservation/new-draft scope differs')

    def sources():
        return {module: fp(PROJECT / sg.h.module_path(module)) for module in sorted(current.graph)}

    def artifacts():
        return {module: g.module_artifacts(sg, module) for module in sorted(watch)}

    def draft_slots():
        return fp(PROJECT / DRAFT_SOURCE), g.module_artifacts(sg, DRAFT_MODULE)

    retained_prior_inputs = {}
    for commit, api in [(AE, s.api), (AG, sg.api)]:
        context = api.read_json(ROOT / commit / 'runs/attempt-00001/CONTEXT_BEFORE.json')
        for path, expected in context['retained_original_evidence'].items():
            require(path not in retained_prior_inputs or retained_prior_inputs[path] == expected,
                    'AE/AG retained evidence pins conflict')
            retained_prior_inputs[path] = expected
    require(all(fp(path) == expected for path, expected in retained_prior_inputs.items()),
            'original AE/AG later-context retained evidence differs')
    before_sources, before_artifacts, before_evidence = sources(), artifacts(), evidence_trees()
    before_git = sg.d.original_git_state(REPO)
    require_current_sources(before_sources, current.manifest)
    require_uninstalled_draft(*draft_slots())
    require(sum(len(rows) for rows in before_artifacts.values()) == 3360,
            'current 160-module artifact inventory differs')
    extras = {**RETAINED_EXTRA_PINS, **AE_FAILURE_EVIDENCE_PINS}
    require(all(fp(path) == expected for path, expected in extras.items()),
            'retained installs/probe0/original AE failed command/log differ')

    def unchanged():
        require(sources() == before_sources and artifacts() == before_artifacts and
                evidence_trees() == before_evidence and sg.d.original_git_state(REPO) == before_git and
                d.snapshot(s, spec) == spec.baseline and g.snapshot(sg, current) == current.baseline and
                all(d.acceptance_binding(s, AE, module) == binding for module, binding in accepted_bindings.items()) and
                all(g.acceptance_binding(sg, AG, module) == binding for module, binding in current_bindings.items()) and
                all(fp(path) == expected for path, expected in retained_prior_inputs.items()) and
                all(fp(path) == expected for path, expected in extras.items()),
                'current sources/artifacts/runtime/original AE or AG acceptances changed during probe')
        require_uninstalled_draft(*draft_slots())

    unchanged()
    run_dir = sg.d.attempt(PROBE_ROOT / AG / 'runs')
    probe = run_dir / 'OriginalSingletonAtlasTrimLogAccuracyProbe.lean'
    sg.d.write_frozen(probe, published)
    suffixes = ['.olean', '.olean.hash', '.olean.private', '.olean.private.hash', '.olean.server',
        '.olean.server.hash', '.ilean', '.ilean.hash', '.ir', '.ir.hash', '.ir.sig', '.c', '.c.hash',
        '.bc', '.bc.hash', '.o', '.o.hash', '.o.export', '.o.export.hash', '.setup.json', '.trace']
    require(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'probe output already exists')
    command = sg.h.serialize(0, run_dir / 'PROBE_LANE.json',
        sg.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    try:
        outcome = sg.ops.run(run_dir, 'serialized-whole-trimlog-probe', command, cwd=PROJECT, relay=False)
    finally:
        unchanged()
    require(fp(probe) == CANDIDATE_FP and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes) and
            outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
            'probe emitted objects or rebuilt a project module')
    log = Path(outcome['log'])
    result = {'schema': 'p15_AtlasTrimLogAccuracy_actual_whole_module_no_output_probe_v1',
        'candidate_publication': {'commit': AD, 'path': PUBLISHED_CANDIDATE, **CANDIDATE_FP},
        'runtime_source_commit': AG, 'original_AE_acceptance_source_commit': AE,
        'exit_code': outcome['exit_code'], 'candidate': {'path': str(probe), **CANDIDATE_FP},
        'whole_original_module_submitted': True, 'Lean_typecheck_commands': 1,
        'original_serializer_and_guard_used': True, 'lake_no_build_env_lean': True,
        'output_object_requested': False, 'existing_project_modules_rebuilt': [],
        'log': {'path': str(log), **fp(log)}, 'compiler_output': log.read_text(),
        'AE_original_accepted_counts': accepted_counts, 'AG_original_accepted_counts': current_counts,
        'AE_prefix_scope': {'sources': 153, 'dependencies': 151, 'suppliers': 25},
        'AG_accepted_scope': {'sources': 144, 'dependencies': 142, 'suppliers': 24},
        'combined_preserved_source_count': 157, 'watched_source_slots': 360,
        'watched_modules': 160, 'watched_artifact_slots': 3360, 'preserved_evidence_tree_count': 9,
        'retained_external_install_and_probe_record_count': len(RETAINED_EXTRA_PINS),
        'old_AE_failed_command_and_log_preserved_as_history': True,
        'current_AG_sources_and_all_accepted_artifacts_preserved': True,
        'new_canonical_source_and_21_project_artifacts_remained_absent': True,
        'all_original_AG_AE_AC_AA_Y_W_U_S_Q_evidence_runtime_and_Git_preserved': True,
        'normal_or_kernel_acceptance_claimed': False, 'new_owner_acceptance': False,
        'whole_P1_5_complete': False}
    sg.d.save(run_dir / 'ACTUAL_TRIMLOG_PROBE_RESULT.json', result)
    print(json.dumps({'status': 'TRIMLOG_WHOLE_MODULE_PROBE_COMPLETE',
        'result_path': str(run_dir / 'ACTUAL_TRIMLOG_PROBE_RESULT.json'), **result}), flush=True)
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
        print(json.dumps({'status': 'TRIMLOG_PROBE_HELD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_acceptance': False}), flush=True)
        raise SystemExit(3)
