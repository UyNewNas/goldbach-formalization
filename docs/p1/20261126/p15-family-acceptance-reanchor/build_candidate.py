#!/usr/bin/env python3
"""Build S only after actual R publication inputs exist; never publish or compile.

PUBLISHED_INPUTS.json must name source_anchor_commit, family_source and three
publications (allk_public, admissible_public, family_repair). File entries contain
local_path, bytes, sha256; publication entries also contain the canonical path.
No runner or manifest is generated while that actual binding file is absent.
"""
import argparse
import ast
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import pprint
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
Q_DIR = HERE.parent / 'entrypoint'
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
P = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
ALLK = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
ADM = 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily'
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
REL = 'docs/p1/20261126/p15-current-corrections'
PUBLIC_REL = 'docs/p1/20261125/p15-current-public-acceptance/'
Q_RUNNER_FP = {'bytes': 101219, 'sha256': 'c168664e6350f79a77c7b07d22db09167ac9a3906b18a251c4c308b773cfbce5'}
Q_MANIFEST_FP = {'bytes': 342103, 'sha256': 'b37216a0928fbd7ebb0c14ff4cb51dfbfda568cd1d606db61966417dbb5077a6'}
FAMILY_SOURCE_FP = {'bytes': 19563, 'sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109'}
LATER13 = [ALLK, ADM, FAMILY,
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
FIXED_RUNS = {
    ALLK: {'group': 'allk_q', 'compiler_job': 'job_f7f42e3d3b7249cd8b60d383ce69a869',
        'run': 'runs/attempt-00000', 'owned': 34, 'public': 31, 'audit_id': '14d74f4877522c8c50f1',
        'closure': 73, 'targets': [ALLK], 'accepted': [ALLK], 'reused': [], 'failed': [],
        'not_accepted': [], 'not_started': [], 'readiness': [ALLK], 'exit_code': 0, 'live_count': 73,
        'result': {'bytes': 33421, 'sha256': '1d53e27318da9580b417ae8bc3925d31b23a043f82d3c52e611b3bb3ad824362'},
        'worker': {'bytes': 33356, 'sha256': '007d6ed0cfc78c08669dd616ac9b428b88e43efbd7e137bdda1e83bdc247c625'}},
    ADM: {'group': 'admissible_q', 'compiler_job': 'job_7b6961dd4ada4d1e82ed170a66eee311',
        'run': 'runs/attempt-00001', 'owned': 42, 'public': 42, 'audit_id': 'ee6394de268ce05592c6',
        'closure': 70, 'targets': LATER13, 'accepted': [ALLK, ADM], 'reused': [ALLK], 'failed': [FAMILY],
        'not_accepted': LATER13[2:], 'not_started': LATER13[3:], 'readiness': [ADM, FAMILY], 'exit_code': 1, 'live_count': 157,
        'result': {'bytes': 47299, 'sha256': '4edbb82b0d72d025a415a7d9f532112c80b7bae7d4f7279c5514900ea56450ec'},
        'worker': {'bytes': 47183, 'sha256': '1cfc84b483e31ed1f500b2e56ac4fb9dbbd60187f40ac5603f7c0892dcccf2db'}},
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def read_fixed(binding):
    need(type(binding['bytes']) is int and binding['bytes'] > 0 and re.fullmatch('[0-9a-f]{64}', binding['sha256']),
         'publication fingerprint not fixed')
    raw = Path(binding['local_path']).read_bytes()
    need(fp(raw) == {k: binding[k] for k in ('bytes', 'sha256')}, 'frozen input differs: ' + binding['local_path'])
    return raw


def replace_once(text, before, after):
    need(text.count(before) == 1, 'expected one original splice: ' + before[:100])
    return text.replace(before, after, 1)


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name); pending.extend(graph[name])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bindings', type=Path, default=HERE / 'PUBLISHED_INPUTS.json')
    parser.add_argument('--manifest-output', type=Path, default=Path('/tmp/p15-entrypoint-s/SOURCE_MANIFEST.json'))
    args = parser.parse_args()
    need(args.bindings.is_file(), 'R_PUBLICATION_NOT_BOUND: no candidate may be frozen yet')
    inputs = json.loads(args.bindings.read_bytes())
    anchor = inputs['source_anchor_commit']
    need(re.fullmatch('[0-9a-f]{40}', anchor) and anchor not in (P, Q), 'actual distinct R source anchor required')
    q_runner_raw, q_manifest_raw = [(Q_DIR / name).read_bytes() for name in ('run_selected.py', 'SOURCE_MANIFEST.json')]
    need(fp(q_runner_raw) == Q_RUNNER_FP and fp(q_manifest_raw) == Q_MANIFEST_FP, 'frozen Q runner/manifest changed')
    manifest = json.loads(q_manifest_raw)
    old_manifest = deepcopy(manifest)
    graph = {n: row['imports'] for n, row in manifest['project_sources'].items()}
    source = read_fixed(inputs['family_source'])
    need(fp(source) == FAMILY_SOURCE_FP, 'Family no-output-probed source differs')
    publications = inputs['publications']
    need(set(publications) == {'allk_public', 'admissible_public', 'family_repair'}, 'publication scope differs')
    repair_raw = read_fixed(publications['family_repair'])
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][FAMILY]
    old_row = deepcopy(row)
    blob = hashlib.sha1(b'blob ' + str(len(source)).encode() + b'\0' + source).hexdigest()
    source_imports = [n for line in re.findall(r'^import\s+([^\n]+)$', source.decode(), re.M) for n in line.split()]
    need(source_imports == row['all_imports'], 'Family imports changed')
    need(repair['module'] == FAMILY and repair['canonical_path'] == row['path'] and
         repair['before'] == {k: old_row[k] for k in ('bytes', 'sha256')} and
         repair['after'] == fp(source), 'Family published provenance differs')
    priors, runs = {}, {}
    for module, key, filename in [(ALLK, 'allk_public', 'ALLK_Q_PUBLIC_ACCEPTANCE.json'),
                                  (ADM, 'admissible_public', 'ADMISSIBLE_Q_PUBLIC_ACCEPTANCE.json')]:
        publication = publications[key]
        need(publication['path'] == PUBLIC_REL + filename, 'Q public canonical path differs')
        public = json.loads(read_fixed(publication))
        fixed = FIXED_RUNS[module]
        owner = public['owners'][module]
        need(public['source_commit'] == Q and public['source_anchor_commit'] == P and
             public['compiler_job'] == fixed['compiler_job'] and public['original_run'] == fixed['run'] and
             public['driver'] == {'commit': Q, 'path': REL + '/run_selected.py', **Q_RUNNER_FP} and
             public['source_manifest'] == {'commit': Q, 'path': REL + '/SOURCE_MANIFEST.json', **Q_MANIFEST_FP} and
             public['original_result'] == fixed['result'] and public['original_worker_result'] == fixed['worker'] and
             public['original_targets'] == fixed['targets'] and set(public['original_requested_targets']) == set(fixed['targets']) and
             len(public['original_requested_targets']) == len(fixed['targets']) and
             owner['source_commit'] == Q and owner['source_sha256'] == manifest['project_sources'][module]['sha256'] and
             (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
             (fixed['owned'], fixed['public'], fixed['audit_id']) and len(closure(graph, [module])) == fixed['closure'],
             'actual original Q identity differs: ' + module)
        prior = {'group': fixed['group'], 'source_commit': Q, 'source_sha256': owner['source_sha256'],
            'live_source_closure_count': fixed['closure'],
            'historical_group': {'source_commit': Q, 'compiler_job': fixed['compiler_job'],
                'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                'run': fixed['run'], 'owners': [module], 'driver': public['driver'], 'source_graph': public['source_manifest'],
                'published_source_count': 360,
                'public_evidence': {'commit': anchor, 'path': publication['path'], **{k: publication[k] for k in ('bytes', 'sha256')}},
                'evidence_kind': 'bounded_public_acceptance'},
            'owned_count': fixed['owned'], 'public_count': fixed['public'], 'audit_id': fixed['audit_id']}
        priors[module] = prior
        runs[module] = {k: fixed[k] for k in ('targets', 'accepted', 'reused', 'failed', 'not_accepted', 'not_started',
                                            'readiness', 'exit_code', 'live_count', 'result', 'worker')}
        runs[module]['requested_targets'] = public['original_requested_targets']
    manifest['source_anchor_commit'] = anchor
    row.update(**fp(source), git_blob=blob)
    origin = manifest['target_source_origins'][FAMILY]
    origin['canonical_source'] = {'commit': anchor, 'path': row['path'], **fp(source)}
    origin['source_reviews'].append({'commit': anchor, 'path': publications['family_repair']['path'], **fp(repair_raw)})
    manifest['previously_accepted_targets'].update(priors)
    guide = manifest['selection_guidance']
    later = [n for n in guide['subsequent_13_targets'] if n not in priors]
    need(len(later) == 11 and len(closure(graph, [FAMILY])) == 75 and len(closure(graph, later)) == 157 and
         len(closure(graph, later) | set(manifest['targets'])) == 160, 'Family/later11/watch scope differs')
    guide.update(minimum_first_targets=[FAMILY], minimum_first_source_count=75, minimum_first_dependency_count=74,
        remaining_project_graph_unblocked_compile_candidates=later, subsequent_11_targets=later,
        subsequent_11_source_count=157, subsequent_11_dependency_count=146,
        subsequent_11_artifact_watch_module_count=160)
    guide['previously_accepted_not_compile_targets'].extend(priors)
    guide['previous_target_live_reuse_condition'] = (
        'Only historical targets in the actual selected closure: Family root75 revalidates HB@F67, Licensed@M68, '
        'PerGroup@O69, AllK@Q73 and Admissible@Q70, without Support or Cutoff. Later11 closure157 additionally '
        'reuses Support@B109 and Cutoff@K68. All seven keep their original source commits and cannot be selected. '
        'AllK retains successful Q attempt-00000 and its final stock receipt; Admissible retains partial failed '
        'Q attempt-00001 with AllK reused, Family failed and ten not started. Old subsequent13/14/15 lists are historical.')
    need([n for n in graph if manifest['project_sources'][n] != old_manifest['project_sources'][n]] == [FAMILY],
         'source-row changes exceed Family')
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    const = {'Q_ALLK_MODULE': ALLK, 'Q_PRIOR_SOURCE_ANCHOR': P, 'Q_PREVIOUSLY_ACCEPTED_TARGETS': priors, 'Q_PRIOR_RUNS': runs}
    declarations = '\n'.join(k + ' = ' + pprint.pformat(v, width=108, sort_dicts=False) for k, v in const.items())
    snippet = (HERE / 'q_prior_adapter.py').read_text()
    snippet = snippet[snippet.index('def q_prior_source_binding'):]
    text = q_runner_raw.decode()
    text = replace_once(text, 'P-anchored 21-root', 'R-anchored 21-root')
    text = replace_once(text, 'Licensed@M and PerGroup@O', 'Licensed@M, PerGroup@O, AllK@Q and Admissible@Q')
    text = replace_once(text, "SOURCE_ANCHOR = '" + P + "'", "SOURCE_ANCHOR = '" + anchor + "'")
    text = replace_once(text, "MANIFEST_SHA = '" + Q_MANIFEST_FP['sha256'] + "'", "MANIFEST_SHA = '" + fp(manifest_bytes)['sha256'] + "'")
    addition = ('# Fixed original Q acceptances, publicly bound at R; old five priors stay unchanged.\n' + declarations +
        '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **Q_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n' + snippet + '\n\n')
    text = replace_once(text, 'def require(ok, message):', addition + 'def require(ok, message):')
    old_set = "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE, LICENSED_M_MODULE, PERGROUP_O_MODULE},"
    text = replace_once(text, old_set, old_set[:-1] + ' | set(Q_PREVIOUSLY_ACCEPTED_TARGETS),')
    text = replace_once(text, '    for module, prior in previous.items():\n',
        '    for module, prior in previous.items():\n'
        '        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Q prior classification differs: ' + module)\n"
        '            q_prior_source_binding(s, graph, sources, module, prior)\n            continue\n')
    text = replace_once(text, '        if module == PERGROUP_O_MODULE:\n            retained_pergroup_o_target(s, spec, module)',
        '        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:\n            retained_q_prior_target(s, spec, module)\n'
        '        elif module == PERGROUP_O_MODULE:\n            retained_pergroup_o_target(s, spec, module)')
    ast.parse(text)
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_output.write_bytes(manifest_bytes)
    (HERE / 'run_selected.py').write_text(text)
    report = {'source_anchor_commit': anchor, 'runner': fp(text.encode()),
              'manifest_path': str(args.manifest_output), 'manifest': fp(manifest_bytes), 'verified': False,
              'publication_inputs': str(args.bindings), 'new_lean_acceptance': False}
    (HERE / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
