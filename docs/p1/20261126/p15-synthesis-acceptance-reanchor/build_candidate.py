#!/usr/bin/env python3
"""Append only Mean@AA; bind the reviewed Synthesis repair to source anchor AB.

No candidate is emitted until the actual AB source publication and successful
whole-module repair probe are supplied. This builder only writes under /tmp.
"""
from pathlib import Path
import argparse
import ast
import copy
import hashlib
import json
import pprint
import re
import sys

sys.dont_write_bytecode = True
AA = 'ae373b971d2b88f97532dc883d835751dd10c67b'
Z = 'bde4a91307cb5e5872b6fc3c1e4a1520908b10c2'
AB = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/MEAN_AA_PUBLIC_ACCEPTANCE.json'
AA_DRIVER = {'bytes': 251538, 'sha256': 'affa66215b9180e61052ba185f2502b5865416898bc8504b44175abe448bb074'}
AA_MANIFEST = {'bytes': 359729, 'sha256': '39eaeca8207c7f387d6b5c6e44d85b38836c721c3c7b1cf1172bbe4c7f95d6c3'}
AA_PUBLIC = {'bytes': 11979, 'sha256': '6d13eca3d7080946540ce94e98c169a2c38c1a5e7b0232294ae5557b67a5ced7'}
AA_READ = {'bytes': 37016, 'sha256': '6e850427d91c24550cbc7b3f3764435514d7b8cc83cd29a149c7949c196b15c8'}
AA_METADATA = {'bytes': 12121, 'sha256': '8ed51ed62a58c41efb5cb58be6dc8ec61dddca46ce80fd87c424106646660d07'}
SYNTHESIS_BEFORE = {'bytes': 14458, 'sha256': '9d8b3b273ade3bf3a35aff7469e16f5fac24d9896eb31171c48c0f04328a8cd7'}
SYNTHESIS_AFTER = {'bytes': 14462, 'sha256': '990ceec9aae74a67c7e1b25e94d66b33644214e1fc0bb3193275ed1b09c50322'}
SYNTHESIS_REPAIR = {'bytes': 2371, 'sha256': '6a64e01ee06cbe340e151d66de8916143bf7c5b43e32c495650004e1e860bcec'}
SYNTHESIS_PROBE_JOB = 'job_d98b1db30a4d406887de810840109325'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(value):
    return {k: value[k] for k in ('bytes', 'sha256')}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def functions(text):
    return {n.name: ast.get_source_segment(text, n) for n in ast.parse(text).body
            if isinstance(n, ast.FunctionDef)}


def replace_once(text, before, after):
    need(text.count(before) == 1, 'nonunique builder splice: ' + before[:100])
    return text.replace(before, after)


def closure(graph, modules):
    seen, pending = set(), list(modules)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-anchor', required=True)
    p.add_argument('--public-summary', type=Path,
                   default=Path('/tmp/p15-aa-actual/MEAN_AA_PUBLIC_ACCEPTANCE.json'))
    p.add_argument('--acceptance-read', type=Path,
                   default=Path('/tmp/p15-aa-actual/ACTUAL_AA_ACCEPTANCE_READ.json'))
    p.add_argument('--repair-source', type=Path, required=True)
    p.add_argument('--repair-candidate', type=Path, required=True)
    p.add_argument('--repair-review-path', required=True)
    p.add_argument('--output', type=Path, default=Path('/tmp/p15-entrypoint-ac'))
    args = p.parse_args()
    need(__debug__ and args.source_anchor == AB,
         'exact published AB source anchor required')
    need(args.output.resolve() == Path('/tmp/p15-entrypoint-ac'),
         'only the separate local /tmp/p15-entrypoint-ac output directory is supported')
    need(args.repair_review_path ==
         'docs/p1/20261126/p15-synthesis-first-compile-repair/REPAIR_CANDIDATE.json',
         'exact Synthesis repair review path required')
    old = Path('/tmp/p15-entrypoint-aa/run_selected.py').read_bytes()
    manifest_raw = Path('/tmp/p15-entrypoint-aa/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == AA_DRIVER and fp(manifest_raw) == AA_MANIFEST, 'frozen AA baseline differs')
    manifest = json.loads(manifest_raw)
    before_manifest = copy.deepcopy(manifest)
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    public_raw, read_raw = args.public_summary.read_bytes(), args.acceptance_read.read_bytes()
    public, read = json.loads(public_raw), json.loads(read_raw)
    metadata_raw = Path('/tmp/p15-aa-actual/ACTUAL_AA_METADATA.json').read_bytes()
    need(fp(public_raw) == AA_PUBLIC and fp(read_raw) == AA_READ and fp(metadata_raw) == AA_METADATA,
         'actual AA cloud-collected public/read/metadata fingerprints differ')
    metadata = json.loads(metadata_raw)
    need(public == read['public_summaries']['MEAN_AA_PUBLIC_ACCEPTANCE'] and
         public['source_commit'] == read['source_commit'] == AA and
         public['source_anchor_commit'] == read['source_anchor_commit'] == Z and
         public['schema'] == 'p15_AA_original_accepted_owner_public_acceptance_v1' and
         public['status'] == 'ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION' and
         public['selected_owners_revalidated'] == [MEAN] and set(public['owners']) == {MEAN} and
         public['original_run'] == 'runs/attempt-00000' and
         public['compiler_job'] == 'job_a01a8d1e8a7d4178988c0c0a5f296b6d' and
         public['current_read_live_source_count'] == 108 and
         public['current_read_preserved_dependency_count'] == 107 and
         public['normal_or_kernel_commands_executed'] == 0 and public['new_lean_acceptance'] is False and
         public['whole_P1_5_complete'] is False, 'actual AA accepted-prefix public identity differs')
    owner = public['owners'][MEAN]
    need((owner['owned_count'], owner['public_count'], owner['audit_id']) ==
         (22, 22, '6f3e2f324ba32c191175') and
         owner['owner_live_source_closure_count'] == len(closure(graph, [MEAN])) == 108 and
         public['driver'] == {'commit': AA, 'path': DRIVER, **AA_DRIVER} and
         public['source_manifest'] == {'commit': AA, 'path': MANIFEST, **AA_MANIFEST} and
         owner['source_sha256'] == manifest['project_sources'][MEAN]['sha256'],
         'Mean@AA own source/count/driver/manifest differs')
    actual = []
    for index in (0, 1):
        raw = Path('/tmp/p15-aa-actual/attempt-%05d-RESULT.json' % index).read_bytes()
        result = json.loads(raw)
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        wr = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        pins = metadata['runs']['attempt-%05d' % index]
        need(fp(raw) == pin(pins['RESULT.json']) and fp(wr) == pin(pins['WORKER_RESULT.json']),
             'actual AA RESULT/WORKER pins differ')
        actual.append(result)
    first, later = actual
    need(first['targets'] == first['accepted_owners'] == [MEAN] and first['failures'] == {} and
         first['worker_exit_code'] == 0 and first['reused_complete_selected_owners'] == [] and
         first['final_stock_readiness']['exit_code'] == 0 and
         len(first['original_supplier_acceptance_bindings']) == 0 and
         later['targets'] == manifest['selection_guidance']['subsequent_6_targets'] and
         later['accepted_owners'] == later['reused_complete_selected_owners'] == [MEAN] and
         later['failures'] == {SYNTHESIS: 'normal failed/scope differs: ' + SYNTHESIS} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['acceptance_bindings'][MEAN] == first['acceptance_bindings'][MEAN] and
         len(later['original_supplier_acceptance_bindings']) == 25 and
         public['later_same_source_reuse'] == read['original_runs'][1] and
         public['later_same_source_reuse']['compiler_job'] == 'job_2d377894edb64660880d7f3e8783b2ee' and
         len(public['later_same_source_reuse']['not_started_modules']) == 4,
         'original AA successful/partial run identities differ')
    group = {'source_commit': AA, 'compiler_job': public['compiler_job'],
             'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
             'run': 'runs/attempt-00000', 'owners': [MEAN],
             'driver': public['driver'], 'source_graph': public['source_manifest'],
             'published_source_count': 360,
             'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC, **fp(public_raw)},
             'evidence_kind': 'bounded_public_acceptance'}
    prior = {'group': 'mean_aa', 'source_commit': AA, 'source_sha256': owner['source_sha256'],
             'live_source_closure_count': 108, 'historical_group': group,
             'owned_count': 22, 'public_count': 22, 'audit_id': owner['audit_id']}
    scope = {'targets': [MEAN], 'accepted': [MEAN], 'reused': [], 'failed': [],
             'not_accepted': [], 'not_started': [], 'readiness': [MEAN], 'exit_code': 0,
             'live_count': 108, 'result': public['original_result'], 'worker': public['original_worker_result'],
             'requested_targets': public['original_requested_targets']}
    need(scope['result'] == pin(metadata['runs']['attempt-00000']['RESULT.json']) and
         scope['worker'] == pin(metadata['runs']['attempt-00000']['WORKER_RESULT.json']),
         'Mean@AA public original run pins differ')
    later_pins = {key: pin(value) for key, value in
                  public['later_same_source_reuse']['evidence_bindings'].items()}
    need(set(later_pins) == set(metadata['runs']['attempt-00001']) | {'executed-driver.py'} and
         all(later_pins[key] == pin(value) for key, value in metadata['runs']['attempt-00001'].items()) and
         later_pins['executed-driver.py'] == AA_DRIVER, 'original AA later run pins differ')
    repair_raw, source_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][SYNTHESIS]
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / row['path']).read_bytes()
    need(fp(repair_raw) == SYNTHESIS_REPAIR and
         repair['schema'] == 'p15_sharp_prime_synthesis_one_proof_splice_candidate_v1' and
         repair['source_base_commit'] == AA and repair['source'] == row['path'] and
         repair['before'] == pin(row) == fp(before) == SYNTHESIS_BEFORE and
         repair['after'] == fp(source_raw) == SYNTHESIS_AFTER and
         len(repair['splices']) == 1 and repair['declaration_count'] == 18 and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['axioms_or_sorry_added'] is False and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe']['exit_code'] == 0 and
         repair['actual_whole_module_probe']['compiler_job'] == SYNTHESIS_PROBE_JOB and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'reviewed Synthesis proof repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'Synthesis splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode())); end = stop
    need(b''.join(pieces) + before[end:] == source_raw and
         re.findall(r'^import\s+(\S+)\s*$', source_raw.decode(), re.M) == row['all_imports'],
         'Synthesis bytes outside reviewed splice or imports changed')
    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
        ('endpoint_y_prior_source_binding', 'require_endpoint_y_prior_scope', 'retained_endpoint_y_prior_target'))
    replacements = [
        ('endpoint_y_prior_source_binding', 'mean_aa_prior_source_binding'),
        ('require_endpoint_y_prior_scope', 'require_mean_aa_prior_scope'),
        ('retained_endpoint_y_prior_target', 'retained_mean_aa_prior_target'),
        ('ENDPOINT_Y_FAILED_MEAN', 'MEAN_AA_FAILED_SYNTHESIS'), ('ENDPOINT_Y_', 'MEAN_AA_'),
        ('p15_Y_original_accepted_owner_public_acceptance_v1', 'p15_AA_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ("'current_read_live_source_count': 110, 'current_read_preserved_dependency_count': 109",
         "'current_read_live_source_count': 108, 'current_read_preserved_dependency_count': 107"),
        ('later_same_Y_reuse_run', 'later_same_AA_reuse_run'),
        ('Endpoint@Y', 'Mean@AA'), ('original Y', 'original AA'),
        ('original Endpoint', 'original Mean'), ('Endpoint reuse', 'Mean reuse'), ('later7', 'later6'),
    ]
    for before_text, after_text in replacements:
        need(before_text in adapter, 'missing adapter fragment: ' + before_text)
        adapter = adapter.replace(before_text, after_text)
    template = Path(__file__).with_name('mean_aa_prior_adapter.py.in').read_text()
    need(adapter + '\n' == template, 'reviewed Mean@AA three-function template differs')
    constants = {'MEAN_AA_MODULE': MEAN, 'MEAN_AA_FAILED_SYNTHESIS': SYNTHESIS,
                 'MEAN_AA_PRIOR_SOURCE_ANCHOR': Z,
                 'MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS': {MEAN: prior},
                 'MEAN_AA_PRIOR_RUNS': {MEAN: scope},
                 'MEAN_AA_LATER_PINS': later_pins, 'MEAN_AA_LATER_TARGETS': later['targets'],
                 'MEAN_AA_LATER_RECORD': public['later_same_source_reuse']}
    inserted = '\n\n# Fixed Mean@AA acceptance; original AA later6 remains partial.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        ' | set(ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS),\n',
        ' | set(ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS) | set(MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS),\n')
    code = replace_once(code,
        '    for module, prior in previous.items():\n        if module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:',
        '    for module, prior in previous.items():\n'
        '        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Mean@AA prior classification differs: ' + module)\n"
        '            mean_aa_prior_source_binding(s, graph, sources, module, prior)\n'
        '            continue\n'
        '        if module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:',
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        '            retained_mean_aa_prior_target(s, spec, module)\n'
        '        elif module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + Z + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'Z-anchored 21-root', 'AB-anchored 21-root')
    code = replace_once(code, 'Smooth@W and Endpoint@Y\n', 'Smooth@W, Endpoint@Y and Mean@AA\n')
    manifest['source_anchor_commit'] = args.source_anchor
    row.update(**fp(source_raw), git_blob=hashlib.sha1(
        b'blob ' + str(len(source_raw)).encode() + b'\0' + source_raw).hexdigest())
    origin = manifest['target_source_origins'][SYNTHESIS]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(source_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': args.repair_review_path, **fp(repair_raw)})
    manifest['previously_accepted_targets'][MEAN] = prior
    guide = manifest['selection_guidance']
    guide.update(minimum_first_targets=[SYNTHESIS], minimum_first_source_count=112,
                 minimum_first_dependency_count=111, minimum_first_artifact_watch_module_count=130,
                 minimum_first_historical_supplier_count=2)
    guide['previously_accepted_not_compile_targets'].append(MEAN)
    guide['remaining_project_graph_unblocked_compile_candidates'].remove(MEAN)
    remaining = [m for m in guide['subsequent_6_targets'] if m != MEAN]
    guide.update(subsequent_5_targets=remaining, subsequent_5_source_count=157,
                 subsequent_5_dependency_count=152, subsequent_5_artifact_watch_module_count=160,
                 subsequent_5_historical_supplier_count=26)
    active, first_active = closure(graph, remaining), closure(graph, [SYNTHESIS])
    historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
    need(len(first_active) == 112 and len(first_active - {SYNTHESIS}) == 111 and
         len(first_active | set(manifest['targets'])) == 130 and
         first_active & historical == {MEAN, ENDPOINT} and len(active) == 157 and
         len(active - set(remaining)) == 152 and len(active | set(manifest['targets'])) == 160 and
         len(active & historical) == 26 and
         SYNTHESIS not in closure(graph, [MEAN]) and
         len(manifest['previously_accepted_targets']) == 13 and
         len(manifest['project_sources']) == 360 and len(manifest['fixed_dependencies']) == 303 and
         len(manifest['unaccepted_p3_dependencies']) == 19,
         'AC source/own dependency scope differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. Synthesis first112/111 '
        'has two historical suppliers, Endpoint@Y and Mean@AA. Later5 closure157/152 includes all thirteen prior targets '
        'and 26 historical supplier entries. Original AA remaining5 has 25 because Mean is still its current completed '
        'owner there. Mean retains its AA attempt-00000 acceptance with final stock and unchanged reuse in partial AA '
        'attempt-00001; Synthesis failed and four following targets were unstarted. Both original run contexts, executed '
        'drivers and six Mean receipts remain fixed; the previous twelve priors are unchanged. Old subsequent6/7/8/10/11/13/14/15 '
        'guidance remains historical. No prior is selected or rebound. The source installer is separate.')
    need({k: v for k, v in manifest['project_sources'].items() if k != SYNTHESIS} ==
         {k: v for k, v in before_manifest['project_sources'].items() if k != SYNTHESIS} and
         all(manifest['project_sources'][m][k] == old_row[k] for m, old_row in before_manifest['project_sources'].items()
             for k in ('imports', 'all_imports')), 'unrelated source/import change')
    need({k: v for k, v in manifest['target_source_origins'].items() if k != SYNTHESIS} ==
         {k: v for k, v in before_manifest['target_source_origins'].items() if k != SYNTHESIS},
         'unrelated source origin changed')
    need({k: v for k, v in manifest['previously_accepted_targets'].items() if k != MEAN} ==
         before_manifest['previously_accepted_targets'], 'twelve prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(manifest[key] == before_manifest[key], 'old policy changed: ' + key)
    mr = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + AA_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if old_functions[name] != new_functions[name]}
    added = set(new_functions) - set(old_functions)
    need(len(old_functions) == 58 and len(new_functions) == 61 and
         changed == {'source_manifest', 'preflight'} and added ==
         {'mean_aa_prior_source_binding', 'require_mean_aa_prior_scope', 'retained_mean_aa_prior_target'},
         'unexpected existing/new function changes')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': mr,
                      'mean_aa_prior_adapter.py': inserted.encode()}.items():
        (args.output / name).write_bytes(raw)
    report = {'schema': 'p15_AB_source_Mean_AA_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'adapter': fp(inserted.encode()),
              'original_AA_function_count': len(old_functions), 'unchanged_AA_functions': len(old_functions) - 2,
              'changed_functions': sorted(changed), 'new_functions': sorted(added),
              'twelve_prior_identities_unchanged': True, 'other_359_sources_all_imports_303_19_policy_unchanged': True,
              'actual_AA_public': fp(public_raw), 'actual_AA_acceptance_read': fp(read_raw),
              'Synthesis_repair': {'source': fp(source_raw), 'review': fp(repair_raw), 'splices': len(repair['splices'])},
              'first': {'sources': 112, 'dependencies': 111, 'watch_modules': 130, 'historical_suppliers': 2},
              'later5': {'sources': 157, 'dependencies': 152, 'watch_modules': 160, 'historical_suppliers': 26},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (args.output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
