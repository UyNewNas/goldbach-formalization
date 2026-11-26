#!/usr/bin/env python3
"""Append only Endpoint@Y; bind the reviewed Mean repair to source anchor Z.

No candidate is emitted until actual Y public evidence and the successful
whole-module repair probe are provided. This builder only writes under /tmp.
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
Y = 'f6e63d1b9785be30a607fb0ff55151ca95d1a6aa'
X = '09bf8a02b4c96798930abe2826cfb27529c01ad3'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/ENDPOINT_Y_PUBLIC_ACCEPTANCE.json'
Y_DRIVER = {'bytes': 223361, 'sha256': 'e84c943388675d65c63b701c1663f030ec3c340e22d1ee31fa1c1ada3bc67918'}
Y_MANIFEST = {'bytes': 357110, 'sha256': '25eef56e95dee4c5ef7308b49b35bf125dc79af032fd5bef0e658bed8001a04a'}
Y_PUBLIC = {'bytes': 12271, 'sha256': '4ca613c9dac4ff86f21b0728977f0f9c66ad1f0acd2abf99a8da87a7de8d461b'}
Y_READ = {'bytes': 37133, 'sha256': 'ae53a023131f8eb776c622289ce77289a22f88af285dc21f98307e015b3011ec'}
Y_METADATA = {'bytes': 13224, 'sha256': '2fbab049f9cb0e59ffb0764dc5d960ae9794098c2620dc63355a41286f14ef80'}


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
                   default=Path('/tmp/p15-y-actual/ENDPOINT_Y_PUBLIC_ACCEPTANCE.json'))
    p.add_argument('--acceptance-read', type=Path,
                   default=Path('/tmp/p15-y-actual/ACTUAL_Y_ACCEPTANCE_READ.json'))
    p.add_argument('--repair-source', type=Path, required=True)
    p.add_argument('--repair-candidate', type=Path, required=True)
    p.add_argument('--repair-review-path', required=True)
    p.add_argument('--output', type=Path, default=Path('/tmp/p15-entrypoint-aa'))
    args = p.parse_args()
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', args.source_anchor) and
         args.source_anchor not in (Y, X), 'exact new Z source publication required')
    need(args.output.resolve() == args.output and args.output.is_relative_to(Path('/tmp')),
         'only a local /tmp output directory is supported')
    need(args.repair_review_path ==
         'docs/p1/20261126/p15-mean-first-compile-repair/REPAIR_CANDIDATE.json',
         'exact Mean repair review path required')
    old = Path('/tmp/p15-entrypoint-y/run_selected.py').read_bytes()
    manifest_raw = Path('/tmp/p15-entrypoint-y/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == Y_DRIVER and fp(manifest_raw) == Y_MANIFEST, 'frozen Y baseline differs')
    manifest = json.loads(manifest_raw)
    before_manifest = copy.deepcopy(manifest)
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    public_raw, read_raw = args.public_summary.read_bytes(), args.acceptance_read.read_bytes()
    public, read = json.loads(public_raw), json.loads(read_raw)
    metadata_raw = Path('/tmp/p15-y-actual/ACTUAL_Y_METADATA.json').read_bytes()
    need(fp(public_raw) == Y_PUBLIC and fp(read_raw) == Y_READ and fp(metadata_raw) == Y_METADATA,
         'actual Y cloud-collected public/read/metadata fingerprints differ')
    metadata = json.loads(metadata_raw)
    need(public == read['public_summaries']['ENDPOINT_Y_PUBLIC_ACCEPTANCE'] and
         public['source_commit'] == read['source_commit'] == Y and
         public['source_anchor_commit'] == read['source_anchor_commit'] == X and
         public['schema'] == 'p15_Y_original_accepted_owner_public_acceptance_v1' and
         public['status'] == 'ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION' and
         public['selected_owners_revalidated'] == [ENDPOINT] and set(public['owners']) == {ENDPOINT} and
         public['original_run'] == 'runs/attempt-00000' and
         public['current_read_live_source_count'] == 110 and
         public['current_read_preserved_dependency_count'] == 109 and
         public['normal_or_kernel_commands_executed'] == 0 and public['new_lean_acceptance'] is False and
         public['whole_P1_5_complete'] is False, 'actual Y accepted-prefix public identity differs')
    owner = public['owners'][ENDPOINT]
    need((owner['owned_count'], owner['public_count'], owner['audit_id']) ==
         (24, 24, 'a602bb782d20fdd11079') and
         owner['owner_live_source_closure_count'] == len(closure(graph, [ENDPOINT])) == 110 and
         public['driver'] == {'commit': Y, 'path': DRIVER, **Y_DRIVER} and
         public['source_manifest'] == {'commit': Y, 'path': MANIFEST, **Y_MANIFEST} and
         owner['source_sha256'] == manifest['project_sources'][ENDPOINT]['sha256'],
         'Endpoint@Y own source/count/driver/manifest differs')
    actual = []
    for index in (0, 1):
        raw = Path('/tmp/p15-y-actual/attempt-%05d-RESULT.json' % index).read_bytes()
        result = json.loads(raw)
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        wr = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        pins = metadata['runs']['attempt-%05d' % index]
        need(fp(raw) == pin(pins['RESULT.json']) and fp(wr) == pin(pins['WORKER_RESULT.json']),
             'actual Y RESULT/WORKER pins differ')
        actual.append(result)
    first, later = actual
    need(first['targets'] == first['accepted_owners'] == [ENDPOINT] and first['failures'] == {} and
         first['worker_exit_code'] == 0 and first['reused_complete_selected_owners'] == [] and
         first['final_stock_readiness']['exit_code'] == 0 and
         later['targets'] == manifest['selection_guidance']['subsequent_7_targets'] and
         later['accepted_owners'] == later['reused_complete_selected_owners'] == [ENDPOINT] and
         later['failures'] == {MEAN: 'normal failed/scope differs: ' + MEAN} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['acceptance_bindings'][ENDPOINT] == first['acceptance_bindings'][ENDPOINT] and
         public['later_same_source_reuse'] == read['original_runs'][1] and
         len(public['later_same_source_reuse']['not_started_modules']) == 5,
         'original Y successful/partial run identities differ')
    group = {'source_commit': Y, 'compiler_job': public['compiler_job'],
             'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
             'run': 'runs/attempt-00000', 'owners': [ENDPOINT],
             'driver': public['driver'], 'source_graph': public['source_manifest'],
             'published_source_count': 360,
             'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC, **fp(public_raw)},
             'evidence_kind': 'bounded_public_acceptance'}
    prior = {'group': 'endpoint_y', 'source_commit': Y, 'source_sha256': owner['source_sha256'],
             'live_source_closure_count': 110, 'historical_group': group,
             'owned_count': 24, 'public_count': 24, 'audit_id': owner['audit_id']}
    scope = {'targets': [ENDPOINT], 'accepted': [ENDPOINT], 'reused': [], 'failed': [],
             'not_accepted': [], 'not_started': [], 'readiness': [ENDPOINT], 'exit_code': 0,
             'live_count': 110, 'result': public['original_result'], 'worker': public['original_worker_result'],
             'requested_targets': public['original_requested_targets']}
    need(scope['result'] == pin(metadata['runs']['attempt-00000']['RESULT.json']) and
         scope['worker'] == pin(metadata['runs']['attempt-00000']['WORKER_RESULT.json']),
         'Endpoint@Y public original run pins differ')
    later_pins = {key: pin(value) for key, value in
                  public['later_same_source_reuse']['evidence_bindings'].items()}
    need(set(later_pins) == set(metadata['runs']['attempt-00001']) | {'executed-driver.py'} and
         all(later_pins[key] == pin(value) for key, value in metadata['runs']['attempt-00001'].items()) and
         later_pins['executed-driver.py'] == Y_DRIVER, 'original Y later run pins differ')
    repair_raw, source_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][MEAN]
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / row['path']).read_bytes()
    need(repair['source_base_commit'] == Y and repair['source'] == row['path'] and
         repair['before'] == pin(row) == fp(before) and repair['after'] == fp(source_raw) and
         repair['splices'] and repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['axioms_or_sorry_added'] is False and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe']['exit_code'] == 0 and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'reviewed Mean proof repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'Mean splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode())); end = stop
    need(b''.join(pieces) + before[end:] == source_raw and
         re.findall(r'^import\s+(\S+)\s*$', source_raw.decode(), re.M) == row['all_imports'],
         'Mean bytes outside reviewed splices or imports changed')
    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
        ('smooth_w_prior_source_binding', 'require_smooth_w_prior_scope', 'retained_smooth_w_prior_target'))
    replacements = [
        ('smooth_w_prior_source_binding', 'endpoint_y_prior_source_binding'),
        ('require_smooth_w_prior_scope', 'require_endpoint_y_prior_scope'),
        ('retained_smooth_w_prior_target', 'retained_endpoint_y_prior_target'),
        ('SMOOTH_W_FAILED_ENDPOINT', 'ENDPOINT_Y_FAILED_MEAN'), ('SMOOTH_W_', 'ENDPOINT_Y_'),
        ('p15_W_original_accepted_owner_public_acceptance_v1', 'p15_Y_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_W_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_Y_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ("'current_read_live_source_count': 130, 'current_read_preserved_dependency_count': 129",
         "'current_read_live_source_count': 110, 'current_read_preserved_dependency_count': 109"),
        ('later_same_W_reuse_run', 'later_same_Y_reuse_run'),
        ('Smooth@W', 'Endpoint@Y'), ('original W', 'original Y'),
        ('original Smooth', 'original Endpoint'), ('Smooth reuse', 'Endpoint reuse'), ('later8', 'later7'),
    ]
    for before_text, after_text in replacements:
        need(before_text in adapter, 'missing adapter fragment: ' + before_text)
        adapter = adapter.replace(before_text, after_text)
    constants = {'ENDPOINT_Y_MODULE': ENDPOINT, 'ENDPOINT_Y_FAILED_MEAN': MEAN,
                 'ENDPOINT_Y_PRIOR_SOURCE_ANCHOR': X,
                 'ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS': {ENDPOINT: prior},
                 'ENDPOINT_Y_PRIOR_RUNS': {ENDPOINT: scope},
                 'ENDPOINT_Y_LATER_PINS': later_pins, 'ENDPOINT_Y_LATER_TARGETS': later['targets'],
                 'ENDPOINT_Y_LATER_RECORD': public['later_same_source_reuse']}
    inserted = '\n\n# Fixed Endpoint@Y acceptance; original Y later7 remains partial.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        '} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS) | set(U_PREVIOUSLY_ACCEPTED_TARGETS) | set(SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS),\n',
        '} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS) | set(U_PREVIOUSLY_ACCEPTED_TARGETS) | set(SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS) | set(ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS),\n')
    code = replace_once(code,
        '    for module, prior in previous.items():\n        if module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:',
        '    for module, prior in previous.items():\n'
        '        if module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Endpoint@Y prior classification differs: ' + module)\n"
        '            endpoint_y_prior_source_binding(s, graph, sources, module, prior)\n'
        '            continue\n'
        '        if module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:',
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        '            retained_endpoint_y_prior_target(s, spec, module)\n'
        '        elif module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + X + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'X-anchored 21-root', 'Z-anchored 21-root')
    code = replace_once(code, 'Family@S, Word@U, AllGroup@U and Smooth@W\n',
                        'Family@S, Word@U, AllGroup@U, Smooth@W and Endpoint@Y\n')
    manifest['source_anchor_commit'] = args.source_anchor
    row.update(**fp(source_raw), git_blob=hashlib.sha1(
        b'blob ' + str(len(source_raw)).encode() + b'\0' + source_raw).hexdigest())
    origin = manifest['target_source_origins'][MEAN]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(source_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': args.repair_review_path, **fp(repair_raw)})
    manifest['previously_accepted_targets'][ENDPOINT] = prior
    guide = manifest['selection_guidance']
    guide.update(minimum_first_targets=[MEAN], minimum_first_source_count=108,
                 minimum_first_dependency_count=107, minimum_first_artifact_watch_module_count=128,
                 minimum_first_historical_supplier_count=0)
    guide['previously_accepted_not_compile_targets'].append(ENDPOINT)
    guide['remaining_project_graph_unblocked_compile_candidates'].remove(ENDPOINT)
    remaining = [m for m in guide['subsequent_7_targets'] if m != ENDPOINT]
    guide.update(subsequent_6_targets=remaining, subsequent_6_source_count=157,
                 subsequent_6_dependency_count=151, subsequent_6_artifact_watch_module_count=160,
                 subsequent_6_historical_supplier_count=25)
    active = closure(graph, remaining)
    historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
    need(len(closure(graph, [MEAN])) == 108 and
         len(closure(graph, [MEAN]) | set(manifest['targets'])) == 128 and
         not (closure(graph, [MEAN]) & historical) and len(active) == 157 and
         len(active - set(remaining)) == 151 and len(active | set(manifest['targets'])) == 160 and
         len(active & historical) == 25 and
         MEAN not in closure(graph, [ENDPOINT]) and ENDPOINT not in closure(graph, [MEAN]),
         'AA source/own dependency scope differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. Mean first108/107 '
        'has no historical suppliers. Later6 closure157/151 includes all twelve prior targets and 25 historical '
        'supplier entries. Original Y remaining6 has 24 because Endpoint is still its current completed owner there. '
        'Endpoint retains its Y attempt-00000 acceptance with final stock and unchanged reuse in partial Y attempt-00001; '
        'Mean failed and five following targets were unstarted. Both original run contexts, executed drivers and '
        'six Endpoint receipts remain fixed; the previous eleven priors are unchanged. Old subsequent7/8/10/11/13/14/15 '
        'guidance remains historical. No prior is selected or rebound. The source installer is separate.')
    need({k: v for k, v in manifest['project_sources'].items() if k != MEAN} ==
         {k: v for k, v in before_manifest['project_sources'].items() if k != MEAN} and
         all(manifest['project_sources'][m][k] == row[k] for m, row in before_manifest['project_sources'].items()
             for k in ('imports', 'all_imports')), 'unrelated source/import change')
    need({k: v for k, v in manifest['target_source_origins'].items() if k != MEAN} ==
         {k: v for k, v in before_manifest['target_source_origins'].items() if k != MEAN},
         'unrelated source origin changed')
    need({k: v for k, v in manifest['previously_accepted_targets'].items() if k != ENDPOINT} ==
         before_manifest['previously_accepted_targets'], 'eleven prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(manifest[key] == before_manifest[key], 'old policy changed: ' + key)
    mr = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + Y_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if old_functions[name] != new_functions[name]}
    added = set(new_functions) - set(old_functions)
    need(changed == {'source_manifest', 'preflight'} and added ==
         {'endpoint_y_prior_source_binding', 'require_endpoint_y_prior_scope', 'retained_endpoint_y_prior_target'},
         'unexpected existing/new function changes')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': mr,
                      'endpoint_y_prior_adapter.py': inserted.encode()}.items():
        (args.output / name).write_bytes(raw)
    report = {'schema': 'p15_Z_source_Endpoint_Y_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'adapter': fp(inserted.encode()),
              'original_Y_function_count': len(old_functions), 'unchanged_Y_functions': len(old_functions) - 2,
              'changed_functions': sorted(changed), 'new_functions': sorted(added),
              'eleven_prior_identities_unchanged': True, 'other_359_sources_all_imports_303_19_policy_unchanged': True,
              'actual_Y_public': fp(public_raw), 'actual_Y_acceptance_read': fp(read_raw),
              'Mean_repair': {'source': fp(source_raw), 'review': fp(repair_raw), 'splices': len(repair['splices'])},
              'first': {'sources': 108, 'dependencies': 107, 'watch_modules': 128, 'historical_suppliers': 0},
              'later6': {'sources': 157, 'dependencies': 151, 'watch_modules': 160, 'historical_suppliers': 25},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (args.output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
