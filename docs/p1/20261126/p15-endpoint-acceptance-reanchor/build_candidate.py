#!/usr/bin/env python3
"""Append only Smooth@W; bind the reviewed Endpoint repair to source anchor X.

No candidate is emitted until actual W public evidence and the successful
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
W = '6484b348b82d8ca6221262bb53f255fa92e9adc8'
V = 'f23c4f3308b471350064bf0d6ad1bdb0fce0d6fb'
SMOOTH = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/SMOOTH_W_PUBLIC_ACCEPTANCE.json'
W_DRIVER = {'bytes': 194954, 'sha256': '2d53b4d52e3e9a9c8fa5a4853837993dfcfe47aa47f8577f776b59e2ac6ab52f'}
W_MANIFEST = {'bytes': 354491, 'sha256': '0a8d1e86f3783bf264eee4d23bc219834537a0ded653aa035eda4e5874c8d41d'}
W_PUBLIC = {'bytes': 12495, 'sha256': '4cf35e8f4fe8a4224a5bc35a034916da7fec78f31838e0d930fcb8ddaf1129fd'}
W_READ = {'bytes': 40449, 'sha256': 'deee4809d9f07f1424a1434ab3d3d35d7c958f737b9b9145bd05bf5a819754f9'}
W_METADATA = {'bytes': 12989, 'sha256': 'b22d10152d480b48df220d0d373e73f37a2bf9703da04003d34a75a96c82e9b6'}


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
                   default=Path('/tmp/p15-w-actual/SMOOTH_W_PUBLIC_ACCEPTANCE.json'))
    p.add_argument('--acceptance-read', type=Path,
                   default=Path('/tmp/p15-w-actual/ACTUAL_W_ACCEPTANCE_READ.json'))
    p.add_argument('--repair-source', type=Path, required=True)
    p.add_argument('--repair-candidate', type=Path, required=True)
    p.add_argument('--repair-review-path', required=True)
    p.add_argument('--output', type=Path, default=Path('/tmp/p15-entrypoint-y'))
    args = p.parse_args()
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', args.source_anchor) and
         args.source_anchor not in (W, V), 'exact new X source publication required')
    need(args.output.resolve() == args.output and args.output.is_relative_to(Path('/tmp')),
         'only a local /tmp output directory is supported')
    need(args.repair_review_path.startswith('docs/p1/20261126/') and
         '..' not in Path(args.repair_review_path).parts and
         args.repair_review_path.endswith('/REPAIR_CANDIDATE.json'), 'exact repair review path required')
    old = Path('/tmp/p15-entrypoint-w/run_selected.py').read_bytes()
    manifest_raw = Path('/tmp/p15-entrypoint-w/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == W_DRIVER and fp(manifest_raw) == W_MANIFEST, 'frozen W baseline differs')
    manifest = json.loads(manifest_raw)
    before_manifest = copy.deepcopy(manifest)
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    public_raw, read_raw = args.public_summary.read_bytes(), args.acceptance_read.read_bytes()
    public, read = json.loads(public_raw), json.loads(read_raw)
    metadata_raw = Path('/tmp/p15-w-actual/ACTUAL_W_METADATA.json').read_bytes()
    need(fp(public_raw) == W_PUBLIC and fp(read_raw) == W_READ and fp(metadata_raw) == W_METADATA,
         'actual W cloud-collected public/read/metadata fingerprints differ')
    metadata = json.loads(metadata_raw)
    need(public == read['public_summaries']['SMOOTH_W_PUBLIC_ACCEPTANCE'] and
         public['source_commit'] == read['source_commit'] == W and
         public['source_anchor_commit'] == read['source_anchor_commit'] == V and
         public['schema'] == 'p15_W_original_accepted_owner_public_acceptance_v1' and
         public['status'] == 'ORIGINAL_W_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION' and
         public['selected_owners_revalidated'] == [SMOOTH] and set(public['owners']) == {SMOOTH} and
         public['original_run'] == 'runs/attempt-00000' and
         public['current_read_live_source_count'] == 130 and
         public['current_read_preserved_dependency_count'] == 129 and
         public['normal_or_kernel_commands_executed'] == 0 and public['new_lean_acceptance'] is False and
         public['whole_P1_5_complete'] is False, 'actual W accepted-prefix public identity differs')
    owner = public['owners'][SMOOTH]
    need((owner['owned_count'], owner['public_count'], owner['audit_id']) ==
         (11, 11, 'f3566f142140cbf69a53') and
         owner['owner_live_source_closure_count'] == len(closure(graph, [SMOOTH])) == 130 and
         public['driver'] == {'commit': W, 'path': DRIVER, **W_DRIVER} and
         public['source_manifest'] == {'commit': W, 'path': MANIFEST, **W_MANIFEST} and
         owner['source_sha256'] == manifest['project_sources'][SMOOTH]['sha256'],
         'Smooth@W own source/count/driver/manifest differs')
    actual = []
    for index in (0, 1):
        raw = Path('/tmp/p15-w-actual/attempt-%05d-RESULT.json' % index).read_bytes()
        result = json.loads(raw)
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        wr = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        pins = metadata['runs']['attempt-%05d' % index]
        need(fp(raw) == pin(pins['RESULT.json']) and fp(wr) == pin(pins['WORKER_RESULT.json']),
             'actual W RESULT/WORKER pins differ')
        actual.append(result)
    first, later = actual
    need(first['targets'] == first['accepted_owners'] == [SMOOTH] and first['failures'] == {} and
         first['worker_exit_code'] == 0 and first['reused_complete_selected_owners'] == [] and
         first['final_stock_readiness']['exit_code'] == 0 and
         later['targets'] == manifest['selection_guidance']['subsequent_8_targets'] and
         later['accepted_owners'] == later['reused_complete_selected_owners'] == [SMOOTH] and
         later['failures'] == {ENDPOINT: 'normal failed/scope differs: ' + ENDPOINT} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['acceptance_bindings'][SMOOTH] == first['acceptance_bindings'][SMOOTH] and
         public['later_same_source_reuse'] == read['original_runs'][1] and
         len(public['later_same_source_reuse']['not_started_modules']) == 6,
         'original W successful/partial run identities differ')
    group = {'source_commit': W, 'compiler_job': public['compiler_job'],
             'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
             'run': 'runs/attempt-00000', 'owners': [SMOOTH],
             'driver': public['driver'], 'source_graph': public['source_manifest'],
             'published_source_count': 360,
             'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC, **fp(public_raw)},
             'evidence_kind': 'bounded_public_acceptance'}
    prior = {'group': 'smooth_w', 'source_commit': W, 'source_sha256': owner['source_sha256'],
             'live_source_closure_count': 130, 'historical_group': group,
             'owned_count': 11, 'public_count': 11, 'audit_id': owner['audit_id']}
    scope = {'targets': [SMOOTH], 'accepted': [SMOOTH], 'reused': [], 'failed': [],
             'not_accepted': [], 'not_started': [], 'readiness': [SMOOTH], 'exit_code': 0,
             'live_count': 130, 'result': public['original_result'], 'worker': public['original_worker_result'],
             'requested_targets': public['original_requested_targets']}
    need(scope['result'] == pin(metadata['runs']['attempt-00000']['RESULT.json']) and
         scope['worker'] == pin(metadata['runs']['attempt-00000']['WORKER_RESULT.json']),
         'Smooth@W public original run pins differ')
    later_pins = {key: pin(value) for key, value in
                  public['later_same_source_reuse']['evidence_bindings'].items()}
    need(set(later_pins) == set(metadata['runs']['attempt-00001']) | {'executed-driver.py'} and
         all(later_pins[key] == pin(value) for key, value in metadata['runs']['attempt-00001'].items()) and
         later_pins['executed-driver.py'] == W_DRIVER, 'original W later run pins differ')
    repair_raw, source_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][ENDPOINT]
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / row['path']).read_bytes()
    need(repair['source_base_commit'] == W and repair['source'] == row['path'] and
         repair['before'] == pin(row) == fp(before) and repair['after'] == fp(source_raw) and
         repair['splices'] and repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['axioms_or_sorry_added'] is False and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe']['exit_code'] == 0 and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'reviewed Endpoint proof repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'Endpoint splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode())); end = stop
    need(b''.join(pieces) + before[end:] == source_raw and
         re.findall(r'^import\s+(\S+)\s*$', source_raw.decode(), re.M) == row['all_imports'],
         'Endpoint bytes outside reviewed splices or imports changed')
    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
        ('family_s_prior_source_binding', 'require_family_s_prior_scope', 'retained_family_s_prior_target'))
    replacements = [
        ('family_s_prior_source_binding', 'smooth_w_prior_source_binding'),
        ('require_family_s_prior_scope', 'require_smooth_w_prior_scope'),
        ('retained_family_s_prior_target', 'retained_smooth_w_prior_target'),
        ('FAMILY_S_FAILED_WORD', 'SMOOTH_W_FAILED_ENDPOINT'), ('FAMILY_S_', 'SMOOTH_W_'),
        ('p15_S_original_accepted_owner_public_acceptance_v1', 'p15_W_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_S_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_W_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ("'current_read_live_source_count': 75, 'current_read_preserved_dependency_count': 74",
         "'current_read_live_source_count': 130, 'current_read_preserved_dependency_count': 129"),
        ('later_same_S_reuse_run', 'later_same_W_reuse_run'),
        ('Family@S', 'Smooth@W'), ('original S', 'original W'),
        ('original Family', 'original Smooth'), ('Family reuse', 'Smooth reuse'), ('later11', 'later8'),
    ]
    for before_text, after_text in replacements:
        need(before_text in adapter, 'missing adapter fragment: ' + before_text)
        adapter = adapter.replace(before_text, after_text)
    adapter = replace_once(adapter,
        "        'new_lean_acceptance': False, 'whole_P1_5_complete': False,\n",
        "        'new_lean_acceptance': False, 'whole_P1_5_complete': False,\n"
        "        'stock_readiness_executed_by_collector': False,\n"
        "        'later_same_source_reuse': SMOOTH_W_LATER_RECORD,\n")
    adapter = replace_once(adapter,
        "    later_run = base / 'runs/attempt-00001'\n",
        "    later_run = base / 'runs/attempt-00001'\n"
        "    require(retained_read(s, spec, later_run / 'executed-driver.py',\n"
        "            SMOOTH_W_LATER_PINS['executed-driver.py']) == published_binding(fixed['driver']),\n"
        "            'original W later executed driver differs')\n")
    adapter = replace_once(adapter,
        "                record['targets'] == SMOOTH_W_LATER_TARGETS and record['accepted_owners'] == [module] and\n",
        "                record['targets'] == SMOOTH_W_LATER_TARGETS and record['accepted_owners'] == [module] and\n"
        "                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and\n"
        "                set(record['direct_import_readiness']) == {SMOOTH_W_FAILED_ENDPOINT} and\n"
        "                all(record[key] is False for key in ('whole_P1_complete', 'accepted_supplier_recompile_requested',\n"
        "                    'dependency_rebuild_requested', 'old_receipts_rebound', 'old_P3_REUSE_changed')) and\n"
        "                not any(key in record for key in ('context_error', 'final_context_error', 'git_error')) and\n")
    constants = {'SMOOTH_W_MODULE': SMOOTH, 'SMOOTH_W_FAILED_ENDPOINT': ENDPOINT,
                 'SMOOTH_W_PRIOR_SOURCE_ANCHOR': V,
                 'SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS': {SMOOTH: prior},
                 'SMOOTH_W_PRIOR_RUNS': {SMOOTH: scope},
                 'SMOOTH_W_LATER_PINS': later_pins, 'SMOOTH_W_LATER_TARGETS': later['targets'],
                 'SMOOTH_W_LATER_RECORD': public['later_same_source_reuse']}
    inserted = '\n\n# Fixed Smooth@W acceptance; original W later8 remains partial.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        '} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS) | set(U_PREVIOUSLY_ACCEPTED_TARGETS),\n',
        '} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS) | set(U_PREVIOUSLY_ACCEPTED_TARGETS) | set(SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS),\n')
    code = replace_once(code,
        '    for module, prior in previous.items():\n        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:',
        '    for module, prior in previous.items():\n'
        '        if module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Smooth@W prior classification differs: ' + module)\n"
        '            smooth_w_prior_source_binding(s, graph, sources, module, prior)\n'
        '            continue\n'
        '        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:',
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in SMOOTH_W_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        '            retained_smooth_w_prior_target(s, spec, module)\n'
        '        elif module in U_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + V + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'V-anchored 21-root', 'X-anchored 21-root')
    code = replace_once(code, 'Family@S, Word@U and AllGroup@U\n', 'Family@S, Word@U, AllGroup@U and Smooth@W\n')
    manifest['source_anchor_commit'] = args.source_anchor
    row.update(**fp(source_raw), git_blob=hashlib.sha1(
        b'blob ' + str(len(source_raw)).encode() + b'\0' + source_raw).hexdigest())
    origin = manifest['target_source_origins'][ENDPOINT]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(source_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': args.repair_review_path, **fp(repair_raw)})
    manifest['previously_accepted_targets'][SMOOTH] = prior
    guide = manifest['selection_guidance']
    guide.update(minimum_first_targets=[ENDPOINT], minimum_first_source_count=110,
                 minimum_first_dependency_count=109, minimum_first_artifact_watch_module_count=130,
                 minimum_first_historical_supplier_count=0)
    guide['previously_accepted_not_compile_targets'].append(SMOOTH)
    guide['remaining_project_graph_unblocked_compile_candidates'].remove(SMOOTH)
    remaining = [m for m in guide['subsequent_8_targets'] if m != SMOOTH]
    guide.update(subsequent_7_targets=remaining, subsequent_7_source_count=157,
                 subsequent_7_dependency_count=150, subsequent_7_artifact_watch_module_count=160,
                 subsequent_7_historical_supplier_count=24)
    active = closure(graph, remaining)
    need(len(closure(graph, [ENDPOINT])) == 110 and
         len(closure(graph, [ENDPOINT]) | set(manifest['targets'])) == 130 and len(active) == 157 and
         len(active - set(remaining)) == 150 and len(active | set(manifest['targets'])) == 160 and
         len(active & (set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers']))) == 24 and
         ENDPOINT not in closure(graph, [SMOOTH]), 'Y source/own dependency scope differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. Endpoint first110/109 '
        'has no historical suppliers. Later7 closure157/150 includes all eleven prior targets and 24 historical '
        'supplier entries. Original W remaining7 has 23 because Smooth is still its current completed owner there. '
        'Smooth retains its W attempt-00000 acceptance with final stock and unchanged reuse in partial W attempt-00001; '
        'Endpoint failed and six following targets were unstarted. Both original run contexts, executed drivers and '
        'six Smooth receipts remain fixed; the previous ten priors are unchanged. Old subsequent8/10/11/13/14/15 '
        'guidance remains historical. No prior is selected or rebound. The source installer is separate.')
    need({k: v for k, v in manifest['project_sources'].items() if k != ENDPOINT} ==
         {k: v for k, v in before_manifest['project_sources'].items() if k != ENDPOINT} and
         all(manifest['project_sources'][m][k] == row[k] for m, row in before_manifest['project_sources'].items()
             for k in ('imports', 'all_imports')), 'unrelated source/import change')
    need({k: v for k, v in manifest['target_source_origins'].items() if k != ENDPOINT} ==
         {k: v for k, v in before_manifest['target_source_origins'].items() if k != ENDPOINT},
         'unrelated source origin changed')
    need({k: v for k, v in manifest['previously_accepted_targets'].items() if k != SMOOTH} ==
         before_manifest['previously_accepted_targets'], 'ten prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(manifest[key] == before_manifest[key], 'old policy changed: ' + key)
    mr = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + W_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if old_functions[name] != new_functions[name]}
    added = set(new_functions) - set(old_functions)
    need(changed == {'source_manifest', 'preflight'} and added ==
         {'smooth_w_prior_source_binding', 'require_smooth_w_prior_scope', 'retained_smooth_w_prior_target'},
         'unexpected existing/new function changes')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': mr,
                      'smooth_w_prior_adapter.py': inserted.encode()}.items():
        (args.output / name).write_bytes(raw)
    report = {'schema': 'p15_X_source_Smooth_W_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'adapter': fp(inserted.encode()),
              'original_W_function_count': len(old_functions), 'unchanged_W_functions': len(old_functions) - 2,
              'changed_functions': sorted(changed), 'new_functions': sorted(added),
              'ten_prior_identities_unchanged': True, 'other_359_sources_all_imports_303_19_policy_unchanged': True,
              'actual_W_public': fp(public_raw), 'actual_W_acceptance_read': fp(read_raw),
              'Endpoint_repair': {'source': fp(source_raw), 'review': fp(repair_raw), 'splices': len(repair['splices'])},
              'first': {'sources': 110, 'dependencies': 109, 'watch_modules': 130, 'historical_suppliers': 0},
              'later7': {'sources': 157, 'dependencies': 150, 'watch_modules': 160, 'historical_suppliers': 24},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (args.output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
