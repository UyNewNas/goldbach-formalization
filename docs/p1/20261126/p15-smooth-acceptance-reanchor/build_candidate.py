#!/usr/bin/env python3
"""Append fixed Word/AllGroup@U priors; bind only the Smooth repair to V.

Local generation only. No compiler, remote invocation, or canonical file writes.
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
BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
U = '2779eb7b2b0433bea10d523ef976317893f8429d'
T = '999510c460e6e026c8cabe46c5f35876f7201f8e'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
ALLGROUP = 'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'
SMOOTH = 'ImbalancedChen.P1OriginalSingletonSmoothLicence'
PUBLIC_PREFIX = 'docs/p1/20261125/p15-current-public-acceptance/'
REPAIR_PATH = 'docs/p1/20261126/p15-smooth-first-compile-repair/REPAIR_CANDIDATE.json'
DRIVER_PATH = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST_PATH = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
EVIDENCE = '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1'
OUT = Path('/tmp/p15-entrypoint-w')
U_DRIVER = {'bytes': 152370, 'sha256': '9d9c2e467b3fd6271b7b0101812094ca6ff768f1ea831812b6de4c95a0dd9c7a'}
U_MANIFEST = {'bytes': 349643, 'sha256': 'ae3f6bb915e0ed2dc799fd6bfed2b906aab3efac3df9186c9c1d54da4b53a1af'}
PUBLIC_FILES = {
    WORD: ('WORD_U_PUBLIC_ACCEPTANCE.json',
           {'bytes': 13061, 'sha256': 'efa15b29f13cdef9ede740c4fc66f1c810ae1136f284f003d3c1df5f30fb7d03'}),
    ALLGROUP: ('ALLGROUP_U_PUBLIC_ACCEPTANCE.json',
               {'bytes': 8771, 'sha256': '40813f4ab82bb3751834fbbd29bfecf9aa79f109e875db4a430be0799cb91b83'}),
}


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(value):
    return {key: value[key] for key in ('bytes', 'sha256')}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def functions(text):
    return {node.name: ast.get_source_segment(text, node)
            for node in ast.parse(text).body if isinstance(node, ast.FunctionDef)}


def replace_once(text, before, after):
    need(text.count(before) == 1, 'nonunique generation splice: ' + before[:160])
    return text.replace(before, after)


def closure(graph, modules):
    pending, seen = list(modules), set()
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-anchor', required=True)
    parser.add_argument('--actual-dir', type=Path, default=Path('/tmp/p15-u-actual'))
    parser.add_argument('--repair-source', type=Path,
                        default=Path('/tmp/p15-smooth-repair/P1OriginalSingletonSmoothLicence.lean'))
    parser.add_argument('--repair-candidate', type=Path,
                        default=Path('/tmp/p15-smooth-repair/REPAIR_CANDIDATE.json'))
    parser.add_argument('--output', type=Path, default=OUT)
    args = parser.parse_args()
    need(__debug__ and re.fullmatch('[0-9a-f]{40}', args.source_anchor), 'exact source anchor required')
    need(args.source_anchor not in (T, U), 'V must retain its own publication identity')
    output = args.output.resolve()
    need(output == args.output and output.is_relative_to(Path('/tmp')), 'local /tmp output required')
    old = (BASE / 'entrypoint-u/run_selected.py').read_bytes()
    old_manifest = Path('/tmp/p15-entrypoint-u/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == U_DRIVER and fp(old_manifest) == U_MANIFEST, 'frozen U runner/manifest differs')
    m = json.loads(old_manifest)
    original_manifest = copy.deepcopy(m)
    graph = {module: row['imports'] for module, row in m['project_sources'].items()}
    need(m['source_anchor_commit'] == T and len(graph) == 360 and
         len(m['previously_accepted_targets']) == 8, 'original U inventory differs')
    metadata = json.loads((args.actual_dir / 'ACTUAL_U_METADATA.json').read_bytes())
    collection_raw = (args.actual_dir / 'ACTUAL_U_ACCEPTANCE_READ.json').read_bytes()
    collection = json.loads(collection_raw)
    need(metadata['source_commit'] == collection['source_commit'] == U and
         collection['source_anchor_commit'] == T and
         collection['selected_owners_revalidated'] == [WORD, ALLGROUP] and
         collection['current_read_live_source_count'] == 139 and
         collection['current_read_preserved_dependency_count'] == 137 and
         collection['normal_or_kernel_commands_executed'] == 0 and
         collection['new_lean_acceptance'] is False and collection['whole_P1_5_complete'] is False,
         'actual U collector identity/scope differs')
    publics, priors, scopes, actual_results = {}, {}, {}, {}
    for index, module in enumerate((WORD, ALLGROUP)):
        filename, expected = PUBLIC_FILES[module]
        raw = (args.actual_dir / filename).read_bytes()
        public = json.loads(raw)
        need(fp(raw) == expected and
             public == collection['public_summaries'][filename.removesuffix('.json')],
             'frozen actual U public summary differs: ' + module)
        owner = public['owners'][module]
        run = 'runs/attempt-%05d' % index
        need(public['source_commit'] == U and public['source_anchor_commit'] == T and
             public['original_run'] == run and set(public['owners']) == {module} and
             public['driver'] == {'commit': U, 'path': DRIVER_PATH, **U_DRIVER} and
             public['source_manifest'] == {'commit': U, 'path': MANIFEST_PATH, **U_MANIFEST} and
             (owner['owned_count'], owner['public_count']) == (15, 15) and
             owner['source_sha256'] == m['project_sources'][module]['sha256'] and
             owner['owner_live_source_closure_count'] == len(closure(graph, [module])) == (77 if index == 0 else 139),
             'U owner/driver/source/own closure differs')
        actual_raw = (args.actual_dir / ('attempt-%05d-RESULT.json' % index)).read_bytes()
        actual = json.loads(actual_raw)
        worker = {key: value for key, value in actual.items()
                  if key not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        worker_raw = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        pins = metadata['runs']['attempt-%05d' % index]
        need(fp(actual_raw) == public['original_result'] == pin(pins['RESULT.json']) and
             fp(worker_raw) == public['original_worker_result'] == pin(pins['WORKER_RESULT.json']),
             'actual RESULT/byte-exact reconstructed WORKER pins differ')
        for stem in ('CONTEXT', 'GIT'):
            pair = public['original_context_pairs'][stem]
            need(pair['before'] == pair['after'] == pin(pins[stem + '_BEFORE.json']) ==
                 pin(pins[stem + '_AFTER.json']), 'U context/Git original pins differ')
        fixed = {'source_commit': U, 'compiler_job': public['compiler_job'],
                 'evidence_root': EVIDENCE, 'run': run, 'owners': [module],
                 'driver': public['driver'], 'source_graph': public['source_manifest'],
                 'published_source_count': 360,
                 'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC_PREFIX + filename, **expected},
                 'evidence_kind': 'bounded_public_acceptance'}
        priors[module] = {'group': 'word_u' if index == 0 else 'allgroup_u', 'source_commit': U,
                         'source_sha256': owner['source_sha256'],
                         'live_source_closure_count': owner['owner_live_source_closure_count'],
                         'historical_group': fixed, 'owned_count': 15, 'public_count': 15,
                         'audit_id': owner['audit_id']}
        scopes[module] = {
            'targets': public['original_targets'], 'accepted': public['original_group_accepted_owners'],
            'reused': public['original_group_reused_complete_selected_owners'],
            'failed': public['original_group_failed_modules'],
            'not_accepted': public['original_group_not_accepted_modules'],
            'not_started': public['original_group_not_started_modules'],
            'readiness': list(actual['direct_import_readiness']),
            'exit_code': public['original_group_worker_exit_code'],
            'live_count': public['original_group_live_closure_count'],
            'result': public['original_result'], 'worker': public['original_worker_result'],
            'requested_targets': public['original_requested_targets'],
            'context_pairs': public['original_context_pairs'],
            'receipt_bindings': owner['receipt_bindings'], 'source': owner['source'],
            'failure_messages': actual['failures'],
        }
        publics[module], actual_results[module] = public, actual
    first, later = actual_results[WORD], actual_results[ALLGROUP]
    need(first['targets'] == first['accepted_owners'] == [WORD] and first['failures'] == {} and
         first['reused_complete_selected_owners'] == [] and first['worker_exit_code'] == 0 and
         first['all_selected_owners_accepted'] is True and first['final_stock_readiness']['exit_code'] == 0 and
         later['targets'][:3] == [WORD, ALLGROUP, SMOOTH] and len(later['targets']) == 10 and
         later['accepted_owners'] == [WORD, ALLGROUP] and later['reused_complete_selected_owners'] == [WORD] and
         later['failures'] == {SMOOTH: 'normal failed/scope differs: ' + SMOOTH} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['acceptance_bindings'][WORD] == first['acceptance_bindings'][WORD] and
         scopes[ALLGROUP]['not_started'] == later['targets'][3:] and len(scopes[ALLGROUP]['not_started']) == 7 and
         scopes[WORD]['live_count'] == 77 and scopes[ALLGROUP]['live_count'] == 157,
         'fixed first Word / partial AllGroup run identities differ')
    later_reuse = publics[WORD]['later_same_source_reuse']
    need(later_reuse == collection['original_runs'][1] and
         publics[ALLGROUP]['later_same_source_reuse'] is None, 'original Word later reuse record differs')
    repair_raw, smooth_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    source_path = m['project_sources'][SMOOTH]['path']
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / source_path).read_bytes()
    need(repair['source_base_commit'] == U and repair['source'] == source_path and
         fp(before) == repair['before'] == pin(m['project_sources'][SMOOTH]) and fp(smooth_raw) == repair['after'] and
         repair['schema'] == 'p15_smooth_licence_five_proof_splices_candidate_v1' and len(repair['splices']) == 5 and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['axioms_or_sorry_added'] is False and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe']['exit_code'] == 0 and repair['earlier_probe_failure']['exit_code'] == 1 and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'current five-splice Smooth repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'Smooth splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode()))
        end = stop
    need(b''.join(pieces) + before[end:] == smooth_raw and
         re.findall(r'^import\s+(\S+)\s*$', smooth_raw.decode(), re.M) == m['project_sources'][SMOOTH]['all_imports'],
         'Smooth repair changes bytes outside five splices or imports')

    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
                           ('q_prior_source_binding', 'require_q_prior_scope', 'retained_q_prior_target'))
    for before_text, after_text in (
        ('q_prior_source_binding', 'u_prior_source_binding'),
        ('require_q_prior_scope', 'require_u_prior_scope'),
        ('retained_q_prior_target', 'retained_u_prior_target'),
        ('Q_PREVIOUSLY_ACCEPTED_TARGETS', 'U_PREVIOUSLY_ACCEPTED_TARGETS'),
        ('Q_PRIOR_SOURCE_ANCHOR', 'U_PRIOR_SOURCE_ANCHOR'),
        ('Q_PRIOR_RUNS', 'U_PRIOR_RUNS'), ('Q_ALLK_MODULE', 'U_WORD_MODULE'),
        ('p15_Q_original_accepted_owner_public_acceptance_v1', 'p15_U_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_Q_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_U_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ("'current_read_live_source_count': 74, 'current_read_preserved_dependency_count': 72",
         "'current_read_live_source_count': 139, 'current_read_preserved_dependency_count': 137"),
        ('later_same_Q_reuse_run', 'later_same_U_reuse_run'),
        ('fixed Q', 'fixed U'), ('original Q', 'original U'), ('Q prior', 'U prior'),
        ('accepted Q owner', 'accepted U owner'), ('original AllK', 'original Word'),
        ('Q public', 'U public'), ('later13', 'later10'),
    ):
        need(before_text in adapter, 'adapter source fragment absent: ' + before_text)
        adapter = adapter.replace(before_text, after_text)
    adapter = replace_once(adapter,
        "        'new_lean_acceptance': False, 'whole_P1_5_complete': False,\n",
        "        'new_lean_acceptance': False, 'whole_P1_5_complete': False,\n"
        "        'stock_readiness_executed_by_collector': False,\n"
        "        'later_same_source_reuse': U_PRIOR_LATER_REUSE if module == U_WORD_MODULE else None,\n")
    adapter = replace_once(adapter,
        "    receipts = owner['receipt_bindings']\n",
        "    receipts = owner['receipt_bindings']\n"
        "    require(receipts == run_scope['receipt_bindings'] and owner['source'] == run_scope['source'] and\n"
        "            public['original_context_pairs'] == run_scope['context_pairs'],\n"
        "            'fixed U six-receipt/source/context pins differ: ' + module)\n")
    adapter = replace_once(adapter,
        "record['accepted_owners'] == run_scope['accepted'] and set(record['failures']) == set(run_scope['failed']) and",
        "record['accepted_owners'] == run_scope['accepted'] and record['failures'] == run_scope['failure_messages'] and")
    adapter = replace_once(adapter,
        "            all(original[key] == worker[key] for key in ('targets', 'accepted_owners', 'failures',\n"
        "                'acceptance_bindings', 'direct_import_readiness', 'original_supplier_acceptance_bindings')),",
        "            all(original.get(key) == value for key, value in worker.items()),")
    start = adapter.index("    fixed, run_scope = prior['historical_group'], U_PRIOR_RUNS[module]\n",
                          adapter.index('def retained_u_prior_target'))
    stop = adapter.index("    binding = original['acceptance_bindings'][module]\n", start)
    prefix = """    records = {}
    # Read both fixed original runs; only the requested active owner is audited below.
    for prior_module, fixed_prior in U_PREVIOUSLY_ACCEPTED_TARGETS.items():
        fixed = fixed_prior['historical_group']
        scope = U_PRIOR_RUNS[prior_module]
        public = json.loads(published_binding(fixed['public_evidence']))
        base = Path(fixed['evidence_root']) / fixed_prior['source_commit']
        run = base / fixed['run']
        original = json.loads(retained_read(s, spec, run / 'RESULT.json', scope['result']))
        worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', scope['worker']))
        require_u_prior_scope(prior_module, fixed_prior, public, original, worker)
        require(retained_read(s, spec, run / 'executed-driver.py',
                {key: fixed['driver'][key] for key in ('bytes', 'sha256')}) == published_binding(fixed['driver']),
                'original U executed driver differs: ' + prior_module)
        for stem, pair in scope['context_pairs'].items():
            require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                    retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                    'original U context/Git pair differs: ' + prior_module)
        records[prior_module] = (public, original, worker, run)
    first_public, first, _, first_run = records[U_WORD_MODULE]
    later = records[U_ALLGROUP_MODULE][1]
    require(later['acceptance_bindings'][U_WORD_MODULE] == first['acceptance_bindings'][U_WORD_MODULE],
            'later10 reused Word binding differs from its first U acceptance')
    stock, public_stock = first['final_stock_readiness'], first_public['original_final_stock_readiness']
    command = json.loads(retained_read(s, spec, first_run / 'final-stock-readiness-command.json',
                                     {key: public_stock['command'][key] for key in ('bytes', 'sha256')}))
    require(command == stock and stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + U_WORD_MODULE + ':olean']) and
            stock['cwd'] == str(PROJECT) and stock['log'] == str(first_run / 'final-stock-readiness.log') and
            {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']} ==
                {key: public_stock['log'][key] for key in ('bytes', 'sha256')},
            'original Word guarded final stock command/log binding differs')
    retained_read(s, spec, Path(stock['log']), {key: public_stock['log'][key] for key in ('bytes', 'sha256')})
    public, original, worker, run = records[module]
    fixed, run_scope = prior['historical_group'], U_PRIOR_RUNS[module]
"""
    adapter = adapter[:start] + prefix + adapter[stop:]
    constants = {'U_WORD_MODULE': WORD, 'U_ALLGROUP_MODULE': ALLGROUP,
                 'U_PRIOR_SOURCE_ANCHOR': T, 'U_PREVIOUSLY_ACCEPTED_TARGETS': priors,
                 'U_PRIOR_RUNS': scopes, 'U_PRIOR_LATER_REUSE': later_reuse}
    inserted = '\n\n# Fixed original Word/AllGroup@U receipts; the partial U run remains failed.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **U_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        "} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS),\n",
        "} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS) | set(U_PREVIOUSLY_ACCEPTED_TARGETS),\n")
    code = replace_once(code,
        "    for module, prior in previous.items():\n        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:",
        "    for module, prior in previous.items():\n"
        "        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:\n"
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'U prior classification differs: ' + module)\n"
        "            u_prior_source_binding(s, graph, sources, module, prior)\n"
        "            continue\n"
        "        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:")
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        "        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:",
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        "        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:\n"
        "            retained_u_prior_target(s, spec, module)\n"
        "        elif module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:")
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + T + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'T-anchored 21-root', 'V-anchored 21-root')
    code = replace_once(code, 'AllK@Q, Admissible@Q and Family@S\n',
                        'AllK@Q, Admissible@Q, Family@S, Word@U and AllGroup@U\n')

    m['source_anchor_commit'] = args.source_anchor
    row = m['project_sources'][SMOOTH]
    row.update(**fp(smooth_raw),
               git_blob=hashlib.sha1(b'blob ' + str(len(smooth_raw)).encode() + b'\0' + smooth_raw).hexdigest())
    origin = m['target_source_origins'][SMOOTH]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(smooth_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': REPAIR_PATH, **fp(repair_raw)})
    m['previously_accepted_targets'].update(priors)
    guide = m['selection_guidance']
    remaining = later['targets'][2:]
    active = closure(graph, remaining)
    first_active = closure(graph, [SMOOTH])
    watch = active | set(m['targets'])
    need(len(remaining) == 8 and len(active) == 157 and len(watch) == 160 and len(first_active) == 130 and
         not active.intersection(m['unaccepted_p3_dependencies']), 'W first/remaining source closure differs')
    guide.update(minimum_first_targets=[SMOOTH], minimum_first_source_count=130, minimum_first_dependency_count=129)
    guide['previously_accepted_not_compile_targets'].extend([WORD, ALLGROUP])
    guide['remaining_project_graph_unblocked_compile_candidates'] = [
        module for module in guide['remaining_project_graph_unblocked_compile_candidates'] if module not in priors]
    guide.update(subsequent_8_targets=remaining, subsequent_8_source_count=157, subsequent_8_dependency_count=149,
                 subsequent_8_artifact_watch_module_count=160)
    historical = set(m['previously_accepted_targets']) | set(m['accepted_suppliers'])
    guide['minimum_first_historical_supplier_count'] = len(first_active & historical)
    guide['subsequent_8_historical_supplier_count'] = len(active & historical)
    need(guide['subsequent_8_historical_supplier_count'] == 23, 'W historical supplier count differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. Smooth first130/129 '
        'reuses HB@F and Licensed@M; later8 closure157/149 includes all ten prior targets, with 23 historical supplier '
        'evidence entries. Original U remaining8 preflight has 21 historical supplier entries because Word/AllGroup '
        'are still original U current owners there. Word@U keeps successful attempt-00000, final stock, and unchanged '
        'reuse in partial attempt-00001; AllGroup@U keeps its first acceptance in that partial attempt-00001. '
        'Smooth failed and seven targets were unstarted in that original U run. Both original run RESULT/WORKER, '
        'executed driver and CONTEXT/GIT pairs remain pinned. All earlier eight priors are unchanged; old '
        'subsequent10/11/13/14/15 guidance is historical. No prior receipt is rebound; the source installer is separate.')
    need({k: v for k, v in m['project_sources'].items() if k != SMOOTH} ==
         {k: v for k, v in original_manifest['project_sources'].items() if k != SMOOTH},
         'unrelated source row changed')
    need(all(m['project_sources'][key][field] == value[field]
             for key, value in original_manifest['project_sources'].items() for field in ('imports', 'all_imports')),
         'project imports changed')
    need({k: v for k, v in m['target_source_origins'].items() if k != SMOOTH} ==
         {k: v for k, v in original_manifest['target_source_origins'].items() if k != SMOOTH},
         'unrelated source provenance changed')
    need({k: v for k, v in m['previously_accepted_targets'].items() if k not in priors} ==
         original_manifest['previously_accepted_targets'], 'eight old prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(m[key] == original_manifest[key], 'original policy changed: ' + key)
    manifest_raw = (json.dumps(m, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + U_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(manifest_raw)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if new_functions[name] != old_functions[name]}
    need(changed == {'source_manifest', 'preflight'} and
         set(new_functions) - set(old_functions) ==
         {'u_prior_source_binding', 'require_u_prior_scope', 'retained_u_prior_target'},
         'unexpected function addition/change')
    output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': manifest_raw,
                      'u_prior_adapter.py': inserted.encode()}.items():
        (output / name).write_bytes(raw)
    report = {'schema': 'p15_V_source_Word_AllGroup_U_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(manifest_raw), 'adapter': fp(inserted.encode()),
              'original_U_runner': U_DRIVER, 'original_U_manifest': U_MANIFEST,
              'original_U_function_count': len(old_functions), 'unchanged_U_functions': len(old_functions) - 2,
              'changed_functions': sorted(changed), 'new_functions': sorted(set(new_functions) - set(old_functions)),
              'other_359_sources_and_all_imports_unchanged': True, 'eight_prior_identities_unchanged': True,
              'fixed_303_policies_and_19_P3_hardstop_unchanged': True,
              'Smooth_repair': {'source': fp(smooth_raw), 'review': fp(repair_raw), 'splices': 5},
              'actual_U_collector': fp(collection_raw),
              'actual_U_public_inputs': {name: binding for name, binding in PUBLIC_FILES.values()},
              'first': {'targets': [SMOOTH], 'sources': 130, 'dependencies': 129,
                        'historical_suppliers': guide['minimum_first_historical_supplier_count']},
              'later': {'targets': remaining, 'sources': 157, 'dependencies': 149, 'watch_modules': 160,
                        'historical_suppliers': 23},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
