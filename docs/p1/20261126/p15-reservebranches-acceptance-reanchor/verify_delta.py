#!/usr/bin/env python3
"""Exact local AE -> AG text/manifest comparison; no cloud/runtime work."""
from pathlib import Path
import ast
import hashlib
import json
import re

ROOT = Path('/tmp/p15-entrypoint-ag')
OLD = Path('/tmp/p15-entrypoint-ae')
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'
L = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
A = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
R = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
P = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def funcs(text):
    return {n.name: ast.get_source_segment(text, n)
            for n in ast.parse(text).body if isinstance(n, ast.FunctionDef)}


def once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('nonunique preservation splice: ' + before[:100])
    return text.replace(before, after)


def save(name, data):
    raw = (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / name).write_bytes(raw)
    return fp(raw)


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        m = pending.pop()
        if m not in seen:
            seen.add(m); pending.extend(graph[m])
    return seen


old_raw, new_raw = (OLD / 'run_selected.py').read_bytes(), (ROOT / 'run_selected.py').read_bytes()
old_text, new_text = old_raw.decode(), new_raw.decode()
old_functions, new_functions = funcs(old_text), funcs(new_text)
changed = sorted(n for n in old_functions if old_functions[n] != new_functions[n])
added = sorted(set(new_functions) - set(old_functions))
unchanged = sorted(n for n in old_functions if old_functions[n] == new_functions[n])
assert len(old_functions) == 64 and len(new_functions) == 67 and len(unchanged) == 62
assert changed == ['preflight', 'source_manifest']
assert added == ['ae_prior_source_binding', 'require_ae_prior_scope', 'retained_ae_prior_target']
restored_manifest_function = once(new_functions['source_manifest'], ' | set(AE_PREVIOUSLY_ACCEPTED_TARGETS)', '')
restored_manifest_function = once(restored_manifest_function,
    '        if module in AE_PREVIOUSLY_ACCEPTED_TARGETS:\n'
    "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
    "                    'AE dual-owner prior classification differs: ' + module)\n"
    '            ae_prior_source_binding(s, graph, sources, module, prior)\n'
    '            continue\n', '')
restored_preflight = once(new_functions['preflight'],
    '        if module in AE_PREVIOUSLY_ACCEPTED_TARGETS:\n'
    '            retained_ae_prior_target(s, spec, module)\n'
    '        elif module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:',
    '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:')
assert restored_manifest_function == old_functions['source_manifest']
assert restored_preflight == old_functions['preflight']

# Invert only the fixed names, labels, and the actual joint read scope. This
# restores the original U functions exactly, independently of builder execution.
body = '\n\n\n'.join(new_functions[n] for n in added)
assert body + '\n' == (ROOT / 'ae_prior_adapter.py.in').read_text()
inverse = [
    ('ae_prior_source_binding', 'u_prior_source_binding'),
    ('require_ae_prior_scope', 'require_u_prior_scope'),
    ('retained_ae_prior_target', 'retained_u_prior_target'),
    ('AE_LOWERTRIM_MODULE', 'U_WORD_MODULE'), ('AE_ATLASTRIM_MODULE', 'U_ALLGROUP_MODULE'),
    ('p15_AE_original_accepted_owner_public_acceptance_v1', 'p15_U_original_accepted_owner_public_acceptance_v1'),
    ('ORIGINAL_AE_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_U_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
    ('later_same_AE_reuse_run', 'later_same_U_reuse_run'), ('AE_', 'U_'),
    ("'current_read_live_source_count': 153, 'current_read_preserved_dependency_count': 151",
     "'current_read_live_source_count': 139, 'current_read_preserved_dependency_count': 137"),
    ('LowerTrim', 'Word'), ('later4', 'later10'),
]
restored_u = body
for before, after in inverse:
    assert before in restored_u
    restored_u = restored_u.replace(before, after)
restored_u = re.sub(r'\bAE\b', 'U', restored_u)
assert restored_u == '\n\n\n'.join(old_functions[n] for n in
    ('u_prior_source_binding', 'require_u_prior_scope', 'retained_u_prior_target'))

adapter = (ROOT / 'ae_prior_adapter.py').read_text()
restored = once(new_text, adapter, '')
for name in changed:
    restored = once(restored, new_functions[name], old_functions[name])
restored = once(restored, 'AF-anchored 21-root', 'AD-anchored 21-root')
restored = once(restored, 'Mean@AA, Synthesis@AC, LowerTrim@AE and AtlasTrim@AE\n', 'Mean@AA and Synthesis@AC\n')
restored = once(restored, "\nSOURCE_ANCHOR = '" + AF + "'", "\nSOURCE_ANCHOR = '" + AD + "'")
old_manifest_raw = (OLD / 'SOURCE_MANIFEST.json').read_bytes()
manifest_raw = (ROOT / 'SOURCE_MANIFEST.json').read_bytes()
restored = once(restored, "MANIFEST_SHA = '" + fp(manifest_raw)['sha256'] + "'",
                "MANIFEST_SHA = '" + fp(old_manifest_raw)['sha256'] + "'")
assert restored.encode() == old_raw
ast_pin = save('AST_DELTA.json', {
    'schema': 'p15_AG_AE_exact_function_delta_v1', 'old_commit': AE, 'source_anchor': AF,
    'old_runner': fp(old_raw), 'new_runner': fp(new_raw),
    'old_function_count': 64, 'new_function_count': 67,
    'unchanged_function_count': 62, 'unchanged_functions': unchanged,
    'changed_functions': changed, 'added_functions': added,
    'source_manifest_only_new_prior_union_and_branch': True,
    'preflight_only_new_prior_dispatch': True,
    'new_three_functions_reverse_exactly_to_original_U_control_flow': True,
    'whole_runner_reverse_to_exact_AE_bytes': True,
    'other_allowed_text_changes': ['two new fixed AE prior mappings and three-function adapter',
        'source anchor AD to AF', 'manifest fingerprint', 'two introductory documentation strings'],
    'old_function_execution_performed_by_this_verifier': False,
})

old_m, new_m = json.loads(old_manifest_raw), json.loads(manifest_raw)
changed_top = sorted(k for k in old_m if old_m[k] != new_m[k])
assert set(old_m) == set(new_m)
assert set(changed_top) == {'source_anchor_commit', 'project_sources', 'target_source_origins',
                            'previously_accepted_targets', 'selection_guidance'}
assert new_m['source_anchor_commit'] == AF
changed_sources = [m for m in old_m['project_sources']
                   if old_m['project_sources'][m] != new_m['project_sources'][m]]
assert changed_sources == [R]
changed_fields = sorted(k for k in old_m['project_sources'][R]
                        if old_m['project_sources'][R][k] != new_m['project_sources'][R][k])
assert changed_fields == ['bytes', 'git_blob', 'sha256']
assert all(old_m['project_sources'][m][k] == new_m['project_sources'][m][k]
           for m in old_m['project_sources'] for k in ('imports', 'all_imports'))
changed_origins = [m for m in old_m['target_source_origins']
                   if old_m['target_source_origins'][m] != new_m['target_source_origins'][m]]
assert changed_origins == [R]
assert len(old_m['previously_accepted_targets']) == 14 and len(new_m['previously_accepted_targets']) == 16
assert {m: row for m, row in new_m['previously_accepted_targets'].items() if m not in (L, A)} == old_m['previously_accepted_targets']
new_priors = {m: new_m['previously_accepted_targets'][m] for m in (L, A)}
for index, module in enumerate((L, A)):
    prior = new_priors[module]
    assert prior['source_commit'] == AE and prior['historical_group']['run'] == 'runs/attempt-%05d' % index
    assert prior['historical_group']['public_evidence']['commit'] == AF
policies = ['fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
            'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review']
assert all(old_m[k] == new_m[k] for k in policies)
assert (len(new_m['project_sources']), len(new_m['fixed_dependencies']), len(new_m['unaccepted_p3_dependencies'])) == (360, 303, 19)
graph = {m: row['imports'] for m, row in new_m['project_sources'].items()}
historical = set(new_m['previously_accepted_targets']) | set(new_m['accepted_suppliers'])
scopes = {}
for label, selected, expected in [('first', [R], (140, 139, 152, 21)), ('later2', [R, P], (144, 142, 152, 24))]:
    active = closure(graph, selected)
    actual_scope = (len(active), len(active - set(selected)), len(active | set(new_m['targets'])), len(active & historical))
    assert actual_scope == expected and not active & {L, A}
    scopes[label] = dict(zip(('sources', 'dependencies', 'watch_modules', 'historical_suppliers'), actual_scope))
    scopes[label]['new_AE_priors_active'] = []
assert len(closure(graph, [L])) == 119 and len(closure(graph, [A])) == 153
assert len(closure(graph, [L, A]) - {L, A}) == 151
packet = json.loads(Path('/tmp/p15-af-publication/publication_packet.json').read_text())
elements = {r['path']: r['content'].encode() for r in packet['elements']}
inventory = {r['path']: {k: r[k] for k in ('bytes', 'sha256')} for r in packet['inventory']}
bindings = {
    'ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.lean': Path('/tmp/p15-reservebranches-repair/P5OriginalPrimeAtlasReserveBranches.lean'),
    'docs/p1/20261126/p15-reservebranches-first-compile-repair/REPAIR_CANDIDATE.json': Path('/tmp/p15-reservebranches-repair/REPAIR_CANDIDATE.json'),
    'docs/p1/20261125/p15-current-public-acceptance/LOWERTRIM_AE_PUBLIC_ACCEPTANCE.json': Path('/tmp/p15-ae-actual/LOWERTRIM_AE_PUBLIC_ACCEPTANCE.json'),
    'docs/p1/20261125/p15-current-public-acceptance/ATLASTRIM_AE_PUBLIC_ACCEPTANCE.json': Path('/tmp/p15-ae-actual/ATLASTRIM_AE_PUBLIC_ACCEPTANCE.json'),
}
for path, local in bindings.items():
    assert elements[path] == local.read_bytes() and fp(elements[path]) == inventory[path]
guide_delta = sorted(k for k in set(old_m['selection_guidance']) | set(new_m['selection_guidance'])
                     if old_m['selection_guidance'].get(k) != new_m['selection_guidance'].get(k))
manifest_pin = save('MANIFEST_DELTA.json', {
    'schema': 'p15_AG_AE_exact_manifest_delta_v1', 'old_commit': AE, 'source_anchor': AF,
    'old_manifest': fp(old_manifest_raw), 'new_manifest': fp(manifest_raw),
    'changed_top_level_keys': changed_top, 'changed_source_modules': changed_sources,
    'changed_source_fields': changed_fields, 'changed_source_origins': changed_origins,
    'all_360_import_lists_unchanged': True, 'other_359_source_rows_unchanged': True,
    'old_14_priors_exactly_unchanged': True, 'new_priors': new_priors,
    'unchanged_policy_keys': policies, 'fixed_dependencies': 303, 'unaccepted_P3_dependencies_held': 19,
    'selection_guidance_changed_keys': guide_delta, 'actual_selection_scopes': scopes,
    'joint_AE_read_scope': {'sources': 153, 'preserved_dependencies': 151},
    'own_closures': {L: 119, A: 153},
    'relevant_local_AF_packet_content_and_inventory_match': {p: inventory[p] for p in bindings},
    'Git_readback_by_this_verifier': False,
})
log = (ROOT / 'TEST_RESULTS.log').read_bytes()
assert b'Ran 7 tests' in log and log.rstrip().endswith(b'OK')
report = {
    'schema': 'p15_AG_new_dual_AE_prior_local_verification_v1',
    'status': 'SEVEN_TARGETED_DUAL_PRIOR_TESTS_PASS_AND_EXACT_DELTA_CONFIRMED',
    'source_anchor': AF, 'original_AE_acceptance_source': AE,
    'runner': fp(new_raw), 'manifest': fp(manifest_raw), 'adapter': fp(adapter.encode()),
    'tests': {'count': 7, 'exit_code': 0, 'log': fp(log),
              'script': fp((ROOT / 'test_new_adapter.py').read_bytes())},
    'ast_delta': ast_pin, 'manifest_delta': manifest_pin, 'next_selection_scopes': scopes,
    'test_scope': ['both actual owners: LowerTrim10/10/run0/119 and AtlasTrim11/9/run1/153',
        'both original RESULT/WORKER pins and original supplier counts3/27; fixed six-receipt/context mutation rejection',
        'source/own closures, selection rejection and actual inactive next-selection guard before IO',
        'joint153/151 identity separate from original119/157 and own119/153; count/path/reuse-field mutation rejection',
        'successful first final stock versus partial later failure/no final stock',
        'read both fixed original runs while auditing only the requested active owner',
        'cross-run reused LowerTrim binding, original pin arguments, source+5 and full21 mutation rejection'],
    'mock_limit': 'Control-flow fixtures use actual public/RESULT data but explicitly mock unavailable context/stock command/log bytes and generic audit IO. They check original pin arguments and parsed identities, not new runtime or Lean acceptance.',
    'old_fixture_suites_rerun': False, 'cloud_commands_executed': 0,
    'Git_operations_executed': 0, 'Lean_commands_executed': 0,
    'new_lean_acceptance': False, 'whole_P1_5_complete': False,
}
save('LOCAL_VERIFICATION.json', report)
print(json.dumps({'status': report['status'], 'unchanged_AE_functions': 62,
                  'old_priors_unchanged': 14, 'source_rows_unchanged': 359,
                  'U_control_flow_preserved': True, 'tests': 7, 'source_anchor': AF}, sort_keys=True))
