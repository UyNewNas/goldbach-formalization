#!/usr/bin/env python3
"""Compare the fixed AC and AC source texts and manifests without runtime work."""
from pathlib import Path
import ast
import hashlib
import json

ROOT = Path('/tmp/p15-entrypoint-ae')
OLD = Path('/tmp/p15-entrypoint-ac')
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AB = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def funcs(text):
    return {n.name: ast.get_source_segment(text, n)
            for n in ast.parse(text).body if isinstance(n, ast.FunctionDef)}


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('nonunique preservation splice: ' + before[:90])
    return text.replace(before, after)


def save(name, data):
    raw = (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()
    (ROOT / name).write_bytes(raw)
    return fp(raw)


old_raw, new_raw = (OLD / 'run_selected.py').read_bytes(), (ROOT / 'run_selected.py').read_bytes()
old_text, new_text = old_raw.decode(), new_raw.decode()
old_functions, new_functions = funcs(old_text), funcs(new_text)
changed = sorted(n for n in old_functions if old_functions[n] != new_functions[n])
added = sorted(set(new_functions) - set(old_functions))
unchanged = sorted(n for n in old_functions if old_functions[n] == new_functions[n])
assert len(old_functions) == 61 and len(new_functions) == 64 and len(unchanged) == 59
assert changed == ['preflight', 'source_manifest']
assert added == sorted(['synthesis_ac_prior_source_binding', 'require_synthesis_ac_prior_scope', 'retained_synthesis_ac_prior_target'])
restored_source_manifest = replace_once(new_functions['source_manifest'],
    ' | set(SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS)', '')
restored_source_manifest = replace_once(restored_source_manifest,
    '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:\n'
    "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
    "                    'Synthesis@AC prior classification differs: ' + module)\n"
    '            synthesis_ac_prior_source_binding(s, graph, sources, module, prior)\n'
    '            continue\n', '')
restored_preflight = replace_once(new_functions['preflight'],
    '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:\n'
    '            retained_synthesis_ac_prior_target(s, spec, module)\n'
    '        elif module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:',
    '        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:')
assert restored_source_manifest == old_functions['source_manifest']
assert restored_preflight == old_functions['preflight']
adapter = (ROOT / 'synthesis_ac_prior_adapter.py').read_text()
restored = replace_once(new_text, adapter, '')
for name in changed:
    restored = replace_once(restored, new_functions[name], old_functions[name])
restored = replace_once(restored, 'AD-anchored 21-root', 'AB-anchored 21-root')
restored = replace_once(restored, 'Endpoint@Y, Mean@AA and Synthesis@AC\n', 'Endpoint@Y and Mean@AA\n')
restored = replace_once(restored, "\nSOURCE_ANCHOR = '" + AD + "'", "\nSOURCE_ANCHOR = '" + AB + "'")
old_manifest_raw = (OLD / 'SOURCE_MANIFEST.json').read_bytes()
manifest_raw = (ROOT / 'SOURCE_MANIFEST.json').read_bytes()
restored = replace_once(restored, "MANIFEST_SHA = '" + fp(manifest_raw)['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(old_manifest_raw)['sha256'] + "'")
assert restored.encode() == old_raw
ast_report = {
    'schema': 'p15_AE_AC_exact_function_delta_v1', 'old_commit': AC, 'source_anchor': AD,
    'old_runner': fp(old_raw), 'new_runner': fp(new_raw),
    'old_function_count': 61, 'new_function_count': 64,
    'unchanged_function_count': 59, 'unchanged_functions': unchanged,
    'changed_functions': changed, 'added_functions': added,
    'source_manifest_only_new_prior_union_and_branch': True,
    'preflight_only_new_prior_dispatch': True,
    'whole_runner_reverse_to_exact_AC_bytes': True,
    'other_allowed_text_changes': ['new fixed Synthesis@AC constants and three-function adapter',
        'source anchor AB to AD', 'manifest fingerprint', 'two introductory documentation strings'],
    'old_function_execution_performed': False,
}
ast_pin = save('AST_DELTA.json', ast_report)

old_m, new_m = json.loads(old_manifest_raw), json.loads(manifest_raw)
changed_top = sorted(k for k in old_m if old_m[k] != new_m[k])
assert set(old_m) == set(new_m)
assert set(changed_top) == {'source_anchor_commit', 'project_sources', 'target_source_origins',
                            'previously_accepted_targets', 'selection_guidance'}
assert new_m['source_anchor_commit'] == AD
changed_sources = [m for m in old_m['project_sources']
                   if old_m['project_sources'][m] != new_m['project_sources'][m]]
assert changed_sources == [LOWERTRIM]
changed_source_fields = sorted(k for k in old_m['project_sources'][LOWERTRIM]
                              if old_m['project_sources'][LOWERTRIM][k] != new_m['project_sources'][LOWERTRIM][k])
assert changed_source_fields == ['bytes', 'git_blob', 'sha256']
assert all(old_m['project_sources'][m][k] == new_m['project_sources'][m][k]
           for m in old_m['project_sources'] for k in ('imports', 'all_imports'))
changed_origins = [m for m in old_m['target_source_origins']
                   if old_m['target_source_origins'][m] != new_m['target_source_origins'][m]]
assert changed_origins == [LOWERTRIM]
assert len(old_m['previously_accepted_targets']) == 13 and len(new_m['previously_accepted_targets']) == 14
assert {m: row for m, row in new_m['previously_accepted_targets'].items() if m != SYNTHESIS} == old_m['previously_accepted_targets']
new_prior = new_m['previously_accepted_targets'][SYNTHESIS]
assert new_prior['source_commit'] == AC and new_prior['historical_group']['run'] == 'runs/attempt-00000'
assert new_prior['historical_group']['public_evidence']['commit'] == AD
policies = ['fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
            'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review']
assert all(old_m[k] == new_m[k] for k in policies)
assert (len(new_m['project_sources']), len(new_m['fixed_dependencies']), len(new_m['unaccepted_p3_dependencies'])) == (360, 303, 19)
packet = json.loads(Path('/tmp/p15-ad-publication/publication_packet.json').read_text())
elements = {r['path']: r['content'].encode() for r in packet['elements']}
inventory = {r['path']: {k: r[k] for k in ('bytes', 'sha256')} for r in packet['inventory']}
bindings = {
    'ImbalancedChen/P5OriginalSingletonLowerTrimPaid.lean': Path('/tmp/p15-lowertrim-repair/P5OriginalSingletonLowerTrimPaid.lean'),
    'docs/p1/20261126/p15-lowertrim-first-compile-repair/REPAIR_CANDIDATE.json': Path('/tmp/p15-lowertrim-repair/REPAIR_CANDIDATE.json'),
    'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json': Path('/tmp/p15-ac-actual/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json'),
}
for path, local in bindings.items():
    assert elements[path] == local.read_bytes() and fp(elements[path]) == inventory[path]
guide_delta = sorted(k for k in set(old_m['selection_guidance']) | set(new_m['selection_guidance'])
                     if old_m['selection_guidance'].get(k) != new_m['selection_guidance'].get(k))
manifest_report = {
    'schema': 'p15_AE_AC_exact_manifest_delta_v1', 'old_commit': AC, 'source_anchor': AD,
    'old_manifest': fp(old_manifest_raw), 'new_manifest': fp(manifest_raw),
    'changed_top_level_keys': changed_top,
    'changed_source_modules': changed_sources, 'changed_source_fields': changed_source_fields,
    'changed_source_origins': changed_origins, 'all_360_import_lists_unchanged': True,
    'other_359_source_rows_unchanged': True, 'old_13_priors_exactly_unchanged': True,
    'new_prior': new_prior, 'unchanged_policy_keys': policies,
    'fixed_dependencies': 303, 'unaccepted_P3_dependencies_held': 19,
    'selection_guidance_changed_keys': guide_delta,
    'relevant_local_AB_packet_content_and_inventory_match': {p: inventory[p] for p in bindings},
    'Git_readback_by_this_verifier': False,
}
manifest_pin = save('MANIFEST_DELTA.json', manifest_report)
log = (ROOT / 'TEST_RESULTS.log').read_bytes()
assert b'Ran 7 tests' in log and log.rstrip().endswith(b'OK')
report = {
    'schema': 'p15_AE_new_Synthesis_AC_prior_local_verification_v1',
    'status': 'SEVEN_TARGETED_TESTS_PASS_AND_EXACT_DELTA_CONFIRMED',
    'source_anchor': AD, 'original_synthesis_acceptance_source': AC,
    'runner': fp(new_raw), 'manifest': fp(manifest_raw), 'adapter': fp(adapter.encode()),
    'tests': {'count': 7, 'exit_code': 0, 'log': fp(log),
              'script': fp((ROOT / 'test_new_adapter.py').read_bytes())},
    'ast_delta': ast_pin, 'manifest_delta': manifest_pin,
    'first': {'sources': 119, 'dependencies': 118, 'watch_modules': 136, 'historical_suppliers': 3},
    'later4': {'sources': 157, 'dependencies': 153, 'watch_modules': 160, 'historical_suppliers': 27},
    'test_scope': ['actual first Synthesis scope and 28/28 identity',
        'both actual RESULT and reconstructed WORKER pins, original supplier counts 2/26',
        'new prior source/closure binding and rejection as a fresh selected target',
        'source/run/count/read-scope/six-receipt paths and original first pins mutation rejection',
        'original successful first final-stock requirement',
        'retained adapter control flow with actual scopes and explicitly mocked runtime/audit IO',
        'later failure/reuse, original later RESULT/WORKER pins, source+5 and full21 rejection'],
    'mock_limit': 'Control-flow tests assert original pin arguments and parsed identities; unavailable original context/log/command bytes and generic audit execution are mocked. No new cloud/runtime/Lean acceptance is claimed.',
    'old_fixture_suites_rerun': False, 'cloud_commands_executed': 0,
    'Git_operations_executed': 0, 'Lean_commands_executed': 0,
    'new_lean_acceptance': False, 'whole_P1_5_complete': False,
}
save('LOCAL_VERIFICATION.json', report)
print(json.dumps({'status': report['status'], 'unchanged_AC_functions': 59,
                  'old_priors_unchanged': 13, 'source_rows_unchanged': 359,
                  'tests': 7, 'source_anchor': AD}, sort_keys=True))
