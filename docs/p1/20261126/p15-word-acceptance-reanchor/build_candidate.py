#!/usr/bin/env python3
"""Append only the original Family@S prior; bind the Word repair source to T."""
from pathlib import Path
import argparse
import ast
import copy
import hashlib
import json
import pprint
import re

BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
R = '0935516b9bd978a61248c81b59776d1eb47f6044'
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
PUBLIC_PATH = 'docs/p1/20261125/p15-current-public-acceptance/FAMILY_S_PUBLIC_ACCEPTANCE.json'
REPAIR_PATH = 'docs/p1/20261126/p15-word-first-compile-repair/REPAIR_CANDIDATE.json'
DRIVER_PATH = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST_PATH = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
OUT = Path('/tmp/p15-entrypoint-u')


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(binding):
    return {k: binding[k] for k in ('bytes', 'sha256')}


def functions(text):
    return {node.name: ast.get_source_segment(text, node)
            for node in ast.parse(text).body if isinstance(node, ast.FunctionDef)}


def replace_once(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--source-anchor', required=True)
    p.add_argument('--public-summary', type=Path, required=True)
    args = p.parse_args()
    assert re.fullmatch('[0-9a-f]{40}', args.source_anchor)
    old = (BASE / 'entrypoint-s/run_selected.py').read_bytes()
    assert fp(old) == {'bytes': 130643, 'sha256': 'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'}
    old_manifest = Path('/tmp/p15-entrypoint-s/SOURCE_MANIFEST.json').read_bytes()
    assert fp(old_manifest) == {'bytes': 346806, 'sha256': '1c6d8499822f69f35469c4bbc222f85d1e46d6a5c977bd4f5c4cdd649520ba86'}
    m = json.loads(old_manifest)
    original_manifest = copy.deepcopy(m)
    pubraw = args.public_summary.read_bytes()
    public = json.loads(pubraw)
    metadata = json.loads(Path('/tmp/p15-s-actual/ACTUAL_S_METADATA.json').read_text())
    repair_raw = Path('/tmp/p15-s-actual/WORD_REPAIR_CANDIDATE.json').read_bytes()
    repair = json.loads(repair_raw)
    word_raw = (BASE / 'P5IndependentPrimeSourceWordDictionary.lean').read_bytes()
    assert fp(word_raw) == repair['after'] == {'bytes': 5672, 'sha256': '021c39e9439f5e304e752093a332f66e68902b1a42a697c5ad4eda2ee29f648f'}
    assert public['source_commit'] == S and public['source_anchor_commit'] == R
    assert public['original_run'] == 'runs/attempt-00000'
    assert public['current_read_live_source_count'] == 75 and public['current_read_preserved_dependency_count'] == 74
    owner = public['owners'][FAMILY]
    assert set(public['owners']) == {FAMILY}
    assert (owner['owned_count'], owner['public_count'], owner['audit_id']) == (27, 27, 'b2f9953a401fa5dd488b')
    assert public['original_result'] == pin(metadata['attempt-00000']['RESULT.json'])
    assert public['original_worker_result'] == pin(metadata['attempt-00000']['WORKER_RESULT.json'])
    group = {'source_commit': S, 'compiler_job': 'job_bf1ad9f0adbc4c8a9fe4b05e99addf4d',
             'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
             'run': 'runs/attempt-00000', 'owners': [FAMILY],
             'driver': {'commit': S, 'path': DRIVER_PATH, **fp(old)},
             'source_graph': {'commit': S, 'path': MANIFEST_PATH, **fp(old_manifest)},
             'published_source_count': 360,
             'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC_PATH, **fp(pubraw)},
             'evidence_kind': 'bounded_public_acceptance'}
    prior = {'group': 'family_s', 'source_commit': S,
             'source_sha256': '4f58683304250030edbca5d1ed4f27eaa06c6de18fb0bbdcad4b2101df0ab109',
             'live_source_closure_count': 75, 'historical_group': group,
             'owned_count': 27, 'public_count': 27, 'audit_id': 'b2f9953a401fa5dd488b'}
    scope = {'targets': [FAMILY], 'accepted': [FAMILY], 'reused': [], 'failed': [],
             'not_accepted': [], 'not_started': [], 'readiness': [FAMILY], 'exit_code': 0,
             'live_count': 75, 'result': pin(metadata['attempt-00000']['RESULT.json']),
             'worker': pin(metadata['attempt-00000']['WORKER_RESULT.json']), 'requested_targets': [FAMILY]}
    later = json.loads(Path('/tmp/p15-s-actual/Later11CapturedResult.json').read_text())
    assert later['source_commit'] == S and later['accepted_owners'] == [FAMILY]
    assert later['reused_complete_selected_owners'] == [FAMILY]
    assert set(later['failures']) == {WORD} and later['worker_exit_code'] == 1
    later_pins = {k: pin(v) for k, v in metadata['attempt-00001'].items()}

    code = old.decode()
    old_functions = functions(code)
    adapter = '\n\n\n'.join(old_functions[n] for n in
        ('q_prior_source_binding', 'require_q_prior_scope', 'retained_q_prior_target'))
    for before, after in (
        ('q_prior_source_binding', 'family_s_prior_source_binding'),
        ('require_q_prior_scope', 'require_family_s_prior_scope'),
        ('retained_q_prior_target', 'retained_family_s_prior_target'),
        ('Q_PREVIOUSLY_ACCEPTED_TARGETS', 'FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS'),
        ('Q_PRIOR_SOURCE_ANCHOR', 'FAMILY_S_PRIOR_SOURCE_ANCHOR'),
        ('Q_PRIOR_RUNS', 'FAMILY_S_PRIOR_RUNS'), ('Q_ALLK_MODULE', 'FAMILY_S_MODULE'),
        ('p15_Q_original_accepted_owner_public_acceptance_v1', 'p15_S_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_Q_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_S_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ("'current_read_live_source_count': 74, 'current_read_preserved_dependency_count': 72",
         "'current_read_live_source_count': 75, 'current_read_preserved_dependency_count': 74"),
        ('later_same_Q_reuse_run', 'later_same_S_reuse_run'),
        ('fixed Q', 'fixed Family@S'), ('original Q', 'original S'), ('Q prior', 'Family@S prior'),
        ('accepted Q owner', 'accepted Family@S owner'), ('original AllK', 'original Family'),
        ('Q public', 'Family@S public')):
        assert before in adapter, before
        adapter = adapter.replace(before, after)
    obsolete = """    else:
        first = json.loads(retained_read(s, spec, base / 'runs/attempt-00000/RESULT.json', FAMILY_S_PRIOR_RUNS[FAMILY_S_MODULE]['result']))
        require(original['acceptance_bindings'][FAMILY_S_MODULE] == first['acceptance_bindings'][FAMILY_S_MODULE],
                'later13 reused AllK binding differs from its first Q acceptance')
"""
    extra = """    later_run = base / 'runs/attempt-00001'
    later = json.loads(retained_read(s, spec, later_run / 'RESULT.json', FAMILY_S_LATER_PINS['RESULT.json']))
    later_worker = json.loads(retained_read(s, spec, later_run / 'WORKER_RESULT.json', FAMILY_S_LATER_PINS['WORKER_RESULT.json']))
    for record in (later, later_worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == FAMILY_S_LATER_TARGETS and record['accepted_owners'] == [module] and
                record['reused_complete_selected_owners'] == [module] and
                record['failures'] == {FAMILY_S_FAILED_WORD: 'normal failed/scope differs: ' + FAMILY_S_FAILED_WORD} and
                set(record['acceptance_bindings']) == {module} and
                record['acceptance_bindings'][module] == original['acceptance_bindings'][module] and
                'final_stock_readiness' not in record and record['whole_P1_5_complete'] is False,
                'original S later11 failure or Family reuse identity differs')
    require(later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
            later['dispatch_error'] == 'serialized worker exited 1' and
            all(later.get(key) == value for key, value in later_worker.items()),
            'original S later11 RESULT/WORKER terminal status differs')
    for stem in ('CONTEXT', 'GIT'):
        require(retained_read(s, spec, later_run / (stem + '_BEFORE.json'), FAMILY_S_LATER_PINS[stem + '_BEFORE.json']) ==
                retained_read(s, spec, later_run / (stem + '_AFTER.json'), FAMILY_S_LATER_PINS[stem + '_AFTER.json']),
                'original S later11 context/Git pair differs')
"""
    adapter = replace_once(adapter, obsolete, extra)
    consts = {'FAMILY_S_MODULE': FAMILY, 'FAMILY_S_FAILED_WORD': WORD,
              'FAMILY_S_PRIOR_SOURCE_ANCHOR': R,
              'FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS': {FAMILY: prior},
              'FAMILY_S_PRIOR_RUNS': {FAMILY: scope},
              'FAMILY_S_LATER_PINS': later_pins, 'FAMILY_S_LATER_TARGETS': later['targets']}
    inserted = '\n\n# Fixed Family@S acceptance; original successful and later partial runs stay S.\n'
    inserted += '\n'.join(k + ' = ' + pprint.pformat(v, width=110, sort_dicts=False) for k, v in consts.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n' + adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        "} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS),\n            'fixed previous-target acceptance identity differs')",
        "} | set(Q_PREVIOUSLY_ACCEPTED_TARGETS) | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS),\n            'fixed previous-target acceptance identity differs')")
    code = replace_once(code, "    for module, prior in previous.items():\n        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:",
        "    for module, prior in previous.items():\n        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:\n            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n                    'Family@S prior classification differs: ' + module)\n            family_s_prior_source_binding(s, graph, sources, module, prior)\n            continue\n        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:")
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:",
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:\n            retained_family_s_prior_target(s, spec, module)\n        elif module in Q_PREVIOUSLY_ACCEPTED_TARGETS:")
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + R + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'R-anchored 21-root', 'T-anchored 21-root')
    code = replace_once(code, 'AllK@Q and Admissible@Q\n', 'AllK@Q, Admissible@Q and Family@S\n')

    m['source_anchor_commit'] = args.source_anchor
    row = m['project_sources'][WORD]
    row.update(**fp(word_raw), git_blob=hashlib.sha1(b'blob ' + str(len(word_raw)).encode() + b'\0' + word_raw).hexdigest())
    origin = m['target_source_origins'][WORD]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(word_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': REPAIR_PATH, **fp(repair_raw)})
    m['previously_accepted_targets'][FAMILY] = prior
    guide = m['selection_guidance']
    guide.update(minimum_first_targets=[WORD], minimum_first_source_count=77, minimum_first_dependency_count=76)
    guide['previously_accepted_not_compile_targets'].append(FAMILY)
    guide['remaining_project_graph_unblocked_compile_candidates'].remove(FAMILY)
    guide['subsequent_10_targets'] = [x for x in guide['subsequent_11_targets'] if x != FAMILY]
    guide.update(subsequent_10_source_count=157, subsequent_10_dependency_count=147,
                 subsequent_10_artifact_watch_module_count=160)
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure are revalidated. Word first77 uses Family@S75 and its '
        'five historical dependencies HB@F67, Licensed@M68, PerGroup@O69, AllK@Q73 and Admissible@Q70. '
        'Later10 closure157 also reuses Support@B109 and Cutoff@K68. All eight remain at their original commits '
        'and cannot be selected. Family retains successful S attempt-00000 with final stock and unchanged '
        'reuse in partial S attempt-00001 (Word failed, nine unstarted). Earlier subsequent11/13/14/15 lists '
        'are historical. The source repair installer is separate.')
    assert {k: v for k, v in m['project_sources'].items() if k != WORD} == {
        k: v for k, v in original_manifest['project_sources'].items() if k != WORD}
    assert all(m['project_sources'][k]['imports'] == v['imports'] for k, v in original_manifest['project_sources'].items())
    assert {k: v for k, v in m['previously_accepted_targets'].items() if k != FAMILY} == original_manifest['previously_accepted_targets']
    mr = (json.dumps(m, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + fp(old_manifest)['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if new_functions[name] != old_functions[name]}
    assert changed == {'source_manifest', 'preflight'}, changed
    assert set(new_functions) - set(old_functions) == {
        'family_s_prior_source_binding', 'require_family_s_prior_scope', 'retained_family_s_prior_target'}
    ast.parse(code)
    output = BASE / 'entrypoint-u'
    output.mkdir(exist_ok=True)
    (output / 'run_selected.py').write_text(code)
    (OUT / 'SOURCE_MANIFEST.json').write_bytes(mr)
    (output / 'family_s_prior_adapter.py').write_text(inserted)
    report = {'schema': 'p15_T_source_Family_S_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'original_S_function_count': len(old_functions),
              'unchanged_S_functions': len(old_functions)-2, 'changed_functions': sorted(changed),
              'new_functions': sorted(set(new_functions)-set(old_functions)),
              'other_359_sources_and_all_imports_unchanged': True,
              'seven_prior_identities_unchanged': True, 'new_lean_acceptance': False,
              'verification_not_yet_run': True, 'whole_P1_5_complete': False}
    (OUT / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
