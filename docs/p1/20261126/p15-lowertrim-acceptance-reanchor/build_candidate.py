#!/usr/bin/env python3
"""Append only Synthesis@AC; bind the reviewed LowerTrim repair to source anchor AD.

No candidate is emitted until the actual AD source publication and successful
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
AC = '9f2013ad9cb9caac9cec03cb213d9949c4443c65'
AB = '60e6b6e18fbda5f6b0e997d15392b32100e854d9'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PUBLIC = 'docs/p1/20261125/p15-current-public-acceptance/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json'
AC_DRIVER = {'bytes': 278990, 'sha256': '3db1965e25fbd2fe9ddf6b1af10ef1a47f479479e8a076646d6de46c3f7130b0'}
AC_MANIFEST = {'bytes': 362316, 'sha256': 'b56ca98e7c46d9e6ab9244b2fe32f15717db95a325a0ca5e52ee965d900f44c9'}
AC_PUBLIC = {'bytes': 11788, 'sha256': '1f2c0a0c1c00f3ac76eb2d0255ff480581438d624129f673b9f4e4e194ae37d7'}
AC_READ = {'bytes': 37703, 'sha256': 'be82048b4039cc6e0368528c01972a85c9d4ae11a0e40e0c77f471eade1a80fa'}
AC_METADATA = {'bytes': 15785, 'sha256': '5103c9d5d04a3c37c68e0bff7043f6ad8d9d8727bf12cd44c1c2dd6c9a7124d2'}
LOWERTRIM_BEFORE = {'bytes': 14601, 'sha256': '82cfc7b75510076d0ded95130504639cde2ee39d38cff4133964a092d5cbcf54'}
LOWERTRIM_AFTER = {'bytes': 14655, 'sha256': 'f26884610a2d205368b347ed5fd80947c91c5973a6750bc0b333cb57dcb42106'}
LOWERTRIM_REPAIR = {'bytes': 1596, 'sha256': '45592035ce29e584e6b4783163e93edbb70d6495a1e0b94e46a06c8c7fb33d73'}
LOWERTRIM_PROBE_JOB = 'job_abfb9ce81e7749c290d6f61c385aa749'
LOWERTRIM_REPAIR_SCHEMA = 'p15_singleton_lower_trim_paid_one_proof_splice_candidate_v1'
LOWERTRIM_DECLARATION_COUNT = 8


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
                   default=Path('/tmp/p15-ac-actual/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json'))
    p.add_argument('--acceptance-read', type=Path,
                   default=Path('/tmp/p15-ac-actual/ACTUAL_AC_ACCEPTANCE_READ.json'))
    p.add_argument('--repair-source', type=Path, required=True)
    p.add_argument('--repair-candidate', type=Path, required=True)
    p.add_argument('--repair-review-path', required=True)
    p.add_argument('--output', type=Path, default=Path('/tmp/p15-entrypoint-ae'))
    args = p.parse_args()
    need(all(value is not None for value in (AD, AC_PUBLIC, AC_READ, LOWERTRIM_AFTER,
         LOWERTRIM_REPAIR, LOWERTRIM_PROBE_JOB, LOWERTRIM_REPAIR_SCHEMA, LOWERTRIM_DECLARATION_COUNT)),
         'HOLD: actual AC collector, successful LowerTrim repair, and real AD publication must be bound')
    need(__debug__ and args.source_anchor == AD,
         'exact published AD source anchor required')
    need(args.output.resolve() == Path('/tmp/p15-entrypoint-ae'),
         'only the separate local /tmp/p15-entrypoint-ae output directory is supported')
    need(args.repair_review_path ==
         'docs/p1/20261126/p15-lowertrim-first-compile-repair/REPAIR_CANDIDATE.json',
         'exact LowerTrim repair review path required')
    old = Path('/tmp/p15-entrypoint-ac/run_selected.py').read_bytes()
    manifest_raw = Path('/tmp/p15-entrypoint-ac/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == AC_DRIVER and fp(manifest_raw) == AC_MANIFEST, 'frozen AC baseline differs')
    manifest = json.loads(manifest_raw)
    before_manifest = copy.deepcopy(manifest)
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    public_raw, read_raw = args.public_summary.read_bytes(), args.acceptance_read.read_bytes()
    public, read = json.loads(public_raw), json.loads(read_raw)
    metadata_raw = Path('/tmp/p15-ac-actual/ACTUAL_AC_METADATA.json').read_bytes()
    need(fp(public_raw) == AC_PUBLIC and fp(read_raw) == AC_READ and fp(metadata_raw) == AC_METADATA,
         'actual AC cloud-collected public/read/metadata fingerprints differ')
    metadata = json.loads(metadata_raw)
    need(public == read['public_summaries']['SYNTHESIS_AC_PUBLIC_ACCEPTANCE'] and
         public['source_commit'] == read['source_commit'] == AC and
         public['source_anchor_commit'] == read['source_anchor_commit'] == AB and
         public['schema'] == 'p15_AC_original_accepted_owner_public_acceptance_v1' and
         public['status'] == 'ORIGINAL_AC_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION' and
         public['selected_owners_revalidated'] == [SYNTHESIS] and set(public['owners']) == {SYNTHESIS} and
         public['original_run'] == 'runs/attempt-00000' and
         public['compiler_job'] == 'job_b4464fff4b944230927c0f40b7cd1632' and
         public['current_read_live_source_count'] == 112 and
         public['current_read_preserved_dependency_count'] == 111 and
         public['normal_or_kernel_commands_executed'] == 0 and public['new_lean_acceptance'] is False and
         public['whole_P1_5_complete'] is False, 'actual AC accepted-prefix public identity differs')
    owner = public['owners'][SYNTHESIS]
    need((owner['owned_count'], owner['public_count'], owner['audit_id']) ==
         (28, 28, '2dd4c543e4398010981b') and
         owner['owner_live_source_closure_count'] == len(closure(graph, [SYNTHESIS])) == 112 and
         public['driver'] == {'commit': AC, 'path': DRIVER, **AC_DRIVER} and
         public['source_manifest'] == {'commit': AC, 'path': MANIFEST, **AC_MANIFEST} and
         owner['source_sha256'] == manifest['project_sources'][SYNTHESIS]['sha256'],
         'Synthesis@AC own source/count/driver/manifest differs')
    actual = []
    for index in (0, 1):
        raw = Path('/tmp/p15-ac-actual/attempt-%05d-RESULT.json' % index).read_bytes()
        result = json.loads(raw)
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        wr = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        pins = metadata['runs']['attempt-%05d' % index]
        need(fp(raw) == pin(pins['RESULT.json']) and fp(wr) == pin(pins['WORKER_RESULT.json']),
             'actual AC RESULT/WORKER pins differ')
        actual.append(result)
    first, later = actual
    need(first['targets'] == first['accepted_owners'] == [SYNTHESIS] and first['failures'] == {} and
         first['worker_exit_code'] == 0 and first['reused_complete_selected_owners'] == [] and
         first['final_stock_readiness']['exit_code'] == 0 and
         len(first['original_supplier_acceptance_bindings']) == 2 and
         later['targets'] == manifest['selection_guidance']['subsequent_5_targets'] and
         later['accepted_owners'] == later['reused_complete_selected_owners'] == [SYNTHESIS] and
         later['failures'] == {LOWERTRIM: 'normal failed/scope differs: ' + LOWERTRIM} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['acceptance_bindings'][SYNTHESIS] == first['acceptance_bindings'][SYNTHESIS] and
         len(later['original_supplier_acceptance_bindings']) == 26 and
         public['later_same_source_reuse'] == read['original_runs'][1] and
         public['later_same_source_reuse']['compiler_job'] == 'job_a108c4d7e2594e1fb5a674382db6600f' and
         len(public['later_same_source_reuse']['not_started_modules']) == 3,
         'original AC successful/partial run identities differ')
    group = {'source_commit': AC, 'compiler_job': public['compiler_job'],
             'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
             'run': 'runs/attempt-00000', 'owners': [SYNTHESIS],
             'driver': public['driver'], 'source_graph': public['source_manifest'],
             'published_source_count': 360,
             'public_evidence': {'commit': args.source_anchor, 'path': PUBLIC, **fp(public_raw)},
             'evidence_kind': 'bounded_public_acceptance'}
    prior = {'group': 'synthesis_ac', 'source_commit': AC, 'source_sha256': owner['source_sha256'],
             'live_source_closure_count': 112, 'historical_group': group,
             'owned_count': 28, 'public_count': 28, 'audit_id': owner['audit_id']}
    scope = {'targets': [SYNTHESIS], 'accepted': [SYNTHESIS], 'reused': [], 'failed': [],
             'not_accepted': [], 'not_started': [], 'readiness': [SYNTHESIS], 'exit_code': 0,
             'live_count': 112, 'result': public['original_result'], 'worker': public['original_worker_result'],
             'requested_targets': public['original_requested_targets']}
    need(scope['result'] == pin(metadata['runs']['attempt-00000']['RESULT.json']) and
         scope['worker'] == pin(metadata['runs']['attempt-00000']['WORKER_RESULT.json']),
         'Synthesis@AC public original run pins differ')
    later_pins = {key: pin(value) for key, value in
                  public['later_same_source_reuse']['evidence_bindings'].items()}
    need(set(later_pins) == set(metadata['runs']['attempt-00001']) | {'executed-driver.py'} and
         all(later_pins[key] == pin(value) for key, value in metadata['runs']['attempt-00001'].items()) and
         later_pins['executed-driver.py'] == AC_DRIVER, 'original AC later run pins differ')
    repair_raw, source_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][LOWERTRIM]
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / row['path']).read_bytes()
    need(fp(repair_raw) == LOWERTRIM_REPAIR and
         repair['schema'] == LOWERTRIM_REPAIR_SCHEMA and
         repair['source_base_commit'] == AC and repair['source'] == row['path'] and
         repair['before'] == pin(row) == fp(before) == LOWERTRIM_BEFORE and
         repair['after'] == fp(source_raw) == LOWERTRIM_AFTER and
         len(repair['splices']) == 1 and repair['declaration_count'] == LOWERTRIM_DECLARATION_COUNT and
         repair['imports_unchanged'] is True and repair['declaration_headers_unchanged'] is True and
         repair['axioms_or_sorry_added'] is False and repair['compiler_probe_performed'] is True and
         repair['actual_whole_module_probe']['exit_code'] == 0 and
         repair['actual_whole_module_probe']['compiler_job'] == LOWERTRIM_PROBE_JOB and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'reviewed LowerTrim proof repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'LowerTrim splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode())); end = stop
    need(b''.join(pieces) + before[end:] == source_raw and
         re.findall(r'^import\s+(\S+)\s*$', source_raw.decode(), re.M) == row['all_imports'],
         'LowerTrim bytes outside reviewed splice or imports changed')
    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
        ('mean_aa_prior_source_binding', 'require_mean_aa_prior_scope', 'retained_mean_aa_prior_target'))
    replacements = [('mean_aa_prior_source_binding', 'synthesis_ac_prior_source_binding'),
     ('require_mean_aa_prior_scope', 'require_synthesis_ac_prior_scope'),
     ('retained_mean_aa_prior_target', 'retained_synthesis_ac_prior_target'),
     ('MEAN_AA_FAILED_SYNTHESIS', 'SYNTHESIS_AC_FAILED_LOWERTRIM'),
     ('MEAN_AA_', 'SYNTHESIS_AC_'),
     ('p15_AA_original_accepted_owner_public_acceptance_v1',
      'p15_AC_original_accepted_owner_public_acceptance_v1'),
     ('ORIGINAL_AA_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
      'ORIGINAL_AC_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
     ("'current_read_live_source_count': 108, 'current_read_preserved_dependency_count': 107",
      "'current_read_live_source_count': 112, 'current_read_preserved_dependency_count': 111"),
     ('later_same_AA_reuse_run', 'later_same_AC_reuse_run'),
     ('Mean@AA', 'Synthesis@AC'),
     ('original AA', 'original AC'),
     ('original Mean', 'original Synthesis'),
     ('Mean reuse', 'Synthesis reuse'),
     ('later6', 'later5')]
    for before_text, after_text in replacements:
        need(before_text in adapter, 'missing adapter fragment: ' + before_text)
        adapter = adapter.replace(before_text, after_text)
    template = Path(__file__).with_name('synthesis_ac_prior_adapter.py.in').read_text()
    need(adapter + '\n' == template, 'reviewed Synthesis@AC three-function template differs')
    constants = {'SYNTHESIS_AC_MODULE': SYNTHESIS, 'SYNTHESIS_AC_FAILED_LOWERTRIM': LOWERTRIM,
                 'SYNTHESIS_AC_PRIOR_SOURCE_ANCHOR': AB,
                 'SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS': {SYNTHESIS: prior},
                 'SYNTHESIS_AC_PRIOR_RUNS': {SYNTHESIS: scope},
                 'SYNTHESIS_AC_LATER_PINS': later_pins, 'SYNTHESIS_AC_LATER_TARGETS': later['targets'],
                 'SYNTHESIS_AC_LATER_RECORD': public['later_same_source_reuse']}
    inserted = '\n\n# Fixed Synthesis@AC acceptance; original AC later5 remains partial.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code,
        ' | set(MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS),\n',
        ' | set(MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS) | set(SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS),\n')
    code = replace_once(code,
        '    for module, prior in previous.items():\n        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:',
        '    for module, prior in previous.items():\n'
        '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Synthesis@AC prior classification differs: ' + module)\n"
        '            synthesis_ac_prior_source_binding(s, graph, sources, module, prior)\n'
        '            continue\n'
        '        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:',
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        '            retained_synthesis_ac_prior_target(s, spec, module)\n'
        '        elif module in MEAN_AA_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + AB + "'", "\nSOURCE_ANCHOR = '" + args.source_anchor + "'")
    code = replace_once(code, 'AB-anchored 21-root', 'AD-anchored 21-root')
    code = replace_once(code, 'Endpoint@Y and Mean@AA\n', 'Endpoint@Y, Mean@AA and Synthesis@AC\n')
    manifest['source_anchor_commit'] = args.source_anchor
    row.update(**fp(source_raw), git_blob=hashlib.sha1(
        b'blob ' + str(len(source_raw)).encode() + b'\0' + source_raw).hexdigest())
    origin = manifest['target_source_origins'][LOWERTRIM]
    origin['canonical_source'] = {'commit': args.source_anchor, 'path': row['path'], **fp(source_raw)}
    origin['source_reviews'].append({'commit': args.source_anchor, 'path': args.repair_review_path, **fp(repair_raw)})
    manifest['previously_accepted_targets'][SYNTHESIS] = prior
    guide = manifest['selection_guidance']
    guide.update(minimum_first_targets=[LOWERTRIM], minimum_first_source_count=119,
                 minimum_first_dependency_count=118, minimum_first_artifact_watch_module_count=136,
                 minimum_first_historical_supplier_count=3)
    guide['previously_accepted_not_compile_targets'].append(SYNTHESIS)
    guide['remaining_project_graph_unblocked_compile_candidates'].remove(SYNTHESIS)
    remaining = [m for m in guide['subsequent_5_targets'] if m != SYNTHESIS]
    guide.update(subsequent_4_targets=remaining, subsequent_4_source_count=157,
                 subsequent_4_dependency_count=153, subsequent_4_artifact_watch_module_count=160,
                 subsequent_4_historical_supplier_count=27)
    active, first_active = closure(graph, remaining), closure(graph, [LOWERTRIM])
    historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
    need(len(first_active) == 119 and len(first_active - {LOWERTRIM}) == 118 and
         len(first_active | set(manifest['targets'])) == 136 and
         first_active & historical == {ENDPOINT, MEAN, SYNTHESIS} and len(active) == 157 and
         len(active - set(remaining)) == 153 and len(active | set(manifest['targets'])) == 160 and
         len(active & historical) == 27 and
         LOWERTRIM not in closure(graph, [SYNTHESIS]) and
         len(manifest['previously_accepted_targets']) == 14 and
         len(manifest['project_sources']) == 360 and len(manifest['fixed_dependencies']) == 303 and
         len(manifest['unaccepted_p3_dependencies']) == 19,
         'AC source/own dependency scope differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. LowerTrim first119/118 '
        'has three historical suppliers, Endpoint@Y, Mean@AA and Synthesis@AC. Later4 closure157/153 includes all fourteen '
        'prior targets and 27 historical supplier entries. Original AC remaining4 has 26 because Synthesis is still its '
        'current completed owner there. Synthesis retains its AC attempt-00000 acceptance with final stock and unchanged '
        'reuse in partial AC attempt-00001; LowerTrim failed and three following targets were unstarted. Both original '
        'run contexts, executed drivers and six Synthesis receipts remain fixed; the previous thirteen priors are unchanged. '
        'Old subsequent5/6/7/8/10/11/13/14/15 guidance remains historical. No prior is selected or rebound. The source installer '
        'is separate.')
    need({k: v for k, v in manifest['project_sources'].items() if k != LOWERTRIM} ==
         {k: v for k, v in before_manifest['project_sources'].items() if k != LOWERTRIM} and
         all(manifest['project_sources'][m][k] == old_row[k] for m, old_row in before_manifest['project_sources'].items()
             for k in ('imports', 'all_imports')), 'unrelated source/import change')
    need({k: v for k, v in manifest['target_source_origins'].items() if k != LOWERTRIM} ==
         {k: v for k, v in before_manifest['target_source_origins'].items() if k != LOWERTRIM},
         'unrelated source origin changed')
    need({k: v for k, v in manifest['previously_accepted_targets'].items() if k != SYNTHESIS} ==
         before_manifest['previously_accepted_targets'], 'thirteen prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(manifest[key] == before_manifest[key], 'old policy changed: ' + key)
    mr = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + AC_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if old_functions[name] != new_functions[name]}
    added = set(new_functions) - set(old_functions)
    need(len(old_functions) == 61 and len(new_functions) == 64 and
         changed == {'source_manifest', 'preflight'} and added ==
         {'synthesis_ac_prior_source_binding', 'require_synthesis_ac_prior_scope', 'retained_synthesis_ac_prior_target'},
         'unexpected existing/new function changes')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': mr,
                      'synthesis_ac_prior_adapter.py': inserted.encode()}.items():
        (args.output / name).write_bytes(raw)
    report = {'schema': 'p15_AD_source_Synthesis_AC_prior_generation_v1', 'source_anchor': args.source_anchor,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'adapter': fp(inserted.encode()),
              'original_AC_function_count': len(old_functions), 'unchanged_AC_functions': len(old_functions) - 2,
              'changed_functions': sorted(changed), 'new_functions': sorted(added),
              'thirteen_prior_identities_unchanged': True, 'other_359_sources_all_imports_303_19_policy_unchanged': True,
              'actual_AC_public': fp(public_raw), 'actual_AC_acceptance_read': fp(read_raw),
              'LowerTrim_repair': {'source': fp(source_raw), 'review': fp(repair_raw), 'splices': len(repair['splices'])},
              'first': {'sources': 119, 'dependencies': 118, 'watch_modules': 136, 'historical_suppliers': 3},
              'later4': {'sources': 157, 'dependencies': 153, 'watch_modules': 160, 'historical_suppliers': 27},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (args.output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
