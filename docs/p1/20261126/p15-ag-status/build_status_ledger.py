#!/usr/bin/env python3
"""Bind final AG status only from actual pinned runs, metadata and collector.

This is local evidence processing. It never runs Lean, Git, a cloud command,
or a search. The older AE snapshots are immutable inputs, never output paths.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json

ROOT = Path('/tmp/p15-ag-status')
AG = '63ad8bf4c52caed9f4e199834ae1d2b0b18f971b'
AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'
MANIFEST_FILE = Path('/tmp/p15-entrypoint-ag/SOURCE_MANIFEST.json')
MANIFEST_PIN = {'bytes': 369103, 'sha256': '21c0b14701a2123edab7353aa27dbb9c950427a805d75aaa3562c6033eb137f9'}
AE_BEFORE = Path('/tmp/p15-ae-status/STATUS_LEDGER.json')
AE_BEFORE_PIN = {'bytes': 52729, 'sha256': '13595d2437a243fa8c2ef552af153d87abcc9f1aca151077a95232df13ca3df1'}
AE_AFTER = Path('/tmp/p15-ae-status/STATUS_LEDGER_AFTER_COLLECTOR.json')
AE_AFTER_PIN = {'bytes': 59466, 'sha256': 'edd6c7c919e3e0a6826ffcbf7481a5728f4f1a83e143980759c88730ad5760d8'}
RESERVE = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
FIRST_JOB = 'job_83532ebe8bdd423caa1a7610aac08ae7'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pure(value):
    return {key: value[key] for key in ('bytes', 'sha256')}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def read_pinned(binding):
    need(isinstance(binding, dict) and isinstance(binding.get('path'), str) and
         type(binding.get('bytes')) is int and isinstance(binding.get('sha256'), str),
         'HOLD: actual local path/bytes/hash binding is missing')
    raw = Path(binding['path']).read_bytes()
    need(fp(raw) == pure(binding), 'actual input fingerprint differs: ' + binding['path'])
    return json.loads(raw)


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module); pending.extend(graph[module])
    return seen


def save(name, value):
    raw = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    (ROOT / name).write_bytes(raw)
    return fp(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, default=ROOT / 'ACTUAL_INPUTS.required.json')
    args = parser.parse_args()
    cfg_raw = args.inputs.read_bytes(); cfg = json.loads(cfg_raw)
    need(cfg.get('state') == 'ACTUAL_AG_RESULTS_METADATA_AND_COLLECTOR_BOUND',
         'HOLD: wait for actual first/later results, metadata, and successful actual collector')
    need(not any((ROOT / name).exists() for name in
                 ('STATUS_LEDGER.json', 'CONTINUE_WORK.md', 'LEDGER_BINDINGS.json')),
         'HOLD: final AG snapshot already exists; do not overwrite a frozen snapshot')
    manifest_raw = MANIFEST_FILE.read_bytes()
    need(fp(manifest_raw) == MANIFEST_PIN, 'published AG manifest changed')
    manifest = json.loads(manifest_raw)
    need(manifest['source_anchor_commit'] == AF and len(manifest['targets']) == 21 and
         len(manifest['previously_accepted_targets']) == 16, 'AG baseline identity differs')
    prior_before_raw, prior_after_raw = AE_BEFORE.read_bytes(), AE_AFTER.read_bytes()
    need(fp(prior_before_raw) == AE_BEFORE_PIN and fp(prior_after_raw) == AE_AFTER_PIN,
         'immutable AE status snapshot changed')
    prior_snapshot = json.loads(prior_after_raw)
    metadata = read_pinned(cfg['metadata'])
    read = read_pinned(cfg['collector']['read'])
    collector_task = read_pinned(cfg['collector']['task'])
    need(metadata['source_commit'] == read['source_commit'] == AG and read['source_anchor_commit'] == AF,
         'actual AG metadata/collector source identity differs')
    need(collector_task['status'] == 'succeeded' and collector_task['exit_code'] == 0 and
         collector_task['task_id'] == cfg['collector']['compiler_job'], 'actual collector task was not successful')
    need(read['normal_or_kernel_commands_executed'] == 0 and read['new_lean_acceptance'] is False and
         read['source_runtime_artifacts_and_original_receipts_unchanged'] is True and
         read['current_dirty_Git_state_unchanged'] is True and read['whole_P1_5_complete'] is False,
         'actual collector conservation/status differs')
    graph = {module: row['imports'] for module, row in manifest['project_sources'].items()}
    historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
    need(len(cfg['runs']) in (1, 2) and len(cfg['runs']) == len(metadata['runs']) == len(read['original_runs']),
         'do not omit an actual original run')
    results, run_evidence = [], []
    for index, run_input in enumerate(cfg['runs']):
        run_key = 'attempt-%05d' % index
        need(run_input['run'] == 'runs/' + run_key, 'original run order differs')
        result = read_pinned(run_input['result'])
        task = read_pinned(run_input['task'])
        pins = metadata['runs'][run_key]
        need(pure(run_input['result']) == pure(pins['RESULT.json']), 'original RESULT pin differs from metadata')
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        worker_raw = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        need(fp(worker_raw) == pure(pins['WORKER_RESULT.json']), 'original WORKER pin differs from metadata')
        need(task['task_id'] == run_input['compiler_job'] and task['exit_code'] == result['worker_exit_code'] and
             task['status'] in ('succeeded', 'failed'), 'original task is not a matching terminal result')
        if index == 0:
            need(run_input['compiler_job'] == FIRST_JOB and result['targets'] == [RESERVE], 'first AG task/selection differs')
        else:
            need(result['targets'] == [RESERVE, ROUGH], 'later2 AG target scope differs')
        need(result['source_commit'] == AG and result['published_source_count'] == 360 and
             result['whole_P1_5_complete'] is False and
             result['selected_live_source_count'] == len(closure(graph, result['targets'])) and
             len(result['original_supplier_acceptance_bindings']) == len(closure(graph, result['targets']) & historical),
             'original run source/graph/supplier scope differs')
        group = read['original_runs'][index]
        need(group['source_commit'] == AG and group['compiler_job'] == run_input['compiler_job'] and
             group['targets'] == result['targets'] and group['accepted_owners'] == result['accepted_owners'] and
             group['reused_complete_selected_owners'] == result['reused_complete_selected_owners'] and
             group['failure_messages'] == result['failures'] and group['worker_exit_code'] == result['worker_exit_code'] and
             pure(group['evidence_bindings']['RESULT.json']) == pure(pins['RESULT.json']) and
             pure(group['evidence_bindings']['WORKER_RESULT.json']) == pure(pins['WORKER_RESULT.json']) and
             group['original_final_stock_readiness']['recorded'] == ('final_stock_readiness' in result),
             'collector rewrote the original run identity or final-stock presence')
        for module in result['reused_complete_selected_owners']:
            previous = [r for r in results if module in r['accepted_owners']]
            need(previous and result['acceptance_bindings'][module] == previous[0]['acceptance_bindings'][module],
                 'reused acceptance differs from its original accepting run')
        results.append(result)
        run_evidence.append({'compiler_job': run_input['compiler_job'], 'run': run_input['run'],
                             'task': run_input['task'], 'original_pins': pins, 'actual_group': group,
                             'reconstructed_WORKER_matches_actual_metadata': True})
    need(len(results) == 2 or (results[0]['worker_exit_code'] != 0 and cfg.get('actual_reason_later_not_run')),
         'HOLD: successful first run does not stand in for a missing later2 outcome')
    accepted = set().union(*(set(result['accepted_owners']) for result in results))
    need(accepted <= {RESERVE, ROUGH} and set(metadata['accepted_owners']) == accepted and
         set(read['selected_owners_revalidated']) == accepted, 'actual accepted prefix / collector selection differs')
    active = closure(graph, accepted)
    need(read['current_read_live_source_count'] == len(active) and
         read['current_read_preserved_dependency_count'] == len(active - accepted) and
         len(read['historical_owners_revalidated_in_current_read_scope']) == len(active & historical),
         'actual joint collector scope differs from the accepted owners')
    publics = {}
    need(set(cfg['collector']['public_summaries']) == set(read['public_summaries']), 'actual public summary list differs')
    for name, binding in cfg['collector']['public_summaries'].items():
        public = read_pinned(binding)
        need(public == read['public_summaries'][name] and len(public['owners']) == 1,
             'public bytes differ from actual collector')
        module = next(iter(public['owners']))
        need(module in accepted and module not in publics, 'unexpected/duplicate public owner')
        owner = public['owners'][module]; actual_owner = metadata['accepted_owners'][module]
        index = actual_owner['first_accepting_run_index']
        need(index == min(i for i, result in enumerate(results) if module in result['accepted_owners']),
             'owner accepting run was changed')
        original = results[index]; original_binding = original['acceptance_bindings'][module]
        need(public['source_commit'] == AG and public['source_anchor_commit'] == AF and
             public['original_run'] == 'runs/attempt-%05d' % index and
             public['compiler_job'] == cfg['runs'][index]['compiler_job'] and
             public['original_targets'] == original['targets'] and
             public['original_group_worker_exit_code'] == original['worker_exit_code'] and
             public['original_result'] == pure(metadata['runs']['attempt-%05d' % index]['RESULT.json']) and
             public['original_worker_result'] == pure(metadata['runs']['attempt-%05d' % index]['WORKER_RESULT.json']) and
             public['current_read_live_source_count'] == len(active) and
             public['current_read_preserved_dependency_count'] == len(active - accepted),
             'public original-run/joint scope differs')
        need((owner['owned_count'], owner['public_count']) ==
             (actual_owner['owned_count'], actual_owner['public_count']) and
             owner['audit_id'] == Path(actual_owner['audit_plan']['path']).parent.name and
             owner['source_sha256'] == actual_owner['source']['sha256'] == manifest['project_sources'][module]['sha256'] and
             owner['owner_live_source_closure_count'] == len(closure(graph, [module])) and
             actual_owner['normal'] == original_binding['normal_receipt'] and
             actual_owner['audit_plan'] == original_binding['audits'][0]['plan'] and
             actual_owner['audit_result'] == original_binding['audits'][0]['result'] and
             actual_owner['audit_exit_code'] == 0 and actual_owner['kernel_exit_codes'] == {module: 0} and
             actual_owner['full_owned_including_private_generated'] is True and actual_owner['only_standard_axioms'] is True and
             owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
             owner['source_plus_five_and_all_21_artifacts_bound_to_original_result'] is True and
             owner['receipt_rebound_to_current_commit'] is False,
             'actual owner source/count/normal/kernel/full-owned identity differs')
        publics[module] = {'summary_name': name, 'file': binding, 'public': public, 'owner': owner, 'run_index': index}
    need(set(publics) == accepted, 'missing actual accepted-owner public summary')
    blocked = set(manifest['selection_guidance']['project_graph_blocked_candidates'])
    rows = []
    for module in manifest['targets']:
        source = manifest['project_sources'][module]
        row = {'module': module, 'current_source': {k: source[k] for k in ('path', 'bytes', 'sha256')},
               'canonical_source_origin': manifest['target_source_origins'][module]['canonical_source']}
        if module in manifest['previously_accepted_targets']:
            prior = manifest['previously_accepted_targets'][module]
            need(prior['source_sha256'] == source['sha256'], 'old accepted source changed')
            row.update(status='ACCEPTED_HISTORICAL_PRIOR', original_acceptance=prior)
        elif module in accepted:
            item = publics[module]; index = item['run_index']
            row.update(status='ACCEPTED_ORIGINAL_AG_OWNER', accepting_run='runs/attempt-%05d' % index,
                       compiler_job=cfg['runs'][index]['compiler_job'], owner=item['owner'],
                       public_summary_file=item['file'], original_group_worker_exit_code=results[index]['worker_exit_code'],
                       original_group_final_stock_recorded='final_stock_readiness' in results[index])
        elif module in blocked:
            row.update(status='HOLD_UNACCEPTED_P3_DEPENDENCIES',
                       blocking_dependency_modules=sorted(closure(graph, [module]) & set(manifest['unaccepted_p3_dependencies'])))
        else:
            relevant = [group for group in read['original_runs'] if module in group['targets']]
            if relevant and module in relevant[-1]['failed_modules']:
                row.update(status='FAILED_NOT_ACCEPTED', failure=relevant[-1]['failure_messages'][module])
            elif relevant and module in relevant[-1]['not_started_modules']:
                row.update(status='NOT_STARTED_NOT_ACCEPTED')
            else:
                row.update(status='UNACCEPTED_NO_COMPLETE_OWNER_EVIDENCE')
        rows.append(row)
    counts = {'total': 21, 'accepted_historical_priors': 16, 'new_original_AG_accepted_owners': len(accepted),
              'confirmed_accepted_targets_total': 16 + len(accepted), 'proper_power_targets_held': len(blocked),
              'other_unaccepted_targets': 2 - len(accepted)}
    need(len(blocked) == 3 and len(manifest['unaccepted_p3_dependencies']) == 19, 'standing P3 HOLD scope changed')
    p3 = copy.deepcopy(prior_snapshot['P3_hold'])
    need(p3['policy'] == manifest['unaccepted_p3_policy'] and
         {r['module'] for r in p3['dependency_sources']} == set(manifest['unaccepted_p3_dependencies']),
         'P3 policy or held source list differs')
    for row in p3['dependency_sources']:
        need(pure(row) == pure(manifest['project_sources'][row['module']]), 'P3 held source fingerprint changed')
    ledger = {
        'schema': 'p15_AG_actual_results_after_collector_status_ledger_v1',
        'state': 'ACTUAL_AG_RESULTS_METADATA_AND_COLLECTOR_BOUND', 'execution_commit_AG': AG,
        'source_anchor_AF': AF, 'whole_P1_complete': False, 'whole_P1_5_complete': False,
        'formal_target_counts': counts, 'targets': rows, 'original_AG_runs': run_evidence,
        'actual_collector': {'compiler_job': cfg['collector']['compiler_job'], 'task': cfg['collector']['task'],
            'read': cfg['collector']['read'], 'public_summaries': cfg['collector']['public_summaries'],
            'selected_owners_revalidated': read['selected_owners_revalidated'],
            'sources': len(active), 'preserved_dependencies': len(active - accepted),
            'historical_suppliers': len(active & historical), 'new_lean_acceptance': False,
            'normal_or_kernel_commands_executed': 0, 'original_run_and_owner_identities_preserved': True},
        'P3_hold': p3, 'source_only_work': prior_snapshot['source_only_work'],
        'mathematical_boundaries': prior_snapshot['mathematical_boundaries'],
        'source_only_work_not_reclassified_by_new_run': True,
        'immutable_prior_snapshot_bindings': {'AE_before_collector': {'path': str(AE_BEFORE), **AE_BEFORE_PIN},
            'AE_after_collector': {'path': str(AE_AFTER), **AE_AFTER_PIN}},
        'evidence_bindings': {'manifest': {'path': str(MANIFEST_FILE), **MANIFEST_PIN},
            'actual_input_config': {'path': str(args.inputs), **fp(cfg_raw)}, 'metadata': cfg['metadata']},
        'actions_in_this_ledger_task': {'cloud_calls': 0, 'Git_calls': 0, 'Lean_commands': 0,
            'old_tests_rerun': False, 'P3_diagnostic_repeated': False, 'missing_source_search_repeated': False,
            'immutable_AE_snapshots_modified': False},
    }
    ledger_pin = save('STATUS_LEDGER.json', ledger)
    md = '# P1.5 — AG 实际结果与 collector 后续状态\n\n'
    md += '**已确认 %d / 21 个 formal targets 接受；整体 P1.5 仍未闭合。**\n\n' % counts['confirmed_accepted_targets_total']
    md += '接受计数由真实原始结果、metadata 与实际 collector 推导，没有预填两个新 owner 成功。\n\n'
    md += '| 目标（省略 ImbalancedChen.） | 实际状态 |\n| --- | --- |\n'
    for row in rows:
        md += '| ' + row['module'].removeprefix('ImbalancedChen.') + ' | ' + row['status'] + ' |\n'
    md += '\n## 原接受身份与范围\n\n'
    for group in read['original_runs']:
        md += '- `' + group['compiler_job'] + '`：exit ' + str(group['worker_exit_code']) + '；accepted ' + str(len(group['accepted_owners']))
        md += '，reused ' + str(len(group['reused_complete_selected_owners'])) + '；final stock recorded=' + str(group['original_final_stock_readiness']['recorded']) + '。\n'
    md += '\n联合只读范围 %d/%d，历史 suppliers %d；每个 owner 保持原 accepting run 和六回执/source+5/full21，collector 不生成新接受。\n' % (len(active), len(active - accepted), len(active & historical))
    md += '\n## 仍需继续的边界\n\n三个 proper-power owner 与 19 项 P3 dependencies 的既有 read-only device HOLD 保持。FixedM 准确原字节仍缺失；本次未重新搜索或诊断。\n\n'
    md += 'Literal historical medium 的同源字典和 full signed bound 尚未交付，`hSmoothSignedPP` 仍是 conditional theorem 的 premise。Residual、outer payment 与 AD 算术修正仍为 SOURCE ONLY，未因本次 owner 验收而升级。Same-kap 额外门与 `u * singularNormalization` 保持原范围。\n\n'
    md += '继续工作应以实际未接受目标及上述证明/依赖边界为准；保全所有已有接受身份，勿将相同源码、历史对象或静态 review 当作完整验收。AE 两版冻结快照未覆盖。\n'
    md_raw = md.encode(); (ROOT / 'CONTINUE_WORK.md').write_bytes(md_raw)
    save('LEDGER_BINDINGS.json', {'schema': 'p15_AG_actual_final_ledger_bindings_v1',
        'files': {'STATUS_LEDGER.json': ledger_pin, 'CONTINUE_WORK.md': fp(md_raw)},
        'actual_input_config': {'path': str(args.inputs), **fp(cfg_raw)},
        'metadata': cfg['metadata'], 'collector': cfg['collector'], 'formal_target_counts': counts,
        'prior_AE_snapshots_preserved': True})
    print(json.dumps({'state': ledger['state'], 'counts': counts, 'ledger': ledger_pin}, sort_keys=True))


if __name__ == '__main__':
    main()
