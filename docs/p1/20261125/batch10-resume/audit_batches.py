#!/usr/bin/env python3
"""Freeze small e9 plans; execute one populated lane, without changing e9.

Normal compilation and proof-source installation are never invoked. Interrupted
lanes are held for inspection. Complete validated lanes are the resume boundary.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
DRIVER_SHA = '63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71'
COMPLETE = 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
HIGHER = 'ImbalancedChen.P2OriginalSixthHigherMoments'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def subset_plan(base, selected, receipt_root, parent_sha, completed):
    need(0 < len(selected) <= 8 and len(set(selected)) == len(selected), 'invalid chunk size or duplicate owner')
    need(set(selected) <= set(base['modules']), 'owner outside parent normal plan')
    need(not set(selected) & set(completed), 'selected/completed overlap')
    plan = json.loads(json.dumps(base))
    plan['modules'] = {m: base['modules'][m] for m in selected}
    keys = {base['modules'][m]['normal_log'] for m in selected}
    plan['normal_logs'] = {k: base['normal_logs'][k] for k in sorted(keys)}
    closure = {d for m in selected for d in base['modules'][m]['project_closure']}
    plan['expected_project_sources'] = {m: base['expected_project_sources'][m] for m in sorted(closure)}
    plan['lanes'] = [{'id': 0, 'modules': selected[:4]}, {'id': 1, 'modules': selected[4:]}]
    plan['receipt_root'] = str(receipt_root)
    plan['audit_parent_plan_sha256'] = parent_sha
    plan['reused_complete_modules'] = sorted(set(base['reused_complete_modules']) | set(completed))
    all_higher = {m for m in base['modules'] if m.startswith(HIGHER)} | set(base['higher_missing_normal_modules'])
    plan['higher_audit_subset_complete'] = bool(all_higher) and all_higher <= set(selected)
    plan['higher_audit_subset_missing'] = sorted(all_higher - set(selected))
    plan['whole_P1_complete'] = False
    return plan


def populated_lanes(plan):
    return [lane['id'] for lane in plan['lanes'] if lane['modules']]


def lane_state(lane):
    if (lane / 'VALIDATION_RESULTS.json').exists():
        return 'RESULT_PRESENT_REQUIRES_VALIDATION'
    if not lane.exists() or {p.name for p in lane.iterdir()} <= {'MODULES.json'}:
        return 'UNSTARTED'
    return 'PARTIAL_REQUIRES_INSPECTION'


def validate_parent_bindings(base, d, h):
    need(base['audit_template'] == {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA},
         'parent audit template differs from pinned full-owned template')
    need(base['runtime_states'] == list(map(str, h.STATES)), 'parent runtime states differ from pinned helper')


def validate_normal_owner(module, base, d, h):
    need(h is not None, 'pinned source/context helper required')
    log = base['normal_logs'][base['modules'][module]['normal_log']]
    normal = json.loads((Path(log['path']).parent.parent / 'NORMAL_PASS.json').read_bytes())
    need(normal['normal_command']['log'] == log['path'] and
         normal['normal_command']['log_sha256'] == log['sha256'], 'durable normal receipt differs from parent log')
    project = Path(base['project'])
    graph, _ = h.project_graph(project, [module])
    need(set(graph) == set(base['modules'][module]['project_closure']), 'normal dependency closure differs from parent')
    sources = {m: base['expected_project_sources'][m] for m in graph}
    context = d.dependency_binding(project, module, graph, sources, h)
    d.validate_normal(project, module, normal, context, h)


def completed_owners(path, base, d, h):
    """Verify actual complete e9 evidence and current objects before reuse."""
    lane = path.parent
    plan_path = lane.parent / 'AUDIT_PLAN.json'
    plan = json.loads(plan_path.read_bytes())
    result = json.loads(path.read_bytes())
    lane_id = int(lane.name.removeprefix('lane-'))
    selected = plan['lanes'][lane_id]['modules']
    need(selected and set(selected) <= set(base['modules']), 'receipt owner scope')
    need(plan['audit_template'] == base['audit_template'] and plan['runtime_states'] == base['runtime_states'],
         'receipt template/runtime differs from parent')
    need(result['audit_template_sha256'] == base['audit_template']['sha256'] and
         result['runtime_state'] == base['runtime_states'][lane_id] and
         result['runtime_state_sha256'] == d.fingerprint(Path(result['runtime_state']))['sha256'], 'receipt runtime/template binding changed')
    need(result['status'] == COMPLETE and result['plan_sha256'] == d.fingerprint(plan_path)['sha256'], 'receipt plan/status binding')
    binding = json.loads((lane.parent / 'PLAN_BINDING.json').read_bytes())
    need(binding['runner_sha256'] == d.RUNNER_SHA and binding['sha256'] == result['plan_sha256'], 'receipt runner binding')
    need(all(plan['modules'][m] == base['modules'][m] for m in selected), 'receipt module differs from parent')
    expected = {m: base['modules'][m]['source_sha256'] for m in selected}
    need(result['modules'] == expected, 'receipt source scope')
    project = Path(base['project'])
    need(plan['project'] == str(project), 'receipt project differs')
    snapshots = {m: d.snapshot(project, m) for m in selected}
    need(result['source_plus_five_outputs'] == snapshots and
         json.loads((lane / 'BEFORE_KERNEL.json').read_bytes()) == snapshots, 'receipt outputs changed')
    closure = {x for m in selected for x in base['modules'][m]['project_closure']}
    sources = {m: base['expected_project_sources'][m] for m in sorted(closure)}
    need(result['project_dependency_sources'] == sources, 'receipt dependency scope')
    need(all(d.fingerprint(project / (m.replace('.', '/') + '.lean'))['sha256'] == value
             for m, value in sources.items()), 'receipt dependency sources changed')
    for key in {base['modules'][m]['normal_log'] for m in selected}:
        log = base['normal_logs'][key]
        need(plan['normal_logs'][key] == log, 'receipt normal provenance changed')
        normal = Path(log['path'])
        need(d.fingerprint(normal)['sha256'] == log['sha256'] and
             set(d.BUILT.findall(d.ANSI.sub('', normal.read_text()))) == set(log['expected_built_modules']), 'receipt normal log changed')
    guard = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', plan['runtime_states'][lane_id]]
    def command(rec, tail):
        need(rec['exit_code'] == 0 and rec['argv'] == guard + tail and rec['cwd'] == str(project), 'receipt command scope/status')
        need(Path(rec['log']).name == rec['log'], 'receipt log path')
        log = lane / rec['log']
        need(d.fingerprint(log)['sha256'] == rec['log_sha256'], 'receipt raw log changed')
        return log.read_text()
    need(set(result['kernel_commands']) == set(selected), 'receipt kernel owner scope')
    for m in selected:
        command(result['kernel_commands'][m], ['lake', 'env', 'leanchecker', '--verbose', m])
    readiness = ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in selected]
    command(result['stock_readiness_before'], readiness)
    command(result['stock_readiness_after'], readiness)
    text = command(result['audit_command'], ['lake', 'env', 'lean', '-DmaxRecDepth=100000',
        '-DmaxHeartbeats=4000000', '--root=' + str(lane), str(lane / 'PublicAudit.lean')])
    records = [json.loads(s) for s in re.findall(r'AUDIT_RECORD (\{[^\n]+\})', text)]
    inventories = [json.loads(s)['names'] for s in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})', text)]
    names = [r['name'] for r in records]
    need(len(inventories) == 1 and sorted(names) == sorted(inventories[0]) and len(set(names)) == len(names), 'receipt owned inventory')
    need(records == json.loads((lane / 'OWNED_EXPORTS.json').read_bytes()) and
         {r['module'] for r in records} == set(selected), 'receipt owned owner scope')
    need(all(r['kind'] != 'axiom' and set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in records)
         and not any(s in text for s in ['sorryAx', '…', '⋯', '...']), 'receipt axiom/type audit')
    need(result['total_owned_exports'] == len(records) and
         result['total_public_exports'] == sum(not r['is_private'] for r in records), 'receipt owned counts')
    for flag in ['full_owned_including_private_generated', 'only_standard_axioms', 'pp_all_true_no_elisions',
                 'source_plus_five_outputs_unchanged_across_kernel_and_audit', 'successful_normal_not_repeated']:
        need(result.get(flag) is True, 'receipt acceptance flag: ' + flag)
    for module in selected:
        validate_normal_owner(module, base, d, h)
    return set(selected)


def inspect(manifest, base, d, h):
    completed, rows = set(), []
    for path in manifest['reused_receipts']:
        completed |= completed_owners(Path(path), base, d, h)
    for chunk in manifest['chunks']:
        path = Path(chunk['plan'])
        need(d.fingerprint(path)['sha256'] == chunk['sha256'], 'frozen subset plan changed')
        plan = json.loads(path.read_bytes())
        for lane_id in populated_lanes(plan):
            lane = Path(plan['receipt_root']) / ('lane-' + str(lane_id))
            state = lane_state(lane)
            if state == 'RESULT_PRESENT_REQUIRES_VALIDATION':
                need(d.fingerprint(lane.parent / 'AUDIT_PLAN.json')['sha256'] == chunk['sha256'], 'completed lane frozen plan differs')
                owners = completed_owners(lane / 'VALIDATION_RESULTS.json', base, d, h)
                need(not completed & owners, 'duplicate completed audit owners')
                completed |= owners
                state = 'COMPLETE_VALIDATED'
            rows.append({'key': chunk['name'] + ':' + str(lane_id), 'state': state,
                         'modules': plan['lanes'][lane_id]['modules'], 'plan': str(path), 'lane': str(lane)})
    need(completed <= set(base['modules']), 'completed owners outside parent')
    return completed, rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    action = ap.add_mutually_exclusive_group(required=True)
    action.add_argument('--prepare', action='store_true')
    action.add_argument('--run-next', action='store_true')
    action.add_argument('--summary', action='store_true')
    ap.add_argument('--plan', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--driver', type=Path)
    ap.add_argument('--reuse-root', type=Path, action='append', default=[])
    ap.add_argument('--retry-partials', action='store_true', help='Explicitly freeze new attempts after inspecting preserved partial lanes.')
    ap.add_argument('--lane-key', help='Execute this exact unstarted chunk-NNN:lane rather than choosing automatically.')
    ap.add_argument('--source-repo', type=Path, default=Path('/workspace/goldbach-formalization'))
    args = ap.parse_args()
    out = args.out.resolve()
    manifest = None if args.prepare else json.loads((out / 'MANIFEST.json').read_bytes())
    need(not args.prepare or args.plan is not None, '--prepare requires the generated parent --plan')
    parent = args.plan.resolve() if args.prepare else out / 'PARENT_PLAN.json'
    raw = parent.read_bytes()
    base = json.loads(raw)
    driver_path = (args.driver or (parent.parents[2] / 'executed-driver.py' if args.prepare else Path(manifest['driver']))).resolve()
    import hashlib
    need(hashlib.sha256(driver_path.read_bytes()).hexdigest() == DRIVER_SHA, 'unchanged normal driver required')
    spec = importlib.util.spec_from_file_location('unchanged_batch10_normal_driver', driver_path)
    d = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(d)
    need(base['schema'] == 'p1_completed_normal_multibatch_audit_plan_v1' and
         base['source_review_head'] == d.SOURCE_COMMIT, 'parent plan schema/source snapshot')
    h = d.load_helper(d.git_read(args.source_repo, d.HELPER_PATH))
    validate_parent_bindings(base, d, h)
    if args.prepare:
        need(not out.exists(), 'new subset output directory must be absent')
        runner_raw = (parent.parent / 'run_parallel_acceptance_multibatch.py').read_bytes()
        need(d.sha(runner_raw) == d.RUNNER_SHA, 'unchanged e9 runner required')
        reused, reused_paths, partials = set(), [], []
        for old in args.reuse_root:
            old_manifest = json.loads((old / 'MANIFEST.json').read_bytes())
            owners, lanes = inspect(old_manifest, base, d, h)
            reused |= owners
            reused_paths.extend(old_manifest['reused_receipts'])
            reused_paths.extend(str(Path(r['lane']) / 'VALIDATION_RESULTS.json') for r in lanes if r['state'] == 'COMPLETE_VALIDATED')
            partials.extend(r for r in lanes if r['state'] == 'PARTIAL_REQUIRES_INSPECTION')
        need(not partials or args.retry_partials, 'partial lanes require inspection and explicit --retry-partials into a fresh subset root')
        remaining = sorted(set(base['modules']) - reused)
        d.write_frozen(out / 'PARENT_PLAN.json', raw)
        d.write_frozen(out / 'run_parallel_acceptance_multibatch.py', runner_raw)
        (out / 'receipts').mkdir()
        manifest = {'parent_plan_sha256': d.sha(raw), 'driver': str(driver_path), 'driver_sha256': DRIVER_SHA,
                    'runner_sha256': d.RUNNER_SHA, 'reused_receipts': sorted(set(reused_paths)),
                    'preserved_partial_lanes': partials, 'chunks': [], 'whole_P1_complete': False}
        for index in range(0, len(remaining), 8):
            name = 'chunk-%03d' % (index // 8)
            path = out / 'plans' / (name + '.json')
            plan = subset_plan(base, remaining[index:index + 8], out / 'receipts' / name, d.sha(raw), reused)
            d.save(path, plan)
            manifest['chunks'].append({'name': name, 'plan': str(path), 'sha256': d.fingerprint(path)['sha256']})
        d.save(out / 'MANIFEST.json', manifest)
    need(d.sha(raw) == manifest['parent_plan_sha256'], 'frozen parent plan changed')
    need(d.fingerprint(out / 'run_parallel_acceptance_multibatch.py')['sha256'] == d.RUNNER_SHA, 'frozen e9 runner changed')
    completed, rows = inspect(manifest, base, d, h)
    if args.run_next:
        pending = [r for r in rows if r['state'] == 'UNSTARTED']
        partials = [r for r in rows if r['state'] == 'PARTIAL_REQUIRES_INSPECTION']
        if args.lane_key:
            pending = [r for r in pending if r['key'] == args.lane_key]
            need(len(pending) == 1, 'requested lane is not exactly one unstarted populated lane')
        else:
            need(not partials, 'partial lanes held; inspect them before choosing an explicit untouched lane or a new subset attempt')
        if pending:
            row = pending[0]
            plan_path = Path(row['plan'])
            plan = json.loads(plan_path.read_bytes())
            need(Path(base['project']) == d.PROJECT, 'audit execution requires original cloud project')
            d.runtime_binding(h)
            need(plan['runtime_states'] == list(map(str, h.STATES)), 'original two runtime states required')
            runner = out / 'run_parallel_acceptance_multibatch.py'
            receipt = Path(plan['receipt_root'])
            if not receipt.exists():
                subprocess.run(['python3', '-B', str(runner), '--plan', str(plan_path), '--prepare-only'], cwd=d.PROJECT, check=True)
            need(d.fingerprint(receipt / 'AUDIT_PLAN.json')['sha256'] == d.fingerprint(plan_path)['sha256'], 'prepared plan differs')
            lane_id = int(row['key'].rsplit(':', 1)[1])
            need(lane_state(Path(row['lane'])) == 'UNSTARTED', 'lane became partial before execution')
            for module in row['modules']:
                validate_normal_owner(module, base, d, h)
            argv = h.serialize(lane_id, Path(row['lane']) / 'VALIDATION_LANE.json',
                ['python3', '-B', str(runner), '--plan', str(receipt / 'AUDIT_PLAN.json'),
                 '--receipt-root', str(receipt), '--lane', str(lane_id)])
            print(json.dumps({'stage': 'AUDIT_LANE_START', 'key': row['key'], 'modules': row['modules']}), flush=True)
            code = subprocess.run(argv, cwd=d.PROJECT).returncode
            need(code == 0, 'audit lane stopped; preserve partial receipt and inspect: ' + row['key'])
            completed, rows = inspect(manifest, base, d, h)
    higher_done = sorted(m for m in completed if m.startswith(HIGHER))
    higher_expected = {m for m in base['modules'] if m.startswith(HIGHER)} | set(base['higher_missing_normal_modules'])
    summary = {'status': 'ALL_SELECTED_OWNERS_ACCEPTED' if completed == set(base['modules']) else 'AUDIT_PROGRESS',
               'normal_scope_in_parent': len(base['modules']), 'batch10_source_scope': 75,
               'accepted_owners': len(completed), 'higher_accepted_owners': len(higher_done), 'higher_required_owners': 53,
               'higher_partition_accepted': len(higher_expected) == 53 and higher_expected <= completed,
               'normal_modules_without_complete_audit': sorted(set(base['modules']) - completed),
               'lanes': rows, 'whole_P1_complete': False}
    print(json.dumps(summary), flush=True)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'AUDIT_ORCHESTRATION_HELD', 'error_type': type(error).__name__,
                          'error': str(error), 'whole_P1_complete': False}), flush=True)
        raise SystemExit(1)
