#!/usr/bin/env python3
"""Reuse the existing helper and exact audit runner; never install project sources."""
from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import traceback

PROJECT = Path('/workspace/blue-member-build')
GIT = Path('/workspace/goldbach-formalization')
BRANCH = 'codex/p1-final-acceptance-20261124'
ROOT = Path('/workspace/p1-complete-proof/20261124-resume/batch6-parallel-next8-second-frontier')
PREFIX = 'docs/p1/20261124/batch6-parallel/'
PLAN_SHA = '28a422661578e6fde5d9fa12a96e54a5e62b3a2ce58456be4a9016308c688171'
HELPER_SHA = '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5'
RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
AUDIT_SHA = '960852c9660f631da5b74358853a728098a3cbdfcc31d5c2eb2e8e0fdadf858b'
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)', re.M)
FAILED = re.compile(r'^\s*✖\ufe0f?\s+\[[^\]\r\n]+\]\s+Building\s+(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)', re.M)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')


def emit(stage, **fields):
    print(json.dumps({'batch6': stage, **fields}, ensure_ascii=False), flush=True)


def diagnostics(path):
    text = ANSI.sub('', Path(path).read_text(errors='replace'))
    lines = text.splitlines()
    hits = [i for i, line in enumerate(lines) if re.match(r'^error:\s+ImbalancedChen/', line)]
    sections = []
    for i in hits[:12]:
        end = i + 1
        while end < min(len(lines), i + 17):
            if re.match(r'^(?:[✔⚠ℹ✖]|(?:error|warning|info):)', lines[end]):
                break
            end += 1
        sections.append({'line': i + 1, 'text': '\n'.join(lines[i:end])[:1800]})
    return {'actual_built_modules': list(dict.fromkeys(BUILT.findall(text))),
            'actual_failed_modules': list(dict.fromkeys(FAILED.findall(text))),
            'project_error_count': len(hits), 'project_error_sections': sections}


def run(directory, name, argv, cwd=PROJECT, relay=False):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / (name + '.log')
    record = {'argv': [str(x) for x in argv], 'cwd': str(cwd), 'started_utc': now()}
    save(directory / (name + '-started.json'), record)
    emit('START', name=name, log=str(log))
    tick = time.monotonic()
    with log.open('xb') as output:
        if relay:
            child = subprocess.Popen(record['argv'], cwd=cwd, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
            for line in child.stdout:
                output.write(line)
                output.flush()
                if line.startswith(b'{"batch6":') and len(line) <= 30000:
                    print(line.decode(errors='replace').rstrip(), flush=True)
            code = child.wait()
        else:
            code = subprocess.run(record['argv'], cwd=cwd, stdout=output,
                                  stderr=subprocess.STDOUT).returncode
    record.update(exit_code=code, elapsed_seconds=time.monotonic() - tick,
                  finished_utc=now(), log=str(log), log_sha256=sha(log),
                  log_bytes=log.stat().st_size, **diagnostics(log))
    save(directory / (name + '-command.json'), record)
    emit('END', name=name, exit_code=code, seconds=round(record['elapsed_seconds'], 3),
         log_sha256=record['log_sha256'], built=record['actual_built_modules'],
         failed=record['actual_failed_modules'], project_error_count=record['project_error_count'])
    budget = 9000
    for section in record['project_error_sections']:
        if budget <= 0:
            break
        excerpt = section['text'][:budget]
        emit('PROJECT_ERROR', name=name, line=section['line'], text=excerpt)
        budget -= len(excerpt)
    return record


def helper():
    path = ROOT / 'inputs' / 'batch5_helpers.py'
    assert sha(path) == HELPER_SHA
    spec = importlib.util.spec_from_file_location('batch5_helpers', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)  # The original __main__ guard prevents its coordinator.
    assert module.PROJECT == PROJECT and module.GIT_REPO == GIT
    return module


def source_gate(h, plan, phase, targets):
    directory = ROOT / 'source-checks' / phase
    matched, records = [], []
    for module in targets:
        rel = h.module_path(module)
        path = PROJECT / rel
        data = path.read_bytes() if path.is_file() else None
        actual = h.digest(data) if data is not None else None
        expected = plan['normal_sources'][module]['sha256']
        row = {'module': module, 'expected_sha256': expected, 'actual_sha256': actual,
               'bytes': len(data) if data is not None else None, 'matches': actual == expected}
        if row['matches']:
            matched.append(module)
        else:
            if data is not None:
                exported = directory / 'actual-sources' / rel
                exported.parent.mkdir(parents=True, exist_ok=True)
                with exported.open('xb') as stream:
                    stream.write(data)
                row['original_source_export'] = str(exported)
                assert sha(exported) == actual
            row['action'] = 'PAUSE_AFFECTED_NORMAL_NO_SOURCE_OVERWRITE'
            emit('SOURCE_MISMATCH', phase=phase, **row)
        records.append(row)
    save(directory / 'SOURCE_BINDING.json', records)
    return matched


def snapshot(h, modules):
    return {m: sha(PROJECT / h.module_path(m)) if (PROJECT / h.module_path(m)).is_file()
            else None for m in sorted(modules)}


def worker(config, phase, lane):
    h = helper()
    assert sha(Path(__file__)) == config['driver_sha256']
    plan = json.loads((ROOT / 'inputs' / 'EXECUTION_PLAN.json').read_bytes())
    assert sha(ROOT / 'inputs' / 'EXECUTION_PLAN.json') == PLAN_SHA
    directory = ROOT / phase / ('lane-' + str(lane))
    directory.mkdir(parents=True, exist_ok=True)
    if phase == 'final-readiness':
        results = [run(directory, 'four-original-roots', h.guard(lane, ['lake', '--no-build', 'build'] +
                       ['+' + m + ':olean' for m in h.FOUR_ROOTS])),
                   run(directory, 'parent-wire', h.guard(lane, ['lake', '--no-build', 'build',
                       '+' + h.WIRE + ':olean']))]
        save(directory / 'READINESS_RESULT.json', {'commands': results,
             'protected_roots': h.check_roots(), 'row5_executed': False, 'whole_P1_complete': False})
        return 0  # A not-ready downstream root is recorded, not counted as a proof failure.
    if lane == 1:
        if not config['audit_prepared']:
            save(directory / 'AUDIT_SKIPPED.json', {'reason': 'PREPARATION_FAILED', 'whole_P1_complete': False})
            return 1
        root = Path(config['audit_receipt_root'])
        # Already inside state1 serializer; exact runner supplies all inner guards.
        result = run(directory, 'next8-full-audit', ['python3', config['audit_runner'],
                     '--plan', str(root / 'AUDIT_PLAN.json'), '--receipt-root', str(root), '--lane', '1'])
        return result['exit_code']
    results = []
    for group in plan['normal_groups']:
        name, requested = group['name'], group['targets']
        item = {'name': name, 'requested_targets': requested, 'status': 'PENDING'}
        results.append(item)
        try:
            selected = [m for m in requested if m in config['eligible_normal_targets']]
            selected = source_gate(h, plan, name + '-before-deps', selected)
            item['source_paused_targets'] = [m for m in requested if m not in selected]
            if not selected:
                item['status'] = 'SKIPPED_SOURCE_MISMATCH'
                continue
            graph, context = h.project_graph(PROJECT, selected)
            other_targets = (set(plan['normal_targets']) - set(selected)) & set(context)
            assert not other_targets, ('actual_normal_groups_not_independent', sorted(other_targets))
            save(directory / (name + '-PROJECT_SOURCE_CONTEXT.json'), context)
            deps = sorted({d for m in selected for d in graph[m]})
            assert deps
            ready = run(directory, name + '-directdeps', h.guard(0, ['lake', '--no-build', 'build'] +
                        ['+' + m + ':olean' for m in deps]))
            item['directdeps_command'] = ready
            if ready['exit_code']:
                item['status'] = 'SKIPPED_DIRECT_DEPENDENCIES_NOT_READY'
                continue
            selected = source_gate(h, plan, name + '-before-build', selected)
            item['source_paused_targets'] = [m for m in requested if m not in selected]
            if not selected:
                item['status'] = 'SKIPPED_SOURCE_CHANGED_BEFORE_BUILD'
                continue
            result = run(directory, name, h.guard(0, ['lake', 'build'] +
                         ['+' + m + ':olean' for m in selected]))
            item['normal_command'] = result
            item['actual_normal_targets'] = selected
            item['unexpected_built_project_modules'] = sorted(set(result['actual_built_modules']) - set(selected))
            item['all_context_sources_unchanged'] = snapshot(h, context) == {m: x['sha256'] for m, x in context.items()}
            item['status'] = ('NORMAL_COMMAND_EXIT0' if result['exit_code'] == 0 and
                not item['unexpected_built_project_modules'] and item['all_context_sources_unchanged']
                and not item['source_paused_targets'] else 'NORMAL_GROUP_INCOMPLETE_OR_FAILED')
        except Exception as error:
            item.update(status='GROUP_EXCEPTION', error_type=type(error).__name__, error=str(error),
                        traceback=traceback.format_exc())
            emit('GROUP_EXCEPTION', name=name, error=str(error))
        finally:
            save(directory / (name + '-RESULT.json'), item)
            emit('GROUP_RESULT', name=name, status=item['status'],
                 paused=item.get('source_paused_targets', []),
                 unexpected_built=item.get('unexpected_built_project_modules', []))
    save(directory / 'LANE_RESULT.json', {'groups': results,
         'independent_groups_continue_after_failure': True, 'normal_is_not_full_acceptance': True,
         'no_project_source_installs': True, 'whole_P1_complete': False})
    return 0 if all(x['status'] == 'NORMAL_COMMAND_EXIT0' for x in results) else 1


def coordinator(commit):
    ROOT.mkdir(exist_ok=False)
    inputs = ROOT / 'inputs'
    inputs.mkdir()
    executed = ROOT / 'executed-driver.py'
    executed.write_bytes(Path(__file__).read_bytes())
    original_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT).strip()
    original_status = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT)
    (ROOT / 'original-git-status-before.bin').write_bytes(original_status)
    assert run(ROOT, 'fetch-published-branch', ['git', 'fetch', 'origin', BRANCH], GIT)['exit_code'] == 0
    assert run(ROOT, 'commit-on-fetched-branch', ['git', 'merge-base', '--is-ancestor', commit, 'FETCH_HEAD'], GIT)['exit_code'] == 0
    reads = []

    def extract(rel, destination):
        argv = ['git', 'show', commit + ':' + rel]
        tick = time.monotonic()
        process = subprocess.run(argv, cwd=GIT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert process.returncode == 0, (rel, process.stderr.decode(errors='replace')[:2000])
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as stream:
            stream.write(process.stdout)
        reads.append({'argv': argv, 'cwd': str(GIT), 'exit_code': process.returncode,
                      'elapsed_seconds': time.monotonic() - tick, 'stdout_file': str(destination),
                      'stdout_sha256': sha(destination), 'bytes': len(process.stdout)})
        return process.stdout

    published_driver = extract(PREFIX + 'run_batch6_parallel.py', inputs / 'published-driver.py')
    assert published_driver == executed.read_bytes(), 'executed driver differs from selected published commit'
    plan = json.loads(extract(PREFIX + 'EXECUTION_PLAN.json', inputs / 'EXECUTION_PLAN.json'))
    assert sha(inputs / 'EXECUTION_PLAN.json') == PLAN_SHA
    assert plan['schema'] == 'p1_batch6_next8_second_frontier_v1'
    assert plan['project'] == str(PROJECT) and plan['git_repo'] == str(GIT)
    assert plan['fetch_branch'] == BRANCH and plan['receipt_root'] == str(ROOT)
    extract(plan['helper']['path'], inputs / 'batch5_helpers.py')
    h = helper()
    assert plan['helper']['sha256'] == HELPER_SHA
    assert plan['protected_original_four_roots'] == h.FOUR_ROOTS
    assert plan['runtime_states'] == [str(s) for s in h.STATES]
    h.check_roots()
    frontier = json.loads(extract(plan['frontier_source']['path'], inputs / 'NEXT_FRONTIER_GROUPS.json'))
    assert sha(inputs / 'NEXT_FRONTIER_GROUPS.json') == plan['frontier_source']['sha256']
    targets = frontier['second_ordinary_scope'] + ['ImbalancedChen.P2Winner9CompleteSeedChronology']
    assert targets == plan['normal_targets'] and len(targets) == len(set(targets)) == 18
    assert [m for group in plan['normal_groups'] for m in group['targets']] == targets
    assert len(plan['normal_groups']) == 3 and all(len(g['targets']) <= 6 for g in plan['normal_groups'])
    assert not set(targets) & set(plan['excluded_prior55_targets'] + plan['hard_exclusions'])
    assert not any('IntegerScales' in m for m in targets)
    for m in targets:
        row = plan['normal_sources'][m]
        assert row['path'] == h.module_path(m)
        data = extract(row['path'], inputs / 'published-sources' / row['path'])
        assert h.digest(data) == row['sha256']
        assert [x for x in h.imports(data) if x.startswith('ImbalancedChen.')] == row['imports']
    audit = json.loads(extract(plan['audit']['plan_path'], inputs / 'AUDIT_PLAN.json'))
    assert sha(inputs / 'AUDIT_PLAN.json') == AUDIT_SHA == plan['audit']['plan_sha256']
    assert audit['project'] == str(PROJECT) and audit['runtime_states'] == plan['runtime_states']
    assert audit['lanes'][0] == {'id': 0, 'modules': []} and audit['lanes'][1]['id'] == 1
    assert len(audit['modules']) == len(audit['lanes'][1]['modules']) == 8
    assert set(audit['modules']) == set(audit['lanes'][1]['modules'])
    assert len(audit['expected_project_sources']) == 317
    assert not set(targets) & set(audit['expected_project_sources'])
    assert not set(targets) & set(audit['reused_complete_modules'])
    runner = inputs / 'run_parallel_acceptance_multibatch.py'
    extract(plan['audit']['runner_path'], runner)
    assert sha(runner) == RUNNER_SHA == plan['audit']['runner_sha256']
    save(ROOT / 'GIT_SHOW_READS.json', reads)
    eligible = source_gate(h, plan, 'coordinator', targets)
    tracked = set(plan['normal_project_closure']) | set(audit['expected_project_sources']) | set(h.FOUR_ROOTS) | {h.WIRE}
    before = snapshot(h, tracked)
    save(ROOT / 'PROJECT_SOURCE_BEFORE.json', before)
    audit_mismatches = [{'module': m, 'expected_sha256': s, 'actual_sha256': before[m]}
                       for m, s in audit['expected_project_sources'].items() if before[m] != s]
    save(ROOT / 'AUDIT_SOURCE_PREFLIGHT.json', {'mismatches': audit_mismatches,
         'source_count': 317, 'original_runner_source_gate_unchanged': True})
    emit('SCOPE', normal_targets=len(targets), eligible_normal_targets=len(eligible),
         audit_targets=8, audit_source_count=317, audit_source_mismatches=audit_mismatches[:20])
    preparation = run(ROOT, 'next8-prepare-only', ['python3', str(runner), '--plan',
                      str(inputs / 'AUDIT_PLAN.json'), '--prepare-only'])
    config = {'commit': commit, 'driver_sha256': sha(executed), 'eligible_normal_targets': eligible,
              'audit_prepared': preparation['exit_code'] == 0, 'audit_runner': str(runner),
              'audit_receipt_root': audit['receipt_root'], 'plan_sha256': PLAN_SHA}
    save(ROOT / 'RUN_CONFIG.json', config)

    def launch(phase, lane):
        directory = ROOT / phase / ('lane-' + str(lane))
        directory.mkdir(parents=True, exist_ok=True)
        argv = h.serialize(lane, directory / 'VALIDATION_LANE.json', ['python3', str(executed),
                           '--commit', commit, '--worker', phase, '--lane', str(lane)])
        return run(directory, 'worker', argv, relay=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        lanes = list(pool.map(lambda lane: launch('execution', lane), [0, 1]))
    final = launch('final-readiness', 1)
    after = snapshot(h, tracked)
    save(ROOT / 'PROJECT_SOURCE_AFTER.json', after)
    source_stable = before == after
    git_stable = (subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT).strip() == original_head and
                  subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT) == original_status)
    result = {'commit': commit, 'finished_utc': now(), 'preparation': preparation,
              'lane_commands': lanes, 'final_readiness': final, 'protected_roots': h.check_roots(),
              'tracked_project_sources_unchanged': source_stable, 'original_dirty_git_checkout_unchanged': git_stable,
              'normal_target_count': 18, 'audit_target_count': 8, 'no_project_source_installs': True,
              'prior55_or_Seed90_scheduled': False, 'integer_scales_scheduled': False,
              'unpublished_part3_candidates_used': False, 'row5_executed': False, 'whole_P1_complete': False}
    save(ROOT / 'BATCH6_RESULT.json', result)
    emit('RESULT', lane_exit_codes=[x['exit_code'] for x in lanes], sources_unchanged=source_stable,
         dirty_checkout_unchanged=git_stable, receipt=str(ROOT / 'BATCH6_RESULT.json'))
    return 0 if all(x['exit_code'] == 0 for x in lanes + [final]) and source_stable and git_stable else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--worker', choices=['execution', 'final-readiness'])
    parser.add_argument('--lane', type=int, choices=[0, 1])
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit), 'use the full reviewed published commit'
    sys.setrecursionlimit(10000)
    try:
        if args.worker:
            assert args.lane is not None
            config = json.loads((ROOT / 'RUN_CONFIG.json').read_text())
            assert config['commit'] == args.commit
            return worker(config, args.worker, args.lane)
        assert args.lane is None
        return coordinator(args.commit)
    except Exception as error:
        record = {'phase': args.worker or 'coordinator', 'lane': args.lane,
                  'error_type': type(error).__name__, 'error': str(error), 'utc': now(),
                  'whole_P1_complete': False}
        path = ROOT / ('FAILURE-' + record['phase'] + '-' + str(args.lane) + '.json')
        if ROOT.exists() and not path.exists():
            save(path, record)
        emit('EXCEPTION', **record)
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
