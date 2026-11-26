#!/usr/bin/env python3
"""Stage the reviewed batch5 sources, then use the two existing validation lanes.

Only the coordinator fetches/extracts/installs sources. Start it on the root-owned
idle main cloud. Workers never change sources or create an alternative checker.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import traceback

PROJECT = Path('/workspace/blue-member-build')
GIT_REPO = Path('/workspace/goldbach-formalization')
BRANCH = 'codex/p1-final-acceptance-20261124'
ROOT = Path('/workspace/p1-complete-proof/20261124-resume/batch5-parallel-higher-audit-frontier')
STATES = [Path('/workspace/blue-build-tools/member-runtime-evidence/state.json'),
          Path('/workspace/blue-build-tools/runtime-evidence/state.json')]
SERIALIZER = '/workspace/blue-build-tools/serialize_validation_lane.py'
GUARD = '/workspace/blue-build-tools/run_guarded.py'
PREFIX = 'docs/p1/20261124/'
ALIGNMENT = PREFIX + 'batch5-source-alignment/'
AUDIT_PREFIX = PREFIX + 'rebound24-audit/'
RUNNER_PATH = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
HIGHER = 'ImbalancedChen.P2OriginalSixthHigherMoments'
PARENTS = ['ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit',
           'ImbalancedChen.P1OriginalFifthEnvelopeTerminalReduction']
WIRE = 'ImbalancedChen.P5OriginalChildIntegerWireBinding'
FOUR_ROOTS = {
    'ImbalancedChen.P1OriginalFinalPolicyRawBound': '4caf892e8278a1213afb632c77c89588c34c46b92d5f340c61ed4ec752bdd377',
    'ImbalancedChen.P1OriginalFinalPolicyStructure': 'faa6df3c9f4dc5a49552ed52e2dd19900c2b9b1a9340bd8e4a716164558e9f51',
    'ImbalancedChen.P1OriginalFinalPolicyAncestorReads': '4757c28c53ae4dfbd33bb799ca0d43c43832f0519042fed4d3c828e316922a03',
    'ImbalancedChen.P1OriginalCompleteFormalProof': '2513190e848303d71b9ff7e9a4aeef8e8b3c10f656d19bb52b5eb739084f79cb',
}
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)', re.M)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')


def emit(stage, **fields):
    print(json.dumps({'batch5': stage, **fields}, ensure_ascii=False), flush=True)


def module_path(module):
    assert re.fullmatch(r'ImbalancedChen(?:\.[A-Za-z0-9_]+)+', module), module
    return module.replace('.', '/') + '.lean'


def error_excerpt(path):
    lines = ANSI.sub('', Path(path).read_text(errors='replace')).splitlines()
    hits = [i for i, line in enumerate(lines)
            if re.search(r'error:|failed|AssertionError|Traceback|panic|exception', line, re.I)]
    indexes = sorted({j for i in hits[:12] for j in range(max(0, i - 1), min(len(lines), i + 4))})
    if not indexes:
        indexes = list(range(max(0, len(lines) - 12), len(lines)))
    return '\n'.join(lines[i][:800] for i in indexes[:55])[:7000]


def run_stage(directory, name, argv, cwd=PROJECT, relay=False):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    log = directory / (name + '.log')
    started = {'argv': [str(x) for x in argv], 'cwd': str(cwd), 'started_utc': now()}
    save(directory / (name + '-started.json'), started)
    emit('START', name=name, log=str(log))
    tick = time.monotonic()
    with log.open('xb') as output:
        if relay:
            process = subprocess.Popen(started['argv'], cwd=cwd, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT)
            for line in process.stdout:
                output.write(line)
                output.flush()
                if line.startswith(b'{"batch5":') and len(line) <= 12000:
                    print(line.decode(errors='replace').rstrip(), flush=True)
            code = process.wait()
        else:
            code = subprocess.run(started['argv'], cwd=cwd, stdout=output,
                                  stderr=subprocess.STDOUT).returncode
    result = {**started, 'exit_code': code, 'elapsed_seconds': time.monotonic() - tick,
              'finished_utc': now(), 'log': str(log), 'log_sha256': file_sha(log),
              'log_bytes': log.stat().st_size}
    save(directory / (name + '-command.json'), result)
    emit('END', name=name, exit_code=code, seconds=round(result['elapsed_seconds'], 3),
         log_sha256=result['log_sha256'])
    if code:
        emit('ERROR_EXCERPT', name=name, text=error_excerpt(log))
    return result


def imports(data):
    # Reused from the existing recover_p1_sources.py import lexer.
    source = data.decode('utf-8-sig')
    out, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end == -1 else end
        else:
            if not depth or source[i] == '\n':
                out.append(source[i] if not depth else '\n')
            i += 1
    result = []
    for line in ''.join(out).splitlines():
        match = re.match(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$', line)
        if match:
            for name in match.group(1).split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name):
                    result.append(name)
                else:
                    raise ValueError('Unrecognized import syntax: ' + line)
    return list(dict.fromkeys(result))


def closure(graph, roots):
    seen, active = set(), set()

    def visit(module):
        assert module not in active, ('import_cycle', module)
        if module in seen:
            return
        active.add(module)
        for dep in graph[module]:
            visit(dep)
        active.remove(module)
        seen.add(module)

    for module in roots:
        visit(module)
    return seen


def assert_disjoint_targets(graph, left, right):
    conflicts = (set(left) & closure(graph, right)) | (set(right) & closure(graph, left))
    assert not conflicts, ('cross_lane_target_dependency', sorted(conflicts))


def project_graph(project, roots):
    graph, sources = {}, {}

    def visit(module):
        if module in graph:
            return
        path = project / module_path(module)
        data = path.read_bytes()
        deps = [x for x in imports(data) if x.startswith('ImbalancedChen.')]
        graph[module] = deps
        sources[module] = {'sha256': digest(data), 'bytes': len(data), 'imports': deps}
        for dep in deps:
            visit(dep)

    for module in roots:
        visit(module)
    closure(graph, roots)
    return graph, sources


def install_sources(project, updates, payloads, backup_root):
    records, changes = [], []
    assert len({row['module'] for row in updates}) == len(updates)
    # Validate the complete batch before backing up or writing any file.
    for row in updates:
        rel = row['path']
        assert rel == module_path(row['module'])
        source = project / rel
        data = source.read_bytes()
        payload = payloads[rel]
        assert digest(payload) == row['after_sha256'], ('published_payload', rel)
        requested = row['cloud_source_mutation_required']
        assert type(requested) is bool
        already_after = digest(data) == row['after_sha256']
        mutable = requested and not already_after
        expected = row['before_sha256'] if mutable else row['after_sha256']
        assert digest(data) == expected, ('actual_source_precondition', rel, expected, digest(data))
        stamp = (source.stat().st_mtime_ns, source.stat().st_ino, source.stat().st_size)
        records.append({**row, 'actual_before_sha256': digest(data), 'mutated': mutable,
                        'action': 'INSTALL_BACKED_UP_PREIMAGE' if mutable else
                        ('ALREADY_AFTER_NOOP' if requested else 'VERIFY_EXISTING_REUSE')})
        if mutable:
            changes.append((source, rel, data, payload))
        else:
            records[-1]['unchanged_stat_before'] = stamp
    for source, rel, data, payload in changes:
        target = backup_root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as output:
            output.write(data)
    for source, rel, data, payload in changes:
        assert source.read_bytes() == data, ('source_changed_before_install', rel)
    for source, rel, data, payload in changes:
        temporary = source.with_name(source.name + '.batch5-candidate-tmp')
        with temporary.open('xb') as output:
            output.write(payload)
        temporary.chmod(source.stat().st_mode & 0o777)
        os.replace(temporary, source)
    for row in records:
        source = project / row['path']
        row['actual_after_sha256'] = file_sha(source)
        assert row['actual_after_sha256'] == row['after_sha256']
        if not row['mutated']:
            assert tuple(row['unchanged_stat_before']) == (
                source.stat().st_mtime_ns, source.stat().st_ino, source.stat().st_size)
    return records


def check_roots():
    actual = {m: file_sha(PROJECT / module_path(m)) for m in FOUR_ROOTS}
    assert actual == FOUR_ROOTS, ('protected_four_roots_changed', actual)
    return actual


def guard(lane, args):
    return ['python3', GUARD, '--state', str(STATES[lane])] + list(args)


def serialize(lane, receipt, args):
    return ['python3', SERIALIZER, '--state', str(STATES[lane]),
            '--receipt', str(receipt)] + list(args)


def readiness(directory, name, lane, modules):
    assert modules, ('empty_readiness_target_set', name)
    return run_stage(directory, name, guard(lane, ['lake', '--no-build', 'build'] +
                                            ['+' + m + ':olean' for m in modules]))


def worker(config, phase, lane):
    assert file_sha(Path(__file__)) == config['driver_sha256']
    directory = ROOT / phase / ('lane-' + str(lane))
    directory.mkdir(parents=True, exist_ok=True)
    if phase == 'preflight':
        deps = config['direct_deps'][str(lane)]
        result = readiness(directory, 'all-project-direct-deps', lane, deps)
        return result['exit_code']
    if phase == 'final-readiness':
        results = [readiness(directory, 'four-original-roots', lane, list(FOUR_ROOTS)),
                   readiness(directory, 'parent-wire', lane, [WIRE])]
        save(directory / 'READINESS_RESULT.json', {
            'commands': results, 'protected_roots': check_roots(),
            'row5_executed': False, 'whole_P1_complete': False})
        # Out-of-date roots are a recorded frontier, not new proof failures.
        return 0
    results = []
    if lane == 1:
        # Already inside state1 serializer. The exact audit runner adds its own
        # run_guarded calls; do not add another guard or serializer here.
        audit_root = Path(config['audit_receipt_root'])
        results.append(run_stage(directory, 'audit24', [
            'python3', config['audit_runner'], '--plan', str(audit_root / 'AUDIT_PLAN.json'),
            '--receipt-root', str(audit_root), '--lane', '1']))
        batches = [('parent-0-normal', [PARENTS[0]]),
                   ('parent-1-normal', [PARENTS[1]]),
                   ('first14-normal', config['first14'])]
    else:
        batches = [('higher-full-module-normal', [HIGHER])]
    for name, targets in batches:
        deps = sorted({d for m in targets for d in config['graph'][m]})
        ready = readiness(directory, name + '-deps', lane, deps)
        results.append(ready)
        if ready['exit_code']:
            save(directory / (name + '-SKIPPED.json'), {'reason': 'DIRECT_DEPENDENCIES_NOT_READY',
                                                       'targets': targets})
            continue
        for m in targets:
            assert file_sha(PROJECT / module_path(m)) == config['normal_source_sha256'][m]
        result = run_stage(directory, name, guard(lane, ['lake', 'build'] +
                                                  ['+' + m + ':olean' for m in targets]))
        text = ANSI.sub('', Path(result['log']).read_text(errors='replace'))
        built = sorted(set(BUILT.findall(text)))
        unexpected = sorted(set(built) - set(targets))
        save(directory / (name + '-HEADERS.json'), {
            'targets': targets, 'actual_built_modules': built,
            'unexpected_built_project_modules': unexpected, 'log_sha256': result['log_sha256']})
        result['unexpected_built_project_modules'] = unexpected
        results.append(result)
        if unexpected:
            emit('UNEXPECTED_BUILD', name=name, modules=unexpected)
    save(directory / 'LANE_RESULT.json', {'lane': lane, 'stages': results,
        'audit_failure_does_not_suppress_independent_normal': True,
        'higher_probes_repeated': False, 'row5_executed': False,
        'whole_P1_complete': False})
    return 0 if all(r['exit_code'] == 0 and not r.get('unexpected_built_project_modules')
                    for r in results) else 1


def coordinator(commit):
    ROOT.mkdir(exist_ok=False)
    inputs = ROOT / 'inputs'
    inputs.mkdir()
    executed = ROOT / 'executed-driver.py'
    executed.write_bytes(Path(__file__).read_bytes())
    start = now()
    original_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT_REPO).strip()
    original_status = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT_REPO)
    (ROOT / 'original-git-status-before.bin').write_bytes(original_status)
    fetch = run_stage(ROOT, 'fetch-published-branch', ['git', 'fetch', 'origin', BRANCH], GIT_REPO)
    assert fetch['exit_code'] == 0
    ancestry = run_stage(ROOT, 'commit-on-fetched-branch',
                        ['git', 'merge-base', '--is-ancestor', commit, 'FETCH_HEAD'], GIT_REPO)
    assert ancestry['exit_code'] == 0
    reads = []

    def extract(rel, destination):
        argv = ['git', 'show', commit + ':' + rel]
        tick = time.monotonic()
        process = subprocess.run(argv, cwd=GIT_REPO, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert process.returncode == 0, (rel, process.stderr.decode(errors='replace')[:2000])
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as output:
            output.write(process.stdout)
        reads.append({'argv': argv, 'cwd': str(GIT_REPO), 'exit_code': process.returncode,
                      'elapsed_seconds': time.monotonic() - tick, 'stdout_file': str(destination),
                      'stdout_sha256': digest(process.stdout), 'bytes': len(process.stdout)})
        return process.stdout

    update = json.loads(extract(ALIGNMENT + 'SOURCE_UPDATE.json', inputs / 'SOURCE_UPDATE.json'))
    frontier = json.loads(extract(ALIGNMENT + 'NEXT_FRONTIER_GROUPS.json', inputs / 'NEXT_FRONTIER_GROUPS.json'))
    plan_bytes = extract(AUDIT_PREFIX + 'AUDIT_PLAN.json', inputs / 'AUDIT_PLAN.json')
    plan = json.loads(plan_bytes)
    binding = json.loads(extract(AUDIT_PREFIX + 'PUBLICATION_BINDING.json', inputs / 'PUBLICATION_BINDING.json'))
    runner = inputs / 'run_parallel_acceptance_multibatch.py'
    extract(RUNNER_PATH, runner)
    assert digest(plan_bytes) == binding['plan_sha256']
    assert file_sha(runner) == RUNNER_SHA == binding['original_exact_runner_sha256']
    assert plan['project'] == str(PROJECT) and plan['runtime_states'] == [str(x) for x in STATES]
    assert [x['id'] for x in plan['lanes']] == [0, 1]
    assert plan['lanes'][0]['modules'] == [] and len(plan['lanes'][1]['modules']) == 24
    audit24 = plan['lanes'][1]['modules']
    assert set(plan['modules']) == set(audit24)
    assert len(plan['reused_complete_modules']) == 90
    assert not set(audit24) & set(plan['reused_complete_modules'])
    protected = {'ImbalancedChen.' + m: s for m, s in update['protected_original_four_roots_sha256'].items()}
    assert protected == FOUR_ROOTS
    check_roots()
    first14 = frontier['first_recommended_scope']
    assert len(first14) == len(set(first14)) == 14
    normal_targets = [HIGHER] + PARENTS + first14
    assert len(set(normal_targets)) == 17
    excluded = set(frontier['same_source_reuse_targets']) | set(plan['reused_complete_modules'])
    assert not set(normal_targets) & excluded
    assert not set(first14 + PARENTS) & set(frontier['hard_exclusions'])
    updates = update['updates']
    by_module = {x['module']: x for x in updates}
    mutable = {x['module'] for x in updates if x['cloud_source_mutation_required']}
    assert {HIGHER, *PARENTS} <= mutable <= set(normal_targets)
    assert sum(not x['cloud_source_mutation_required'] for x in updates) == 13
    payloads = {}
    for row in updates:
        assert row['path'] == module_path(row['module'])
        payloads[row['path']] = extract(row['path'], inputs / 'sources' / row['path'])
    expected_sources = {}
    frontier_rows = {x['module']: x for x in frontier['frontier']}
    for m in normal_targets:
        rel = module_path(m)
        if rel not in payloads:
            payloads[rel] = extract(rel, inputs / 'sources' / rel)
        expected_sources[m] = (by_module[m]['after_sha256'] if m in by_module
                               else frontier_rows[m]['source_sha256'])
        assert digest(payloads[rel]) == expected_sources[m], ('normal_git_source', m)
        if m not in mutable:
            assert file_sha(PROJECT / rel) == expected_sources[m], ('normal_cloud_source', m)
    save(ROOT / 'GIT_SHOW_READS.json', reads)
    installed = install_sources(PROJECT, updates, payloads, ROOT / 'source-backups')
    save(ROOT / 'SOURCE_INSTALL.json', {'commit': commit, 'sources': installed,
                                      'protected_roots_after': check_roots(),
                                      'original_dirty_git_worktree_not_checked_out': True})
    graph, sources = project_graph(PROJECT, normal_targets + audit24)
    assert_disjoint_targets(graph, [HIGHER], PARENTS + first14)
    assert not set(normal_targets) & closure(graph, audit24), 'normal target changes audit24 closure'
    for m, expected in plan['expected_project_sources'].items():
        assert sources[m]['sha256'] == expected, ('audit24_source_context', m)
    save(ROOT / 'PROJECT_SOURCE_CONTEXT.json', sources)
    config = {'commit': commit, 'started_utc': start, 'driver_sha256': file_sha(executed),
              'audit_runner': str(runner), 'audit_receipt_root': plan['receipt_root'],
              'plan_sha256': digest(plan_bytes), 'first14': first14, 'graph': graph,
              'normal_source_sha256': expected_sources, 'excluded_already_accepted_targets': sorted(excluded),
              'direct_deps': {'0': sorted(graph[HIGHER]),
                              '1': sorted({d for m in PARENTS + first14 for d in graph[m]})}}
    save(ROOT / 'RUN_CONFIG.json', config)

    def launch(phase, lane):
        directory = ROOT / phase / ('lane-' + str(lane))
        directory.mkdir(parents=True, exist_ok=True)
        argv = serialize(lane, directory / 'VALIDATION_LANE.json',
                         ['python3', str(executed), '--commit', commit,
                          '--worker', phase, '--lane', str(lane)])
        return run_stage(directory, 'worker', argv, relay=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        preflight = list(pool.map(lambda lane: launch('preflight', lane), [0, 1]))
    assert all(r['exit_code'] == 0 for r in preflight), 'direct dependency preflight failed; no normal launched'
    preparation = run_stage(ROOT, 'audit24-prepare-only', [
        'python3', str(runner), '--plan', str(inputs / 'AUDIT_PLAN.json'), '--prepare-only'])
    assert preparation['exit_code'] == 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        lanes = list(pool.map(lambda lane: launch('execution', lane), [0, 1]))
    final = launch('final-readiness', 1)
    final_source_hashes = {m: file_sha(PROJECT / module_path(m)) for m in sources}
    assert final_source_hashes == {m: r['sha256'] for m, r in sources.items()}, 'source changed during execution'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT_REPO).strip() == original_head
    assert subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT_REPO) == original_status
    result = {'commit': commit, 'started_utc': start, 'finished_utc': now(),
              'preflight': preflight, 'lane_commands': lanes, 'final_readiness': final,
              'protected_roots': check_roots(), 'all_project_sources_unchanged_during_execution': True,
              'original_dirty_git_checkout_unchanged': True, 'seed90_or_prior55_scheduled': False,
              'higher_probe_reruns': False, 'row5_executed': False, 'whole_P1_complete': False,
              'normal_requires_separate_kernel_full_owned_acceptance': True}
    save(ROOT / 'BATCH5_RESULT.json', result)
    emit('RESULT', lane_exit_codes=[r['exit_code'] for r in lanes],
         final_readiness_worker_exit=final['exit_code'], receipt=str(ROOT / 'BATCH5_RESULT.json'))
    return 0 if all(r['exit_code'] == 0 for r in lanes + [final]) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--worker', choices=['preflight', 'execution', 'final-readiness'])
    parser.add_argument('--lane', type=int, choices=[0, 1])
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit), 'use the full published Git commit'
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
        record = {'status': 'STOPPED_WITH_EXCEPTION', 'phase': args.worker or 'coordinator',
                  'lane': args.lane, 'error_type': type(error).__name__,
                  'error': str(error), 'utc': now(), 'whole_P1_complete': False}
        failure = ROOT / ('FAILURE-' + (args.worker or 'coordinator') + '-' + str(args.lane) + '.json')
        if ROOT.exists() and not failure.exists():
            save(failure, record)
        emit('EXCEPTION', **record)
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
