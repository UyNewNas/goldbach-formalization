#!/usr/bin/env python3
"""Continue exactly Batch10's 75 owners; generate, never replace, the e9 audit.

--check reads only Git objects and project files. --install-and-run uses the
existing cloud lane/guard. --audit-plan-only reads durable normal receipts and
writes a pending plan, without invoking Lean/Lake or changing project sources.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import types

sys.dont_write_bytecode = True
SOURCE_COMMIT = '99c1f8ba1dc453b21f47e30b667db0de93d73387'
PROJECT = Path('/workspace/blue-member-build')
SOURCE_REPO = Path('/workspace/goldbach-formalization')
RECEIPTS = Path('/workspace/p1-complete-proof/20261125-batch10-resume')
PREFIX = 'docs/p1/20261124/'
HELPER_PATH = PREFIX + 'batch5-parallel/run_batch5_parallel.py'
HELPER_SHA = '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5'
RUNNER_PATH = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
GUARD_SHA = 'c202e53a319d9f30ee78db1582f53fe2104872f4ee749e1e5cac7d3ad5cfb526'
SERIALIZER_SHA = '734602546772451e12fcbe8d8c3380ee2db9211db30444cbb524c59c79a8f368'
INPUTS = {
    PREFIX + 'batch10-source-update/SOURCE_UPDATE.json':
        '1f165eed939b8ae1eb06b50a540dcacad6d0bae39510d340e69af6328a8c7441',
    PREFIX + 'batch10-higher-partition/COMPILE_PLAN.json':
        'c5944ed7660064d9a7ce3d70acd46210deee1ddcbf7ce98f75648ad6fe45d740',
    HELPER_PATH: HELPER_SHA, RUNNER_PATH: RUNNER_SHA,
}
AUDIT_TEMPLATE = Path('/workspace/p1-complete-proof/20261124-resume/accepted-batch102-two/PublicAudit.lean')
AUDIT_TEMPLATE_SHA = '535d5e697ff5c719dbbd90ff04e358be7071cdc9a0b145cf4d3edf2fff002248'
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+([\w.]+)(?::olean)?(?=\s|$)', re.M)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(path):
    with Path(path).open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size,
                'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_frozen(path, data):
    """Create an atomic, immutable file, or verify identical existing bytes."""
    path = Path(path)
    if path.exists():
        require(path.read_bytes() == data, 'existing receipt differs: ' + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp-' + str(os.getpid()))
    try:
        with temporary.open('xb') as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)  # Exclusive publication, never overwrite a racing file.
    finally:
        temporary.unlink(missing_ok=True)


def save(path, value):
    write_frozen(path, (json.dumps(value, indent=2, sort_keys=True) + '\n').encode())


def attempt(parent):
    parent.mkdir(parents=True, exist_ok=True)
    for number in range(100000):
        path = parent / ('attempt-%05d' % number)
        try:
            path.mkdir()
            return path
        except FileExistsError:
            continue
    raise RuntimeError('too many prior attempts')


def git_read(repo, path):
    return subprocess.check_output(['git', 'show', SOURCE_COMMIT + ':' + path], cwd=repo)


def load_helper(raw):
    require(sha(raw) == HELPER_SHA, 'pinned helper integrity')
    helper = types.ModuleType('unchanged_batch5_helper')
    exec(compile(raw, HELPER_PATH, 'exec'), helper.__dict__)
    return helper


def load_inputs(repo):
    raw = {p: git_read(repo, p) for p in INPUTS}
    for path, expected in INPUTS.items():
        require(sha(raw[path]) == expected, 'published input integrity: ' + path)
    helper = load_helper(raw[HELPER_PATH])
    ordinary = json.loads(raw[PREFIX + 'batch10-source-update/SOURCE_UPDATE.json'])['updates']
    higher = json.loads(raw[PREFIX + 'batch10-higher-partition/COMPILE_PLAN.json'])
    require(len(ordinary) == 22 and len(higher['files']) == 53, 'unexpected Batch10 scope')
    rows = [dict(row, cloud_source_mutation_required=True) for row in ordinary]
    facade = 'ImbalancedChen.P2OriginalSixthHigherMoments'
    for module in higher['compile_order']:
        rows.append({'module': module, 'path': helper.module_path(module),
                     'before_sha256': higher['original_source_sha256'] if module == facade else None,
                     'after_sha256': higher['files'][module]['sha256'],
                     'cloud_source_mutation_required': True})
    require(len({r['module'] for r in rows}) == 75, 'duplicate Batch10 owner')
    payloads = {}
    for row in rows:
        require(row['path'] == helper.module_path(row['module']), 'noncanonical source path')
        payloads[row['path']] = git_read(repo, row['path'])
        require(sha(payloads[row['path']]) == row['after_sha256'], 'published payload integrity: ' + row['path'])
    tree = subprocess.check_output(['git', 'ls-tree', '-r', '-z', SOURCE_COMMIT, '--', 'ImbalancedChen'], cwd=repo)
    blobs = {entry.split(b'\t', 1)[1].decode(): entry.split(b'\t', 1)[0].split()[2].decode()
             for entry in tree.split(b'\0') if entry}
    return {'updates': rows, 'payloads': payloads, 'helper': helper, 'raw_inputs': raw,
            'higher_order': higher['compile_order'], 'ordinary': [r['module'] for r in ordinary],
            'blob_ids': blobs}


def preflight_sources(project, rows, payloads):
    """Validate the entire batch without even creating a backup directory."""
    require(len({r['path'] for r in rows}) == len(rows), 'duplicate source path')
    result = []
    for row in rows:
        require(sha(payloads[row['path']]) == row['after_sha256'], 'payload integrity: ' + row['path'])
        path = project / row['path']
        current = sha(path.read_bytes()) if path.is_file() else None
        require(current in {row['before_sha256'], row['after_sha256']} and
                (current is not None or not os.path.lexists(path)), 'unknown source preimage: ' + row['path'])
        action = ('ALREADY_AFTER_NOOP' if current == row['after_sha256'] else
                  'CREATE_ABSENT' if current is None else 'REPLACE_PREIMAGE')
        result.append(dict(row, actual_sha256=current, action=action))
    return result


def install_sources(project, rows, payloads, backup_root, helper):
    before = preflight_sources(project, rows, payloads)
    old = [dict(r, cloud_source_mutation_required=True) for r in rows if r['before_sha256'] is not None]
    # The original helper keeps its full-batch checks, backups and exact no-ops.
    records = helper.install_sources(project, old, payloads, backup_root)
    for row in before:
        if row['before_sha256'] is None:
            write_frozen(project / row['path'], payloads[row['path']])
            records.append(row)
    require(all(r['action'] == 'ALREADY_AFTER_NOOP'
                for r in preflight_sources(project, rows, payloads)), 'installation postimage')
    return records


def project_context(project, spec):
    helper = spec['helper']
    for module, expected in helper.FOUR_ROOTS.items():
        require(sha((project / helper.module_path(module)).read_bytes()) == expected, 'protected P1 root changed: ' + module)
    graph, imports, sources = {}, {}, {}
    pending = [r['module'] for r in spec['updates']]
    while pending:
        module = pending.pop()
        if module in graph:
            continue
        path = helper.module_path(module)
        data = spec['payloads'].get(path)
        if data is None:
            data = (project / path).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(blob == spec['blob_ids'].get(path), 'dependency source differs from fixed snapshot: ' + path)
        imports[module] = helper.imports(data)
        graph[module] = [d for d in imports[module] if d.startswith('ImbalancedChen.')]
        sources[module] = sha(data)
        pending.extend(graph[module])
    return graph, imports, sources


def compile_order(higher, ordinary, graph):
    selected, seen, active, ordered = set(higher + ordinary), set(), set(), []
    def visit(module):
        require(module not in active, 'source import cycle: ' + module)
        if module in seen:
            return
        active.add(module)
        for dep in graph[module]:
            visit(dep)
        active.remove(module)
        seen.add(module)
        if module in selected:
            ordered.append(module)
    for module in higher + ordinary:
        visit(module)
    require(ordered[:len(higher)] == higher, 'Higher order conflicts with source dependencies')
    return ordered


def snapshot(project, module):
    rel = module.replace('.', '/')
    paths = [rel + '.lean', '.lake/build/lib/lean/' + rel + '.olean',
             '.lake/build/lib/lean/' + rel + '.ilean', '.lake/build/ir/' + rel + '.c',
             '.lake/build/ir/' + rel + '.setup.json', '.lake/build/lib/lean/' + rel + '.trace']
    return {p: fingerprint(project / p) for p in paths}


def runtime_binding(helper):
    paths = [Path(helper.GUARD), Path(helper.SERIALIZER), *helper.STATES, AUDIT_TEMPLATE]
    result = {str(p): fingerprint(p) for p in paths}
    require(result[str(helper.GUARD)]['sha256'] == GUARD_SHA, 'existing guard differs from observed cloud runtime')
    require(result[str(helper.SERIALIZER)]['sha256'] == SERIALIZER_SHA, 'existing serializer differs from observed cloud runtime')
    require(result[str(AUDIT_TEMPLATE)]['sha256'] == AUDIT_TEMPLATE_SHA, 'unchanged full-owned audit template required')
    return result


def dependency_binding(project, module, graph, sources, helper):
    closure = helper.closure(graph, [module])
    actual = {m: sha((project / helper.module_path(m)).read_bytes()) for m in sorted(closure)}
    require(actual == {m: sources[m] for m in sorted(closure)}, 'source context changed: ' + module)
    objects = {}
    for dep in sorted(closure - {module}):
        stem = '.lake/build/lib/lean/' + dep.replace('.', '/')
        for ext in ('.olean', '.trace'):
            objects[stem + ext] = fingerprint(project / (stem + ext))
    configuration = {p: fingerprint(project / p) for p in
                     ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean')
                     if (project / p).is_file()}
    return {'source_commit': SOURCE_COMMIT, 'project_sources': actual,
            'dependency_objects_and_traces': objects, 'configuration': configuration,
            'existing_runtime': runtime_binding(helper)}


def record_command(project, directory, name, argv, relay=False):
    log = directory / (name + '.log')
    record = {'argv': list(map(str, argv)), 'cwd': str(project), 'started_utc': now()}
    save(directory / (name + '-started.json'), record)
    tick = time.monotonic()
    with log.open('xb') as stream:
        if relay:
            child = subprocess.Popen(record['argv'], cwd=project, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            with child.stdout:
                for line in child.stdout:
                    stream.write(line)
                    stream.flush()
                    if line.startswith(b'{"stage":') and len(line) <= 8000:
                        print(line.decode(errors='replace').rstrip(), flush=True)
            code = child.wait()
        else:
            code = subprocess.run(record['argv'], cwd=project, stdout=stream, stderr=subprocess.STDOUT).returncode
    record.update(exit_code=code, elapsed_seconds=time.monotonic() - tick, finished_utc=now(),
                  log=str(log), log_sha256=fingerprint(log)['sha256'],
                  actual_built_modules=BUILT.findall(ANSI.sub('', log.read_text(errors='replace'))))
    path = directory / (name + '-command.json')
    save(path, record)
    return dict(record, command_receipt=str(path), command_sha256=fingerprint(path)['sha256'])


def validate_normal(project, module, receipt, context, helper):
    require(receipt['module'] == module and receipt['source_commit'] == SOURCE_COMMIT and
            receipt['status'] == 'NORMAL_PASS_AUDIT_PENDING', 'invalid normal receipt identity')
    require(receipt['dependency_context'] == context and
            receipt['source_plus_five_outputs'] == snapshot(project, module), 'stale normal receipt binding: ' + module)
    command = Path(receipt['normal_command']['command_receipt'])
    require(fingerprint(command)['sha256'] == receipt['normal_command']['command_sha256'], 'normal command receipt changed')
    rec = json.loads(command.read_bytes())
    require(all(receipt['normal_command'].get(k) == v for k, v in rec.items()), 'normal receipt command copy differs')
    require(rec['exit_code'] == 0 and rec['argv'] == helper.guard(0, ['lake', 'build', '+' + module + ':olean']) and
            rec['cwd'] == str(project), 'normal command receipt scope')
    log = Path(rec['log'])
    require(fingerprint(log)['sha256'] == rec['log_sha256'] and
            BUILT.findall(ANSI.sub('', log.read_text())) == [module] and
            rec['actual_built_modules'] == [module], 'normal log receipt scope')


def normal_one(project, module, direct_imports, root, helper, context_fn):
    folder = root / 'normal' / module
    durable = folder / 'NORMAL_PASS.json'
    prior = json.loads(durable.read_bytes()) if durable.exists() else None
    if prior:
        validate_normal(project, module, prior, context_fn(), helper)
    directory = attempt(folder)
    if direct_imports:
        deps = record_command(project, directory, 'dependencies-ready', helper.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in direct_imports]))
        require(deps['exit_code'] == 0, 'DEPENDENCIES_NOT_READY: ' + module)
    before = context_fn()
    ready = record_command(project, directory, 'target-ready', helper.guard(0,
                           ['lake', '--no-build', 'build', '+' + module + ':olean']))
    if ready['exit_code'] == 0:
        require(prior is not None, 'READY_WITHOUT_NORMAL_PROVENANCE: ' + module)
        validate_normal(project, module, prior, context_fn(), helper)
        return dict(prior, reused=True)
    require(prior is None, 'normal receipt exists but stock target readiness failed: ' + module)
    require(ready['exit_code'] == 3, 'unexpected no-build readiness exit: ' + module)
    print(json.dumps({'stage': 'NORMAL_START', 'module': module}), flush=True)
    normal = record_command(project, directory, 'normal', helper.guard(0, ['lake', 'build', '+' + module + ':olean']))
    require(normal['exit_code'] == 0 and normal['actual_built_modules'] == [module],
            'normal failed or unexpected build scope: ' + module + '; log=' + normal['log'] + '\n' +
            (helper.error_excerpt(Path(normal['log']))[:3000] if normal['exit_code'] else ''))
    require(context_fn() == before, 'dependency context changed during normal: ' + module)
    result = {'status': 'NORMAL_PASS_AUDIT_PENDING', 'source_commit': SOURCE_COMMIT, 'module': module,
              'source_plus_five_outputs': snapshot(project, module), 'dependency_context': before,
              'normal_command': normal, 'whole_P1_complete': False, 'kernel_or_full_owned_claim': False}
    save(durable, result)
    return dict(result, reused=False)


def pending_audit(project, root, spec, graph, sources, passed):
    """Only actual, validated normal receipts enter the unchanged e9 plan."""
    selected = sorted(passed)
    if not selected:
        return {'status': 'NO_VALID_NORMAL_RECEIPTS', 'whole_P1_complete': False}
    key = sha(json.dumps({m: passed[m]['normal_command']['command_sha256'] for m in selected}, sort_keys=True).encode())[:20]
    directory = root / 'pending-audit' / key
    helper = spec['helper']
    plan = {'schema': 'p1_completed_normal_multibatch_audit_plan_v1', 'status': 'PENDING_ACTUAL_KERNEL_AND_FULL_OWNED',
            'project': str(project), 'receipt_root': str(root / ('audit-' + key)),
            'runtime_states': list(map(str, helper.STATES)),
            'audit_template': {'path': str(AUDIT_TEMPLATE), 'sha256': AUDIT_TEMPLATE_SHA},
            'normal_logs': {}, 'modules': {}, 'expected_project_sources': {},
            'lanes': [{'id': 0, 'modules': selected}, {'id': 1, 'modules': []}],
            'excluded_prior13': [], 'reused_complete_modules': [], 'whole_P1_complete': False,
            'source_review_head': SOURCE_COMMIT, 'runner_binding': {'path': RUNNER_PATH, 'sha256': RUNNER_SHA},
            'higher_partition_normal_complete': set(spec['higher_order']) <= set(selected),
            'higher_missing_normal_modules': sorted(set(spec['higher_order']) - set(selected))}
    for module in selected:
        rec = passed[module]
        log = rec['normal_command']
        closure = sorted(helper.closure(graph, [module]))
        plan['normal_logs'][module] = {'path': log['log'], 'sha256': log['log_sha256'],
            'source_commit': SOURCE_COMMIT, 'expected_built_modules': [module]}
        plan['modules'][module] = {'source_sha256': sources[module], 'normal_log': module, 'project_closure': closure}
        plan['expected_project_sources'].update({m: sources[m] for m in closure})
    plan_path = directory / 'AUDIT_PLAN.json'
    runner = directory / 'run_parallel_acceptance_multibatch.py'
    save(plan_path, plan)
    write_frozen(runner, spec['raw_inputs'][RUNNER_PATH])
    receipt = Path(plan['receipt_root'])
    commands = {'status': 'PENDING_NOT_EXECUTED', 'cwd': str(project), 'plan_sha256': fingerprint(plan_path)['sha256'],
        'prepare_only_if_receipt_root_absent': ['python3', '-B', str(runner), '--plan', str(plan_path), '--prepare-only'],
        'run_only_populated_lane': helper.serialize(0, receipt / 'lane-0/VALIDATION_LANE.json',
            ['python3', '-B', str(runner), '--plan', str(receipt / 'AUDIT_PLAN.json'),
             '--receipt-root', str(receipt), '--lane', '0']),
        'higher_partition_normal_complete': plan['higher_partition_normal_complete'],
        'higher_missing_normal_modules': plan['higher_missing_normal_modules'],
        'selected_modules': selected, 'whole_P1_complete': False,
        'note': 'A partial selected-owner audit is not acceptance of all 53 Higher owners or P1.'}
    save(directory / 'PENDING_COMMANDS.json', commands)
    return {'status': 'AUDIT_PLAN_PENDING', 'plan': str(plan_path), 'commands': str(directory / 'PENDING_COMMANDS.json'),
            'normal_modules': len(selected), 'higher_partition_normal_complete': plan['higher_partition_normal_complete'],
            'whole_P1_complete': False}


def original_git_state(repo):
    return {'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo).decode().strip(),
            'status_hex': subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=repo).hex()}


def verify_lane(helper):
    state = json.loads(helper.STATES[0].read_bytes())
    lock = Path(state['slot'] + '.validation-lane.lock')
    inode = str(lock.stat().st_ino)
    require(any('FLOCK' in line and '->' not in line and (' ' + str(os.getppid()) + ' ') in line and inode in line
                for line in Path('/proc/locks').read_text().splitlines()), 'worker requires the existing parent serializer lane')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--install-and-run', action='store_true')
    mode.add_argument('--audit-plan-only', action='store_true')
    parser.add_argument('--source-repo', type=Path, default=SOURCE_REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--receipt-root', type=Path, default=RECEIPTS)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project, root = args.source_repo.resolve(), args.project.resolve(), args.receipt_root.resolve()
    git_before = original_git_state(repo)
    spec = load_inputs(repo)
    helper = spec['helper']
    preflight = preflight_sources(project, spec['updates'], spec['payloads'])
    graph, imports, sources = project_context(project, spec)
    order = compile_order(spec['higher_order'], spec['ordinary'], graph)
    if args.check:
        require(original_git_state(repo) == git_before, 'original Git worktree changed')
        print(json.dumps({'status': 'READ_ONLY_SOURCE_CHECK_PASSED_NOT_COMPILATION', 'source_commit': SOURCE_COMMIT,
            'target_modules': len(order), 'project_source_closure': len(sources), 'higher_modules': len(spec['higher_order']),
            'actions': {a: sum(r['action'] == a for r in preflight) for a in
                        ('ALREADY_AFTER_NOOP', 'REPLACE_PREIMAGE', 'CREATE_ABSENT')},
            'compile_order': order, 'no_source_or_receipt_writes': True, 'no_Lean_or_Lake_run': True,
            'whole_P1_complete': False}, indent=2))
        return 0
    require(project == PROJECT and repo != project, 'cloud execution requires the existing prepared project')
    runtime = runtime_binding(helper)
    binding = {'source_commit': SOURCE_COMMIT, 'inputs': INPUTS, 'project': str(project),
               'project_sources': sources, 'runtime': runtime, 'driver_sha256': fingerprint(Path(__file__))['sha256']}
    if args.audit_plan_only:
        require(all(r['action'] == 'ALREADY_AFTER_NOOP' for r in preflight), 'audit planning requires installed exact sources')
        passed = {}
        for module in order:
            path = root / 'normal' / module / 'NORMAL_PASS.json'
            if path.exists():
                rec = json.loads(path.read_bytes())
                validate_normal(project, module, rec, dependency_binding(project, module, graph, sources, helper), helper)
                passed[module] = rec
        result = pending_audit(project, root, spec, graph, sources, passed)
        require(original_git_state(repo) == git_before, 'original Git worktree changed')
        print(json.dumps(result))
        return 0
    save(root / 'RUN_BINDING.json', binding)
    if not args.inside_lane:
        executed = root / 'executed-driver.py'
        write_frozen(executed, Path(__file__).read_bytes())
        directory = attempt(root / 'runs')
        save(directory / 'ORIGINAL_GIT_BEFORE.json', git_before)
        argv = helper.serialize(0, directory / 'VALIDATION_LANE.json',
            ['python3', '-B', str(executed), '--install-and-run', '--inside-lane',
             '--source-repo', str(repo), '--project', str(project), '--receipt-root', str(root)])
        result = record_command(project, directory, 'serialized-worker', argv, relay=True)
        require(original_git_state(repo) == git_before, 'original Git worktree changed')
        print(json.dumps({'status': 'BATCH10_NORMAL_WORKER_FINISHED', 'exit_code': result['exit_code'],
                          'receipt': str(directory), 'whole_P1_complete': False}))
        return result['exit_code']
    verify_lane(helper)
    directory = attempt(root / 'source-installations')
    installed = install_sources(project, spec['updates'], spec['payloads'], directory / 'backups', helper)
    save(directory / 'SOURCE_INSTALL.json', installed)
    passed, failed = {}, {}
    for module in order:
        try:
            passed[module] = normal_one(project, module, imports[module], root, helper,
                lambda m=module: dependency_binding(project, m, graph, sources, helper))
            print(json.dumps({'stage': 'NORMAL_REUSED' if passed[module]['reused'] else 'NORMAL_PASS_AUDIT_PENDING',
                              'module': module}), flush=True)
        except Exception as error:
            failed[module] = {'error_type': type(error).__name__, 'error': str(error)}
            print(json.dumps({'stage': 'NORMAL_BLOCKED_OR_FAILED', 'module': module, **failed[module]}), flush=True)
    require(runtime_binding(helper) == runtime, 'runtime changed during continuation')
    require(original_git_state(repo) == git_before, 'original Git worktree changed')
    require(all(r['action'] == 'ALREADY_AFTER_NOOP'
                for r in preflight_sources(project, spec['updates'], spec['payloads'])), 'sources changed during continuation')
    require(project_context(project, spec) == (graph, imports, sources), 'protected roots or dependency sources changed')
    # Revalidate successes after the full run before making a pending audit plan.
    for module, rec in passed.items():
        validate_normal(project, module, rec, dependency_binding(project, module, graph, sources, helper), helper)
    audit = pending_audit(project, root, spec, graph, sources, passed)
    result = {'status': 'NORMAL_COMPLETE_AUDIT_PENDING' if not failed else 'PARTIAL_NORMAL_PROGRESS',
              'normal_passes': sorted(passed), 'blocked_or_failed': failed, 'pending_audit': audit,
              'original_dirty_git_worktree_unchanged': True, 'whole_P1_complete': False}
    save(directory / 'RESULT.json', result)
    print(json.dumps(result), flush=True)
    return 0 if not failed else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'STOPPED_WITHOUT_COMPLETION_CLAIM', 'error_type': type(error).__name__,
                          'error': str(error), 'whole_P1_complete': False}), flush=True)
        raise SystemExit(1)
