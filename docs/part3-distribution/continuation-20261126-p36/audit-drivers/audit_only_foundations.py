#!/usr/bin/env python3
"""Finish only the timed-out audit of one fixed six-foundation P3.6 run.

No target compilation, kernel replay, git checkout, or old-report mutation.
The original audit is retained; the new audit adds flushed progress messages only.
The caller must restore the parent's namespace visibility before execution.
Nonempty external-cache mirrors are outside this fixed continuation's scope.
Unfilled parent bindings fail before any output directory is created.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import threading
import time

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/p36-classical-20261125')
PIN = '3e87c2a76db9bbeba9ed26b7d6ebda5e8d69d463'
PARENT_TASK = 'a24f071e264d4fcf9f7c3f33d1dfc6b1'
RUN = PROJECT / '.lake/p36-six-core-build/runs/20261125T175104.739977Z'
PARENT_REPORT_SHA = '5d12208209316afdc9049d945fa914b531edc43d84280a714320d5b472589662'
ORIGINAL_AUDIT_SHA = '1c893eefa4a6ae36939f2510a3fafe59f56f44b8d2053bf84481b660b686c386'
PROGRESS_AUDIT_SHA = 'b93cd8bd6bcca0c5b686b716e8dc71cddb2bd7be9f29d132bfee1462cae8f722'
RUNNER_SHA = 'be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709'
FAILURE_ARCHIVE = Path('/workspace/p36-private-delivery-20261126/audit-timeout-3e87-foundations/evidence.tar.xz')
FAILURE_ARCHIVE_SHA = 'e42874fbaa1bd86be5c79d9865a6abb16aabe707b2c77980afe480d68b2eff02'
INTERRUPTED_AUDIT_SHA = 'd6147796edafa6241f1c712ab7919afed296a54dde1c1acc7078c10cd117293c'
PARENT_AUDIT_TIMEOUT = 300
PARENT_AUDIT_ELAPSED = 300.309
TARGETS = ('ImbalancedChen.P2RoundedFibreCore',
           'ImbalancedChen.P3OriginalU5WarmMixedReusedCore',
           'ImbalancedChen.P1ActualMovingAffineWallMass',
           'ImbalancedChen.P1ActualMovingCoordinateSlab',
           'ImbalancedChen.P1ActualMovingAffineSlab',
           'ImbalancedChen.P3OriginalU5FixedWidthSlabReserve')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def now():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def emit(name, value):
    print(name + ' ' + json.dumps(value, ensure_ascii=False), flush=True)


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def validate_parent_terminal(original):
    """Accept only this group's final audit timeout after all strict/replay stages."""
    require(original['status'] == 'FAILED' and original['strict_owned'] is True
            and original['targets'] == list(TARGETS) and not original['blockers'],
            'Parent status/scope differs')
    require(not original.get('planned_external_cache_mirrors', [])
            and not original.get('external_cache_mirrors', {}), 'Parent has unsupported cache mirrors')
    stages = original['commands']
    require(bool(stages), 'Missing parent stages')
    last = stages[-1]
    compiler = Path(original['compiler']['path'])
    audit_log = RUN / 'owned-inventory-audit.log'
    require(last['name'] == 'owned-inventory-audit' and last['exit_code'] == 124
            and last.get('elapsed_seconds') == PARENT_AUDIT_ELAPSED
            and PARENT_AUDIT_ELAPSED >= PARENT_AUDIT_TIMEOUT
            and last.get('log') == str(audit_log)
            and last['command'] == [str(compiler), '-t0', '-j1', '-DwarningAsError=true',
                                    '-R', str(RUN), str(RUN / 'P36OwnedAudit.lean')],
            'Parent does not end in the fixed 300-second audit timeout')
    require(all(stage['exit_code'] == 0 and stage['name'] != 'owned-inventory-audit'
                for stage in stages[:-1]), 'Another parent stage failed or audited')
    error = original.get('error', '')
    require(error.startswith(f'owned-inventory-audit failed with exit 124; see {audit_log}\n')
            and "Runner: this runner's child exceeded its configured timeout." in error.splitlines(),
            'Parent failure is not the recorded audit timeout')
    for name in TARGETS:
        record = original['modules'][name]
        require(record.get('action') == 'compiled' and record.get('strict') is True
                and record.get('exit_code') == 0, 'No original strict compilation: ' + name)
        for kind in ('compile-', 'replay-'):
            matched = [stage for stage in stages if stage['name'] == kind + name]
            require(len(matched) == 1 and matched[0]['exit_code'] == 0,
                    'Incomplete parent stage: ' + kind + name)
            if kind == 'compile-':
                relative = name.replace('.', '/')
                expected = [str(compiler), '-t0', '-j1', '-R', str(PROJECT),
                            '-DwarningAsError=true', '-o',
                            str(PROJECT / '.lake/p36-six-core-build/lib/lean' / (relative + '.olean')),
                            str(PROJECT / (relative + '.lean'))]
                require(matched[0]['command'] == record['command'] == expected,
                        'Strict command mismatch')
            else:
                require(matched[0]['command'] ==
                        [str(compiler.parent / 'leanchecker'), '--verbose', name],
                        'Checker command mismatch')


def require_fixed_bindings():
    """These values must come from the quiescent parent, never from defaults."""
    require(bool(PARENT_TASK) and len(PARENT_TASK) >= 16, 'Unfilled parent task identity')
    for name, value in (('PARENT_REPORT_SHA', PARENT_REPORT_SHA),
                        ('ORIGINAL_AUDIT_SHA', ORIGINAL_AUDIT_SHA),
                        ('PROGRESS_AUDIT_SHA', PROGRESS_AUDIT_SHA),
                        ('FAILURE_ARCHIVE_SHA', FAILURE_ARCHIVE_SHA),
                        ('INTERRUPTED_AUDIT_SHA', INTERRUPTED_AUDIT_SHA)):
        require(isinstance(value, str) and re.fullmatch(r'[0-9a-f]{64}', value) is not None,
                'Unfilled fixed binding: ' + name)
    require(isinstance(FAILURE_ARCHIVE, Path) and FAILURE_ARCHIVE.is_absolute(),
            'Unfilled absolute parent-timeout archive path')


def git(*args, cwd=PROJECT):
    return subprocess.check_output(['git', '--no-optional-locks', *args], cwd=cwd)


def object_paths(path):
    return {str(p) for suffix in ('', '.private', '.server')
            if (p := Path(str(path) + suffix)).is_file()}


def verify_snapshot_and_resolution(snapshots, modules, roots, build):
    for path, expected in snapshots.items():
        require(sha(path) == expected, 'Snapshot changed: ' + path)
    for name, node in modules.items():
        relative = name.replace('.', '/') + '.olean'
        expected = build / 'lib/lean' / relative if node['kind'] == 'build' else Path(node['cached_object'])
        namespace = name.split('.')[0]
        # Exact Lean 4.33 SearchPath.findWithExt semantics: a top-level
        # namespace directory/file locks the root even if this module is absent.
        root = next((r for r in roots if (r / namespace).is_dir() or (r / (namespace + '.olean')).exists()), None)
        chosen = root / relative if root is not None else None
        require(chosen is not None and chosen.is_file() and chosen.resolve() == expected.resolve(),
                'Import resolution changed: ' + name)
        require(object_paths(expected) == set(node['objects']), 'Object/sidecar set changed: ' + name)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--progress-audit', type=Path, required=True)
    ap.add_argument('--execute', action='store_true')
    ap.add_argument('--audit-timeout', type=int, default=2400)
    args = ap.parse_args()
    require(1 <= args.audit_timeout <= 3000, 'Audit timeout outside bounded range')
    require_fixed_bindings()
    out = PROJECT / '.lake/p36-audit-continuations' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    out.mkdir(parents=True, exist_ok=False)
    receipt = {'status': 'PREPARING_AUDIT_ONLY', 'p36_closed': False, 'started_utc': now(),
               'parent_task': PARENT_TASK, 'parent_run': str(RUN), 'parent_report_sha256': PARENT_REPORT_SHA,
               'mathematical_commit': PIN, 'targets': list(TARGETS),
               'fresh_target_compilation_this_task': False, 'kernel_replay_this_task': False,
               'compile_and_replay_origin': 'Referenced successful stages from the exact parent run',
               'scope': 'Six specified owned foundation modules only; not whole P3.6 closure'}
    write_json(out / 'report.json', receipt)
    snapshots = {}
    archive_files = {}

    def expect(path, expected):
        path = str(path)
        require(path not in snapshots or snapshots[path] == expected, 'Conflicting expected snapshot: ' + path)
        snapshots[path] = expected

    def bind(path, expected=None, archive_name=None):
        path = Path(path)
        actual = sha(path)
        if expected is not None:
            require(actual == expected, 'Input changed: ' + str(path))
        if str(path) in snapshots:
            require(snapshots[str(path)] == actual, 'Input raced: ' + str(path))
        snapshots[str(path)] = actual
        if archive_name is not None:
            require(archive_name not in archive_files or archive_files[archive_name] == path,
                    'Conflicting archive member: ' + archive_name)
            archive_files[archive_name] = path
        return actual

    try:
        require(git('rev-parse', 'HEAD').decode().strip() == PIN, 'Project HEAD differs from parent')
        bind(RUN / 'report.json', PARENT_REPORT_SHA, 'parent/run/report.json')
        original = json.loads((RUN / 'report.json').read_text())
        validate_parent_terminal(original)
        require(original['runner_sha256'] == RUNNER_SHA, 'Different parent runner')
        build = Path(original['build_dir'])
        roots = [Path(p) for p in original['lean_path']]
        compiler = Path(original['compiler']['path'])
        toolchain = compiler.parent.parent
        require(build == PROJECT / '.lake/p36-six-core-build' and roots[0] == build / 'lib/lean', 'Unexpected own build root')
        bind(compiler, original['compiler']['sha256'])
        checker_sha = bind(toolchain / 'bin/leanchecker')
        bind(FAILURE_ARCHIVE, FAILURE_ARCHIVE_SHA)
        for name in ('TERMINAL.json', 'STAGE.json', 'RECEIPT.json'):
            bind(FAILURE_ARCHIVE.parent / name, archive_name='parent/timeout/' + name)
        timeout_stage = json.loads((FAILURE_ARCHIVE.parent / 'STAGE.json').read_text())
        require(timeout_stage['report_sha256'] == PARENT_REPORT_SHA and timeout_stage['head'] == PIN,
                'Timeout-stage evidence differs')
        receipt['parent_timeout_archive'] = {'sha256': FAILURE_ARCHIVE_SHA, 'bytes': FAILURE_ARCHIVE.stat().st_size,
                                            'included_as_nested_archive': False,
                                            'note': 'Original report, logs, sources and timeout metadata are included directly, avoiding duplicate compressed data.'}
        bind(RUN / 'P36OwnedAudit.lean', ORIGINAL_AUDIT_SHA, 'parent/run/P36OwnedAudit.lean')
        bind(RUN / 'owned-inventory-audit.log', INTERRUPTED_AUDIT_SHA,
             'parent/run/interrupted-owned-inventory-audit.log')
        bind(args.progress_audit, PROGRESS_AUDIT_SHA)
        audit_text = args.progress_audit.read_text()
        stripped = re.sub(r'(?m)^ *-- P36_PROGRESS_BEGIN\n.*?^ *-- P36_PROGRESS_END\n', '', audit_text, flags=re.S)
        require(stripped.encode() == (RUN / 'P36OwnedAudit.lean').read_bytes(), 'Audit contains a semantic edit')
        audit = out / 'P36OwnedAuditProgress.lean'
        audit.write_bytes(args.progress_audit.read_bytes())
        bind(audit, PROGRESS_AUDIT_SHA, 'continuation/P36OwnedAuditProgress.lean')
        bind(Path(__file__), archive_name='continuation/audit_only_p36_main.py')
        for rel in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                    'verification/p36/compile_p36_local.py', 'verification/p36/project_cache_reuse.py',
                    'verification/p36/test_compile_p36_local.py', 'verification/verify_part3_continuation.py',
                    'verification/verify_part3_distribution.py', 'verification/Part3DistributionAudit.lean',
                    'verification/verify_variable_envelope_boxes.py'):
            committed = hashlib.sha256(git('show', PIN + ':' + rel)).hexdigest()
            bind(PROJECT / rel, committed, 'parent/config/' + rel)
        manifest = original['source_manifest']
        bind(Path(manifest['path']), manifest['sha256'], 'parent/SOURCE_SELECTION.json')
        for entry in json.loads(Path(manifest['path']).read_text())['sources']:
            relative = entry['module'].replace('.', '/') + '.lean'
            require(relative == entry['selected_path'], 'Bad manifest path')
            bind(PROJECT / relative, entry['selected_sha256'])
        for stage in original['commands']:
            log = Path(stage['log'])
            require(log.parent == RUN, 'Parent command log outside its run')
            bind(log, stage['log_sha256'], 'parent/run/' + log.name)
            require(log.read_text().splitlines()[0] == 'command=' + json.dumps(stage['command']),
                    'Parent log command header differs: ' + stage['name'])
        for name in TARGETS:
            record = original['modules'][name]
            require(record.get('action') == 'compiled' and record.get('strict') is True
                    and record.get('exit_code') == 0, 'No original strict compilation: ' + name)
            for kind in ('compile-', 'replay-'):
                stages = [x for x in original['commands'] if x['name'] == kind + name]
                require(len(stages) == 1 and stages[0]['exit_code'] == 0, 'Incomplete parent stage: ' + kind + name)
                if kind == 'compile-':
                    require(stages[0]['command'] == record['command']
                            and '-DwarningAsError=true' in stages[0]['command'], 'Strict command mismatch')
                else:
                    require(stages[0]['command'] == [str(toolchain / 'bin/leanchecker'), '--verbose', name], 'Checker command mismatch')
                    require('replaying ' + name in Path(stages[0]['log']).read_text().splitlines(), 'Missing exact replay evidence')
            relative = name.replace('.', '/')
            bind(PROJECT / (relative + '.lean'), record['source_sha256'], 'parent/source/' + relative + '.lean')
            for path, expected in record['objects'].items():
                p = Path(path)
                bind(p, expected, 'parent/objects/' + relative + p.name[len(Path(relative).name):])

        state_path = build / 'state.json'
        bind(state_path, archive_name='parent/lineage/local-state.json')
        state = json.loads(state_path.read_text())['modules']
        for name in original['topological_order']:
            node = original['modules'][name]
            if node.get('source'):
                bind(node['source'], node['source_sha256'])
            obj = (build / 'lib/lean' / (name.replace('.', '/') + '.olean')
                   if node['kind'] == 'build' else Path(node['cached_object']))
            require(object_paths(obj) == set(node['objects']), 'Object/sidecar set differs: ' + name)
            for path, expected in node['objects'].items():
                expect(path, expected)
            if node.get('action') == 'reused':
                prev = state[name]
                require(prev['input_key'] == node['input_key'] and prev['objects'] == node['objects']
                        and prev['source_sha256'] == node['source_sha256'], 'Local reuse state differs: ' + name)
                log = Path(node['previous_log'])
                require(log.is_relative_to(build) and str(log) == prev['log'], 'Local lineage path differs')
                bind(log, prev['log_sha256'], 'parent/lineage/' + log.parent.name + '/' + log.name)
        for alias in original.get('native_research_aliases', []):
            bind(alias['source'], alias['sha256'])
            native = Path(alias['source']).parents[len(alias['module'].split('.')) - 1]
            for match in alias['tracked_matches']:
                bind(native / match['path'], alias['sha256'])
        for i, transferred in enumerate(original.get('transferred_verified_objects', [])):
            bind(transferred['receipt'], transferred['receipt_sha256'], f'parent/transferred-{i}/RECEIPT.json')
            for path, expected in transferred['evidence_sha256'].items():
                bind(path, expected)
            accepted = json.loads(Path(transferred['receipt']).read_text())
            bind(Path(transferred['receipt']).parent / 'evidence.tar.xz', accepted['archive_sha256'],
                 f'parent/transferred-{i}/evidence.tar.xz')

        def check_current():
            require(git('rev-parse', 'HEAD').decode().strip() == PIN, 'HEAD changed')
            verify_snapshot_and_resolution(snapshots, original['modules'], roots, build)
            packages = PROJECT / '.lake/p36-packages'
            for package, rev in original['dependency_pins'].items():
                require(git('rev-parse', 'HEAD', cwd=packages / package).decode().strip() == rev, 'Package pin changed: ' + package)
                require(not git('status', '--porcelain', '--untracked-files=no', cwd=packages / package).strip(), 'Dirty package: ' + package)

        check_current()
        binding = {'parent_report_sha256': PARENT_REPORT_SHA, 'source_commit': PIN,
                   'snapshot_sha256': snapshots, 'lean_path': original['lean_path'],
                   'original_audit_sha256': ORIGINAL_AUDIT_SHA, 'progress_audit_sha256': PROGRESS_AUDIT_SHA,
                   'current_checker_sha256': checker_sha,
                   'checker_note': 'Current official checker snapshot; original replay commands/logs are separately preserved, not rerun.',
                   'checked_before_utc': now()}
        write_json(out / 'binding.json', binding)
        receipt.update(status='AUDIT_ONLY_READY', snapshot_count=len(snapshots), compiler=original['compiler'],
                       dependency_pins=original['dependency_pins'], lean_path=original['lean_path'])
        write_json(out / 'report.json', receipt)
        emit('P36_AUDIT_ONLY_READY', {'path': str(out), 'snapshots': len(snapshots), 'parent_report_sha256': PARENT_REPORT_SHA})
        if not args.execute:
            return 0
        sys.path.insert(0, str(PROJECT / 'verification'))
        import verify_part3_distribution as validator
        log = out / 'owned-inventory-audit.log'
        command = [str(compiler), '-t0', '-j1', '-DwarningAsError=true', '-R', str(out), str(audit)]
        env = os.environ.copy()
        (out / 'tmp').mkdir()
        env.update(LEAN_PATH=os.pathsep.join(map(str, roots)), LEAN_SYSROOT=str(toolchain),
                   LEAN_NUM_THREADS='1', PATH=str(compiler.parent) + os.pathsep + env.get('PATH', ''), TMPDIR=str(out / 'tmp'))
        stop = threading.Event()

        def monitor():
            position = 0
            partial = b''
            tick = time.monotonic()
            while not stop.wait(1):
                if log.exists():
                    with log.open('rb') as f:
                        f.seek(position)
                        data = f.read()
                    position += len(data)
                    parts = (partial + data).split(b'\n')
                    partial = parts.pop()
                    for line in parts:
                        if line.startswith(b'P36_AUDIT_STAGE '):
                            print(line.decode('utf-8', errors='replace'), flush=True)
                    if time.monotonic() - tick >= 45:
                        emit('P36_AUDIT_HEARTBEAT', {'utc': now(), 'log_bytes': position})
                        tick = time.monotonic()

        started = time.monotonic()
        thread = threading.Thread(target=monitor, daemon=True)
        with log.open('w') as f:
            f.write('command=' + json.dumps(command) + '\n'); f.flush()
            thread.start()
            try:
                code = subprocess.run(command, cwd=PROJECT, env=env, stdout=f, stderr=subprocess.STDOUT,
                                      timeout=args.audit_timeout).returncode
            except subprocess.TimeoutExpired:
                f.write('\nAudit-only child exceeded its configured timeout.\n'); code = 124
            finally:
                stop.set(); thread.join(timeout=5)
        body = log.read_text().split('\n', 1)[1]
        receipt['audit_command'] = {'command': command, 'exit_code': code, 'elapsed_seconds': round(time.monotonic() - started, 3),
                                    'log': str(log), 'log_sha256': sha(log)}
        write_json(out / 'report.json', receipt)
        require(code == 0, 'Audit did not complete successfully: ' + str(code) + '\n' + body[-12000:])
        declarations, counts = validator.validate_inventory(body, modules=TARGETS)
        check_current()
        write_json(out / 'declarations.json', declarations)
        receipt.update(status='VERIFIED_OWNED_AUDIT_CONTINUATION', finished_utc=now(),
                       complete_owned_declaration_count=len(declarations), module_counts=counts,
                       module_declaration_kinds={m: dict(Counter(x['kind'] for x in declarations if x['module'] == m)) for m in TARGETS},
                       strict_compilation=True, bundled_kernel_replay=True, complete_transitive_axiom_audit=True,
                       allowed_transitive_axioms=sorted(ALLOWED), source_sha256={m: original['modules'][m]['source_sha256'] for m in TARGETS},
                       objects_sha256={m: original['modules'][m]['objects'] for m in TARGETS},
                       checked_after_utc=now())
        write_json(out / 'report.json', receipt)
        for p in sorted(out.iterdir()):
            if p.is_file():
                archive_files['continuation/' + p.name] = p
        archive = out / 'evidence.tar.xz'
        hashes = {name: sha(path) for name, path in archive_files.items()}
        with tarfile.open(archive, 'w:xz', preset=6) as tar:
            for name, path in sorted(archive_files.items()):
                tar.add(path, arcname=name, recursive=False)
        require(all(sha(path) == hashes[name] for name, path in archive_files.items()), 'Archive inputs raced')
        final = {**receipt, 'archive': str(archive), 'archive_bytes': archive.stat().st_size,
                 'archive_sha256': sha(archive), 'files': hashes}
        write_json(out / 'RECEIPT.json', final)
        emit('P36_AUDIT_ONLY_EVIDENCE', final)
        return 0
    except Exception as error:
        receipt.update(status='AUDIT_ONLY_FAILED_NOT_ACCEPTED', finished_utc=now(), error=str(error))
        write_json(out / 'report.json', receipt)
        emit('P36_AUDIT_ONLY_FAILED', {'path': str(out), **receipt})
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
