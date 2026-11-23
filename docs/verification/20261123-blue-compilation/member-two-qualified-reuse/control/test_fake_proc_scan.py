"""Exercise only the AST-extracted scan against temporary fake /proc trees.

This never imports a gate/caller module, reads real /proc, acquires a lock,
starts a child process, or calls historical qualification/installation code.
"""
from pathlib import Path
import argparse
import ast
import datetime
import errno
import hashlib
import json
import os
import shutil
import tempfile
from unittest.mock import patch


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    output = Path(args.output)
    assert not output.exists(), 'Do not overwrite a previous fixture result'
    source = Path(__file__).with_name('controlled_window_gate_candidate.py')
    raw = source.read_bytes()
    tree = ast.parse(raw)
    selected = next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef) and node.name == 'current_related_jobs')
    # Only this one pure-read function is compiled. None of the source's
    # imports, assignments, decorators, __main__, gate or caller is executed.
    isolated = ast.Module(body=[selected], type_ignores=[])
    namespace = {'Path': Path, 'os': os, 'errno': errno,
                 'MEMBER': Path('/workspace/blue-member-build'),
                 'PRODUCER': Path('/workspace/blue-reindex-build')}
    exec(compile(isolated, '<AST-extracted-current_related_jobs-only>', 'exec'), namespace)
    scan = namespace['current_related_jobs']
    results = []
    original_read_text = Path.read_text
    original_resolve = Path.resolve
    original_iterdir = Path.iterdir

    with tempfile.TemporaryDirectory(prefix='controlled-gate-fake-proc-') as temp:
        fixture_root = Path(temp)

        def run_case(name, argv=None, comm='python3', state='S', fault=None,
                     fault_field='stat', disappear=False, expected_jobs=1,
                     expected_error=None, cwd_override=None, pid=999999):
            case = fixture_root / name
            proc = case / 'proc'
            proc.mkdir(parents=True)
            work = case / 'unrelated-working-directory'
            work.mkdir()
            entry = proc / str(pid)
            entry.mkdir()
            fields = [state, '1'] + ['0'] * 17 + ['123456']
            (entry / 'stat').write_text(f'{pid} (fixture process) ' + ' '.join(fields))
            (entry / 'comm').write_text(comm + '\n')
            if argv is None:
                argv = ['python3', '/tmp/unrelated-readable.py']
            (entry / 'cmdline').write_text('\0'.join(argv) + ('\0' if argv else ''))
            (entry / 'cwd').symlink_to(work, target_is_directory=True)

            def read_fake_only(path, *a, **kw):
                path = Path(path)
                assert path.is_relative_to(fixture_root), ('real_or_nonfixture_read_forbidden', str(path))
                if fault and path == entry / fault_field:
                    if disappear:
                        shutil.rmtree(entry)
                    if fault == 'permission':
                        raise PermissionError(errno.EACCES, 'fixture access denied', str(path))
                    if fault == 'unicode':
                        raise UnicodeDecodeError('utf-8', b'\xff', 0, 1, 'fixture invalid utf8')
                    if fault == 'enoent':
                        raise FileNotFoundError(errno.ENOENT, 'fixture absent', str(path))
                    if fault == 'esrch':
                        raise ProcessLookupError(errno.ESRCH, 'fixture vanished', str(path))
                    if fault == 'eio':
                        raise OSError(errno.EIO, 'fixture I/O failure', str(path))
                    if fault == 'malformed':
                        return 'not a process stat'
                    raise AssertionError(('unknown_fixture_fault', fault))
                return original_read_text(path, *a, **kw)

            def resolve_fake_only(path, *a, **kw):
                path = Path(path)
                assert path.is_relative_to(fixture_root), ('real_or_nonfixture_resolve_forbidden', str(path))
                if path == entry / 'cwd' and cwd_override == 'permission':
                    raise PermissionError(errno.EACCES, 'fixture unreadable cwd', str(path))
                if path == entry / 'cwd' and cwd_override:
                    return Path(cwd_override)  # Identity only; never resolves that real path.
                return original_resolve(path, *a, **kw)

            def iterdir_fake_only(path):
                path = Path(path)
                assert path == proc, ('real_or_unexpected_proc_enumeration_forbidden', str(path))
                return original_iterdir(path)

            observed_error, jobs = None, None
            with patch.object(Path, 'read_text', read_fake_only), \
                    patch.object(Path, 'resolve', resolve_fake_only), \
                    patch.object(Path, 'iterdir', iterdir_fake_only):
                try:
                    jobs = scan(proc_root=proc)
                except Exception as error:
                    observed_error = type(error).__name__
            if expected_error:
                assert observed_error == expected_error, (name, observed_error, jobs)
            else:
                assert observed_error is None, (name, observed_error)
                assert len(jobs) == expected_jobs, (name, jobs)
            results.append({'name': name, 'status': 'PASS', 'expected_jobs': expected_jobs,
                            'observed_jobs': jobs, 'observed_error': observed_error})

        # GATE-R2-01: visible unreadable stat/comm must remain blockers.
        run_case('stat_permission_visible', fault='permission')
        run_case('comm_permission_visible', fault='permission', fault_field='comm')
        run_case('stat_unicode_visible', fault='unicode')
        run_case('comm_unicode_visible', fault='unicode', fault_field='comm')
        run_case('stat_eio_visible', fault='eio')
        run_case('stat_malformed_visible', fault='malformed')
        run_case('stat_enoent_pid_still_visible', fault='enoent')
        run_case('comm_esrch_pid_still_visible', fault='esrch', fault_field='comm')
        # Only a confirming absent PID makes an ENOENT/ESRCH read race ignorable.
        run_case('stat_genuine_enoent_disappearance', fault='enoent', disappear=True, expected_jobs=0)
        run_case('comm_genuine_esrch_disappearance', fault='esrch', fault_field='comm',
                 disappear=True, expected_jobs=0)
        run_case('cmdline_genuine_enoent_disappearance', fault='enoent', fault_field='cmdline',
                 disappear=True, expected_jobs=0)
        # GATE-R2-02: opaque/empty Python argv is not proof of idleness.
        run_case('python_cmdline_permission_visible', fault='permission', fault_field='cmdline')
        run_case('python_cmdline_unicode_visible', fault='unicode', fault_field='cmdline')
        run_case('python_cmdline_enoent_pid_still_visible', fault='enoent', fault_field='cmdline')
        run_case('python_cmdline_empty_visible', argv=[])
        run_case('lean_cmdline_empty_visible', argv=[], comm='lean-runtime')
        # GATE-R2-03: the actual queued launcher, before it starts a child.
        guarded = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state',
                   '/workspace/blue-build-tools/member-runtime-evidence/state.json',
                   'lake', 'build', 'ImbalancedChen.PendingModule:olean']
        run_case('queued_run_guarded_member_cwd', argv=guarded,
                 cwd_override='/workspace/blue-member-build')
        run_case('queued_run_guarded_unreadable_cwd', argv=guarded, cwd_override='permission')
        run_case('known_lane_serializer', argv=['python3', '/workspace/blue-build-tools/serialize_validation_lane.py'])
        run_case('known_batch_controller', argv=['python3', '/workspace/blue-member-repair-batch99/run_validation.py'])
        run_case('known_legacy_resume', argv=['python3', '/workspace/p1-complete-proof/validation-lane-correction/resume_legacy_p6_lane.py'])
        run_case('direct_lean_runtime_member_source', comm='lean-runtime',
                 argv=['/tmp/lean-runtime', '/workspace/blue-member-build/ImbalancedChen/Test.lean'])
        run_case('shadow_python_source_wrapper', argv=['python3',
                 '/workspace/blue-build-tools/member-runtime/p0-ci-shadow-toolchain/bin/lean',
                 '/workspace/blue-member-build/ImbalancedChen/Test.lean'])
        run_case('checker_related_argv', comm='leanchecker',
                 argv=['/tmp/leanchecker', '/workspace/blue-member-build/ImbalancedChen/Test.olean'])
        run_case('compiler_unreadable_cwd_retained', comm='lake', argv=['/tmp/lake', '--githash'],
                 cwd_override='permission')
        # Controls: fully readable unrelated processes may be omitted.
        run_case('visible_readable_unrelated_python', expected_jobs=0)
        run_case('visible_readable_unrelated_compiler', comm='clang',
                 argv=['/usr/bin/clang', '/tmp/unrelated.c'], expected_jobs=0)
        run_case('zombie_has_no_future_source_work', state='Z', argv=guarded, expected_jobs=0)
        run_case('scanner_own_pid_excluded', pid=os.getpid(), argv=guarded, expected_jobs=0)

    result = {'schema': 'controlled_gate_v3_isolated_pure_scan_fake_proc_fixtures_v1',
              'status': 'PASS_FAKE_PROC_REGRESSIONS_ONLY_NOT_A_PRODUCTION_WINDOW',
              'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'candidate_gate_sha256': sha(raw),
              'test_script_sha256': sha(Path(__file__).read_bytes()),
              'extracted_function_sha256': sha(ast.get_source_segment(raw.decode(), selected).encode()),
              'passed': len(results), 'failed': 0, 'cases': results,
              'candidate_module_top_level_or_caller_import_execution': False,
              'real_proc_scan_or_read': False, 'production_or_fixture_lock_acquisition': False,
              'Lean_Lake_stock_copy_signal_controller_or_qualification_actions': False}
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'passed', 'failed', 'candidate_gate_sha256']}))


if __name__ == '__main__':
    main()
