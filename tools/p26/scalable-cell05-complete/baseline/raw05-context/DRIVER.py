#!/usr/bin/env python3
"""One raw05 kernel compatibility check in the exact completed pilot context."""
from pathlib import Path
import argparse
import datetime
import io
import json
import os
import signal
import subprocess
import tarfile
import time

from Geometry01Decoding_verify import dump_new, fp, read, same, tree_rss


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    assert args.attempt and all(c.isalnum() or c in '_-' for c in args.attempt)
    script = Path(__file__).resolve()
    plan_path = script.with_name('RAW05_CONTEXT_CHECK_PLAN.json')
    plan = read(plan_path)
    assert same(fp(script), plan['driver'])
    stage = Path(plan['stage'])
    baseline_run = stage / plan['baseline_run_member']
    baseline_command = stage / plan['baseline_command_member']
    assert same(fp(baseline_run), plan['baseline_run_identity'])
    assert same(fp(baseline_command), plan['baseline_command_identity'])
    run, original_command = read(baseline_run), read(baseline_command)
    assert run == plan['baseline_run_content']
    assert original_command['cwd'] == run['cwd']
    assert original_command['LEAN_PATH'] == run['LEAN_PATH']
    assert original_command['lean_version'] == run['lean_version']
    assert original_command['mathlib_commit'] == run['mathlib_commit']
    checker = Path(original_command['argv'][0])
    lean = checker.with_name('lean')
    assert checker == Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker')
    assert checker.is_file() and lean.is_file()
    assert original_command['argv'][1:] == ['--verbose', plan['reference_module']]
    module = plan['target_module']
    assert module == 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05'
    argv = [str(checker), '--verbose', module]
    assert plan['command_count'] == 1 and plan['normal_commands'] == 0

    def snapshot():
        protected = []
        for item in plan['protected_baseline_files']:
            path = stage / item['member']
            got = fp(path)
            assert same(got, item), ('Baseline file changed', str(path))
            protected.append(got)
        archive = fp(stage / plan['baseline_archive']['member'])
        assert same(archive, plan['baseline_archive'])
        suppliers = []
        for item in plan['supplier_file_groups']:
            directory = stage / item['directory']
            paths = sorted(p for p in directory.glob(item['stem'] + '.*') if p.is_file())
            got = [fp(path) for path in paths]
            expected = item['files']
            assert [str(p.relative_to(stage)) for p in paths] == [x['member'] for x in expected], (
                'Supplier sidecar inventory changed', item['module'], item['kind'])
            assert all(same(a, b) for a, b in zip(got, expected)), (
                'Supplier source/object/sidecar changed', item['module'], item['kind'])
            suppliers.append({'module': item['module'], 'kind': item['kind'], 'files': got})
        return {'protected_baseline_files': protected, 'baseline_archive': archive,
                'nine_supplier_sources_objects_and_sidecars': suppliers,
                'lean_binary': fp(lean), 'leanchecker_binary': fp(checker),
                'driver': fp(script), 'plan': fp(plan_path)}

    before = snapshot()
    output = stage / 'raw05-context-compatibility' / args.attempt
    output.mkdir(parents=True, exist_ok=False)
    for name, source in [('RUN.json', baseline_run), ('BASELINE_KERNEL_COMMAND.json', baseline_command),
                         ('PLAN.json', plan_path), ('DRIVER.py', script)]:
        with (output / name).open('xb') as stream:
            stream.write(source.read_bytes())
    dump_new(output / 'BEFORE.json', before)
    env = os.environ.copy()
    env['PATH'] = str(checker.parent) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = run['LEAN_PATH']
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    command = {'schema': 'raw05_current_pilot_context_kernel_command_v1',
               'module': module, 'mode': 'kernel', 'argv': argv, 'cwd': run['cwd'],
               'LEAN_PATH': run['LEAN_PATH'], 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1',
               'complete_baseline_run': run, 'baseline_run': fp(baseline_run),
               'baseline_kernel_command': fp(baseline_command),
               'frozen_before': fp(output / 'BEFORE.json'),
               'normal_commands': 0, 'kernel_commands': 1, 'six_new_owners_replayed': False,
               'sources_generated_or_changed': False, 'old_receipts_changed': False,
               'started_unix': time.time()}
    dump_new(output / 'COMMAND.json', command)
    log = output / 'kernel.log'
    started, peak, reason = time.monotonic(), 0, None
    with log.open('x') as stream:
        proc = subprocess.Popen(argv, cwd=run['cwd'], env=env,
                                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        while proc.poll() is None:
            peak = max(peak, tree_rss(proc.pid))
            if peak > run['rss_limit_bytes']:
                reason = 'rss_limit'
            elif time.monotonic() - started > run['wall_limit_seconds']:
                reason = 'timeout'
            if reason:
                os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.1)
        rc = proc.wait()
    elapsed = time.monotonic() - started
    after = snapshot()
    dump_new(output / 'AFTER.json', after)
    assert before == after, 'Frozen files or binaries changed across kernel check'
    result = {'schema': 'raw05_current_pilot_context_kernel_result_v1',
              'status': 'PASS_RAW05_KERNEL_IN_PILOT_CONTEXT' if rc == 0 and reason is None else reason or 'failed',
              'module': module, 'exit_code': rc, 'elapsed_seconds': elapsed,
              'peak_rss_bytes': peak, 'command': fp(output / 'COMMAND.json'), 'log': fp(log),
              'before': fp(output / 'BEFORE.json'), 'after': fp(output / 'AFTER.json'),
              'frozen_sources_objects_sidecars_context_unchanged': True,
              'normal_commands': 0, 'kernel_commands': 1, 'six_new_owners_replayed': False,
              'baseline_18_steps_and_archive_unchanged': True,
              'historical_evidence_rewritten': False,
              'context_object_differences': plan['historical_to_current_dependency_changes'],
              'historical_RAW05_normal_owned_retained': True,
              'whole_geometry_decoded': False, 'P2_6_complete': False}
    dump_new(output / 'RESULT.json', result)
    selected = sorted(path for path in output.iterdir() if path.is_file())
    manifest = {'schema': 'raw05_current_context_kernel_addendum_v1',
                'status': result['status'], 'members': [{'member': p.name, **fp(p)} for p in selected],
                'original_six_owner_evidence_archive': plan['baseline_archive'],
                'original_raw05_historical_archive': plan['historical_raw05_archive'],
                'normal_commands': 0, 'kernel_commands': 1, 'six_new_owners_replayed': False}
    manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode()
    archive = output / 'raw05-current-context-kernel-addendum.tar.xz'
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for path in selected:
            data = path.read_bytes()
            info = tarfile.TarInfo(path.name)
            info.size, info.mode = len(data), 0o644
            tar.addfile(info, io.BytesIO(data))
        info = tarfile.TarInfo('EXPORT_MANIFEST.json')
        info.size, info.mode = len(manifest_bytes), 0o644
        tar.addfile(info, io.BytesIO(manifest_bytes))
    with (output / 'EXPORT_MANIFEST.json').open('xb') as stream:
        stream.write(manifest_bytes)
    print(json.dumps({'status': result['status'], 'run': str(output), 'archive': fp(archive),
                      'result': fp(output / 'RESULT.json'), 'elapsed_seconds': elapsed,
                      'peak_rss_bytes': peak, 'normal_commands': 0, 'kernel_commands': 1}), flush=True)
    raise SystemExit(0 if result['status'] == 'PASS_RAW05_KERNEL_IN_PILOT_CONTEXT' else 1)


if __name__ == '__main__':
    main()
