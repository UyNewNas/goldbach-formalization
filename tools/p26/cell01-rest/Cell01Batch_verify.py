#!/usr/bin/env python3
"""Execute selected frozen merged Cell01 finite owners against an accepted cache.

No Lean/audit source is generated here. Existing suppliers are SHA-checked
and linked into one complete project namespace, without recompilation.
Normal, independent kernel, and complete owned audit each retain a receipt.
"""
from pathlib import Path
import argparse
import datetime
import errno
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import time

from Geometry01Decoding_verify import ALLOWED, dump_new, fp, parse_owned, read, same, tree_rss


DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell01-rest-finite')
DEFAULT_CACHE = Path('/workspace/p26-continuation-59264dd64286/cell01-row000')
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'


def canonical_path(path):
    path = Path(path).absolute()
    if '..' in path.parts or path.is_symlink() or path.resolve() != path:
        raise ValueError(('Noncanonical or symlinked path', str(path)))
    return path


def stage_path(stage, path):
    stage, path = canonical_path(stage), canonical_path(path)
    if not path.is_relative_to(stage):
        raise ValueError(('Write target escapes stage', str(path), str(stage)))
    return path


def stage_mkdir(stage, path, *, exist_ok):
    path = stage_path(stage, path)
    path.mkdir(parents=True, exist_ok=exist_ok)
    stage_path(stage, path)


def dump_new_in_stage(stage, path, value):
    path = stage_path(stage, path)
    stage_mkdir(stage, path.parent, exist_ok=True)
    stage_path(stage, path)
    dump_new(path, value)


def install_frozen_file(source, destination, expected, *, stage):
    source, destination = canonical_path(source), stage_path(stage, destination)
    assert source.is_file() and same(fp(source), expected), ('Supplier bytes differ', str(source))
    stage_mkdir(stage, destination.parent, exist_ok=True)
    stage_path(stage, destination)
    method = 'existing_identical'
    if destination.exists():
        assert destination.is_file() and same(fp(destination), expected), ('Refusing supplier overwrite', str(destination))
    else:
        try:
            stage_path(stage, destination)
            os.link(source, destination)
            method = 'hardlink'
        except OSError as error:
            if error.errno != errno.EXDEV:
                raise
            stage_path(stage, destination)
            with source.open('rb') as incoming, destination.open('xb') as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            method = 'cross_filesystem_copy'
    stage_path(stage, destination)
    actual = fp(destination)
    assert same(actual, expected), ('Installed supplier bytes differ', str(destination))
    return {'source': fp(source), 'installed': actual, 'method': method}


def validated_receipt(path, module, mode, source, obj, audit, context):
    prior = read(path)
    # A successful normal receipt is a recovery obligation even when later
    # context or evidence checks prevent reuse. Never rebuild its lost object.
    if (mode == 'normal' and prior.get('mode') == 'normal' and
        prior.get('status') == 'succeeded' and prior.get('exit_code') == 0 and
        prior.get('module') == module and same(prior.get('source'), source)):
        if obj is None or not same(prior.get('object'), obj):
            raise RuntimeError('RESTORE_EXACT_ACCEPTED_OBJECT: ' + json.dumps({
                'module': module, 'normal_receipt': str(path),
                'required_object': prior.get('object'), 'live_object': obj,
                'normal_recompilation_allowed': False}, sort_keys=True))
    if (prior.get('status') != 'succeeded' or prior.get('exit_code') != 0 or
        prior.get('module') != module or prior.get('mode') != mode or
        not same(prior.get('source'), source) or not same(prior.get('object'), obj) or
        prior.get('runtime_context_sha256') != context['runtime_context_sha256'] or
        not same(prior.get('supplier_manifest'), context['supplier_manifest']) or
        (mode == 'owned' and not same(prior.get('audit_source'), audit))):
        return None
    assert source['path'] == prior['source']['path'] and obj['path'] == prior['object']['path']
    assert same(fp(source['path']), source) and same(fp(obj['path']), obj)
    old_run = read(Path(path).parent.parent / 'RUN.json')
    assert all(prior.get(key) == value for key, value in old_run.items())
    for key in ('lean_version', 'mathlib_commit', 'lean_binary', 'leanchecker_binary',
                'LEAN_PATH', 'cwd', 'mathlib_package_object_roots', 'required_mathlib_packages'):
        assert prior[key] == context[key], ('Prior runtime context differs', key)
    assert prior['full_supplier_kernel_closed'] is True
    assert prior['cloud_source_generation'] is False and prior['suppliers_recompiled'] is False
    for key in ('command', 'log', 'input_fingerprints', 'supplier_installation'):
        assert same(fp(prior[key]['path']), prior[key]), ('Prior receipt dependency changed', key)
    command = read(prior['command']['path'])
    assert all(prior.get(key) == value for key, value in command.items())
    expected_flags = ['-j1', f"-M{prior['rss_limit_bytes'] // (1024**2)}",
                      '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        expected_argv = [prior['lean_binary']['path'], *expected_flags, '-o', obj['path'],
                         str(Path(source['path']).relative_to(Path(prior['cwd'])))]
        assert prior['object_before'] is None
        text = Path(prior['log']['path']).read_text()
        printed = {axiom.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                   for axiom in group.split(',') if axiom.strip()}
        assert printed <= ALLOWED and sorted(printed) == prior['printed_axioms']
    elif mode == 'kernel':
        expected_argv = [prior['leanchecker_binary']['path'], '--verbose', module]
        assert same(prior['object_before'], obj)
    else:
        assert mode == 'owned' and same(prior['object_before'], obj)
        assert prior['audit_source']['path'] == audit['path'] and same(fp(audit['path']), audit)
        expected_argv = [prior['lean_binary']['path'], *expected_flags, audit['path']]
        assert same(fp(prior['owned_declarations']['path']), prior['owned_declarations'])
        owned = parse_owned(Path(prior['log']['path']).read_text(), module)
        assert owned == read(prior['owned_declarations']['path'])
        assert owned['owned_declaration_count'] == prior['owned_declaration_count']
    assert prior['argv'] == expected_argv, 'Prior command is not the required exact mode'
    return prior


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--cache-root', type=Path, default=DEFAULT_CACHE)
    ap.add_argument('--toolchain-bin', type=Path, default=Path('/toolchains/bin'))
    ap.add_argument('--mathlib', type=Path, default=Path('/mathlib'))
    ap.add_argument('--mathlib-packages', type=Path,
                    help='Built dependency directory; defaults to <mathlib>/.lake/packages')
    ap.add_argument('--wall-seconds', type=int, default=900)
    ap.add_argument('--rss-gib', type=int, default=6)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--batch', choices=['A', 'B', 'C'])
    group.add_argument('--rows', type=int, nargs='+')
    ap.add_argument('--task-budget-seconds', type=int, default=3300)
    ap.add_argument('--row-start-reserve-seconds', type=int, default=180)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    batch_started = time.monotonic()
    assert 120 <= args.task_budget_seconds <= 3300
    assert args.wall_seconds > 0 and args.row_start_reserve_seconds >= 30
    assert re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt)
    stage, cache = map(canonical_path, (args.stage, args.cache_root))
    assert stage != cache and not stage.is_relative_to(cache) and not cache.is_relative_to(stage)
    project, objects, logs = (stage_path(stage, stage / name) for name in ('project', 'objects', 'verification'))
    assert project.is_dir()
    stage_mkdir(stage, objects, exist_ok=True)
    verifier_path = Path(__file__).with_name('Cell01Batch_VERIFIER.json')
    supplier_path = stage / 'Cell01Batch_SUPPLIERS.json'
    helper_path = Path(__file__).with_name('Geometry01Decoding_verify.py')
    verifier, supplier = read(verifier_path), read(supplier_path)
    assert same(fp(__file__), verifier['driver'])
    assert same(fp(helper_path), verifier['mature_helper'])
    assert same(fp(supplier_path), verifier['supplier_manifest'])
    expected = {item['original_ordinal']: item for item in verifier['targets']}
    assert len(expected) == len(verifier['targets']) == 142 and set(expected) == set(range(2, 144))
    ordinals = verifier['batches'][args.batch] if args.batch else args.rows
    assert len(ordinals) == len(set(ordinals)) and set(ordinals) <= set(expected)
    selected = [expected[ordinal] for ordinal in ordinals]
    all_modules = {item['module'] for item in expected.values()}
    assert all(re.fullmatch(r'ImbalancedChen\.P2OriginalSaving19Cell01Row\d{3}Finite', name)
               for name in all_modules)
    assert supplier['existing_supplier_count'] == len(supplier['suppliers']) == 399
    assert supplier['per_owner_closure_count'] == 400 and supplier['available_cache_modules'] == 420
    assert supplier['full_supplier_kernel_closed'] is True
    assert supplier['normal_only_suppliers'] == []
    frozen = {}

    def freeze(path, pin):
        path = Path(path)
        assert path.is_file() and path.resolve() == path, ('Missing or symlinked file', str(path))
        actual = fp(path)
        assert same(actual, pin), ('Frozen bytes differ', str(path))
        frozen[actual['path']] = actual

    freeze(Path(__file__).resolve(), verifier['driver'])
    freeze(helper_path.resolve(), verifier['mature_helper'])
    freeze(verifier_path.resolve(), fp(verifier_path))
    freeze(supplier_path, verifier['supplier_manifest'])
    for item in verifier['frozen_evidence']:
        relative = Path(item['archive_member'])
        assert not relative.is_absolute() and '..' not in relative.parts
        freeze(stage / relative, item)
    completion = read(stage / supplier['kernel_completion']['archive_member'])
    assert completion['status'] == 'COMPLETE_BY_EXACT_SAME_SOURCE_AND_OBJECT_P1_KERNEL_RECEIPT'
    assert completion['supplier_kernel_closed_in_combined_evidence'] is True
    assert completion['remaining_pending_supplier_kernel_modules'] == []
    recurrence = next(row for row in supplier['suppliers']
                      if row['module'] == 'ImbalancedChen.P2Winner9HomogeneousRecurrence')
    assert same(completion['source'], recurrence['source']) and same(completion['object'], recurrence['object'])
    accepted = read(stage / supplier['kernel_receipt']['archive_member'])
    kernel_result = read(stage / supplier['kernel_result']['archive_member'])
    assert accepted['status'] == kernel_result['status'] == 'succeeded' and kernel_result['exit_code'] == 0
    assert accepted['all_frozen_inputs_unchanged'] is True
    assert accepted['module'] == recurrence['module'] and accepted['mode'] == 'kernel'
    assert same(accepted['source'], recurrence['source']) and same(accepted['object'], recurrence['object'])
    assert same(accepted['command_result'], supplier['kernel_result'])
    assert same(accepted['log'], supplier['kernel_log']) and same(kernel_result['log'], supplier['kernel_log'])
    assert kernel_result['argv'][-2:] == ['--verbose', recurrence['module']]
    assert Path(kernel_result['argv'][0]).name == 'leanchecker'
    installations, seen = [], set()
    for row in supplier['suppliers']:
        name = row['module']
        assert name not in seen and name not in all_modules
        seen.add(name)
        relative = Path(name.replace('.', '/'))
        for kind, suffix, directory in [('source', '.lean', 'project'), ('object', '.olean', 'objects')]:
            origin = cache / directory / relative.with_suffix(suffix)
            destination = stage / directory / relative.with_suffix(suffix)
            freeze(origin, row[kind])
            installations.append({'module': name, 'kind': kind,
                                  **install_frozen_file(origin, destination, row[kind], stage=stage)})
            freeze(destination, row[kind])
    for item in expected.values():
        relative = Path(item['module'].replace('.', '/'))
        freeze(project / relative.with_suffix('.lean'), item['source'])
        freeze(stage / item['audit_relative_path'], item['audit'])
        assert not (cache / 'objects' / relative.with_suffix('.olean')).exists(), 'Target shadows supplier cache'
    allowed_objects = {objects / Path(name.replace('.', '/') + '.olean') for name in seen | all_modules}
    assert set(objects.rglob('*.olean')) <= allowed_objects, 'Unpinned object in isolated namespace'

    lean, checker = args.toolchain_bin / 'lean', args.toolchain_bin / 'leanchecker'
    assert lean.is_file() and checker.is_file()
    version = subprocess.run([str(lean), '--version'], text=True, capture_output=True, check=True).stdout.strip()
    assert '4.33.0-rc1' in version and LEAN_COMMIT in version
    mathlib_commit = subprocess.run(['git', '-C', str(args.mathlib), 'rev-parse', 'HEAD'],
                                   text=True, capture_output=True, check=True).stdout.strip()
    assert mathlib_commit == MATHLIB_COMMIT
    required_packages = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']
    packages = args.mathlib_packages or args.mathlib / '.lake/packages'
    package_roots = [packages / name / '.lake/build/lib/lean' for name in required_packages]
    assert all(root.is_dir() for root in package_roots)
    cli = packages / 'Cli/.lake/build/lib/lean'
    if cli.is_dir():
        package_roots.append(cli)
    mathlib_objects = args.mathlib / '.lake/build/lib/lean'
    assert mathlib_objects.is_dir()
    env = os.environ.copy()
    env.pop('LEAN_SRC_PATH', None)
    env.pop('LEAN_SYSROOT', None)
    env['PATH'] = str(args.toolchain_bin) + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = os.pathsep.join(map(str, [objects, *package_roots, mathlib_objects]))
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    run_root = logs / args.attempt
    stage_mkdir(stage, run_root, exist_ok=False)
    installation_path, inputs_path = run_root / 'SUPPLIER_INSTALLATION.json', run_root / 'INPUT_FINGERPRINTS.json'
    dump_new_in_stage(stage, installation_path, {'single_project_object_root': str(objects), 'supplier_modules': 399,
                                'entries': installations, 'suppliers_recompiled': False})
    dump_new_in_stage(stage, inputs_path, {'files': list(frozen.values()), 'cloud_source_generation': False})
    context = {'attempt': args.attempt, 'stage': str(stage), 'cache_root': str(cache),
        'lean_version': version, 'mathlib_commit': mathlib_commit,
        'lean_binary': fp(lean), 'leanchecker_binary': fp(checker),
        'driver': fp(__file__), 'mature_helper': fp(helper_path),
        'verifier_manifest': fp(verifier_path), 'supplier_manifest': fp(supplier_path),
        'supplier_installation': fp(installation_path), 'input_fingerprints': fp(inputs_path),
        'required_mathlib_packages': required_packages, 'mathlib_packages_root': str(packages),
        'mathlib_package_object_roots': list(map(str, package_roots)),
        'LEAN_PATH': env['LEAN_PATH'], 'cwd': str(project),
        'wall_limit_seconds': args.wall_seconds, 'rss_limit_bytes': args.rss_gib * 1024**3,
        'cloud_source_generation': False, 'suppliers_recompiled': False,
        'full_supplier_kernel_closed': True, 'accepted_supplier_count': 399,
        'selected_ordinals': ordinals, 'batch_label': args.batch,
        'task_budget_seconds': args.task_budget_seconds,
        'integral_claimed': False, 'P2_6_complete_claimed': False}
    stable = {key: context[key] for key in ['lean_version', 'mathlib_commit', 'lean_binary',
        'leanchecker_binary', 'supplier_manifest', 'mathlib_package_object_roots', 'LEAN_PATH', 'cwd']}
    context['runtime_context_sha256'] = hashlib.sha256(
        json.dumps(stable, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    dump_new_in_stage(stage, run_root / 'RUN.json', context)
    records = []

    def unchanged():
        for path, pin in frozen.items():
            assert same(fp(path), pin), ('Frozen file changed', path)

    completed_rows, row_durations = [], []

    def remaining():
        return args.task_budget_seconds - (time.monotonic() - batch_started)

    def pause(where, module=None, mode=None):
        unchanged()
        result = {**context, 'status': 'BUDGET_PAUSE', 'where': where, 'module': module, 'mode': mode,
                  'completed_rows': completed_rows, 'records': records,
                  'remaining_ordinals': [n for n in ordinals if n not in completed_rows],
                  'frozen_inputs_unchanged': True, 'batch_complete': False}
        dump_new_in_stage(stage, run_root / 'PARTIAL.json', result)
        print(json.dumps({'status': 'BUDGET_PAUSE', 'run': str(run_root),
                          'completed_rows': completed_rows, 'remaining_ordinals': result['remaining_ordinals']}), flush=True)
        raise SystemExit(0)

    for target in selected:
        reserve = max(args.row_start_reserve_seconds, 3 * max(row_durations, default=0))
        if remaining() < reserve:
            pause('before_row')
        module = target['module']
        relative = Path(module.replace('.', '/'))
        source_path, object_path = project / relative.with_suffix('.lean'), stage_path(stage, objects / relative.with_suffix('.olean'))
        audit_path = stage / target['audit_relative_path']
        row_started, first_record = time.monotonic(), len(records)
        for mode in ['normal', 'kernel', 'owned']:
            if remaining() <= 35:
                pause('before_mode', module, mode)
            unchanged()
            source, audit = fp(source_path), fp(audit_path)
            stage_path(stage, object_path)
            before = fp(object_path) if object_path.exists() else None
            reused = None
            for path in sorted(logs.glob(f'*/{module.split(".")[-1]}/{mode}-result.json')):
                prior = validated_receipt(path, module, mode, source, before, audit, context)
                if prior is not None:
                    reused = fp(path)
                    break
            if reused:
                frozen[str(object_path)] = before
                records.append({'module': module, 'mode': mode, 'reused_successful_receipt': reused})
                print(json.dumps(records[-1]), flush=True)
                continue
            folder = run_root / module.split('.')[-1]
            stage_mkdir(stage, folder, exist_ok=True)
            stage_mkdir(stage, object_path.parent, exist_ok=True)
            stage_path(stage, object_path)
            flags = ['-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
            if mode == 'normal':
                assert not object_path.exists(), 'Refusing to overwrite an unreceipted object'
                argv = [str(lean), *flags, '-o', str(object_path), str(source_path.relative_to(project))]
            elif mode == 'kernel':
                assert object_path.is_file()
                argv = [str(checker), '--verbose', module]
            else:
                assert object_path.is_file()
                argv = [str(lean), *flags, str(audit_path)]
            command_limit = min(args.wall_seconds, remaining() - 30)
            assert command_limit > 0
            command = {**context, 'module': module, 'mode': mode, 'argv': argv, 'source': source,
                       'original_ordinal': target['original_ordinal'],
                       'effective_wall_limit_seconds': command_limit,
                       'object_before': before, 'audit_source': audit if mode == 'owned' else None,
                       'started_unix': time.time()}
            command_path = folder / (mode + '-command.json')
            dump_new_in_stage(stage, command_path, command)
            log = folder / (mode + '.log')
            started, peak, reason, code = time.monotonic(), 0, None, None
            print(json.dumps({'module': module, 'mode': mode, 'started': True}), flush=True)
            stage_path(stage, log)
            with log.open('x') as output:
                try:
                    stage_path(stage, project)
                    stage_path(stage, object_path)
                    proc = subprocess.Popen(argv, cwd=project, env=env, stdout=output,
                                            stderr=subprocess.STDOUT, start_new_session=True)
                    while proc.poll() is None:
                        peak = max(peak, tree_rss(proc.pid))
                        if peak > args.rss_gib * 1024**3:
                            reason = 'rss_limit'
                        elif time.monotonic() - started > command_limit:
                            reason = 'timeout'
                        if reason:
                            os.killpg(proc.pid, signal.SIGKILL)
                            break
                        time.sleep(0.1)
                    code = proc.wait()
                except Exception as error:
                    reason = 'launch_or_monitor_error: ' + repr(error)
                    if 'proc' in locals() and proc.poll() is None:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
            result = {**command, 'status': reason or ('succeeded' if code == 0 else 'failed'),
                      'exit_code': code, 'elapsed_seconds': time.monotonic() - started,
                      'peak_rss_bytes': peak, 'command': fp(command_path), 'log': fp(log),
                      'object': fp(object_path) if object_path.exists() else None}
            try:
                unchanged()
                if mode != 'normal':
                    assert same(result['object'], before), 'Checked object changed'
                if code == 0 and mode == 'normal':
                    printed = {axiom.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', log.read_text())
                               for axiom in group.split(',') if axiom.strip()}
                    assert printed <= ALLOWED and result['object'] is not None
                    result['printed_axioms'] = sorted(printed)
                if code == 0 and mode == 'owned':
                    owned = parse_owned(log.read_text(), module)
                    owned_path = folder / 'owned-declarations.json'
                    dump_new_in_stage(stage, owned_path, owned)
                    result['owned_declarations'] = fp(owned_path)
                    result['owned_declaration_count'] = owned['owned_declaration_count']
            except Exception as error:
                result['status'], result['validation_error'] = 'evidence_validation_failed', repr(error)
            receipt_path = folder / (mode + '-result.json')
            dump_new_in_stage(stage, receipt_path, result)
            records.append({'module': module, 'mode': mode, 'receipt': fp(receipt_path), 'status': result['status']})
            print(json.dumps(records[-1]), flush=True)
            if result['status'] != 'succeeded':
                dump_new_in_stage(stage, run_root / 'STOPPED.json', {'failed_module': module, 'failed_mode': mode, 'records': records})
                raise SystemExit(1)
            frozen[str(object_path)] = result['object']
        row_records = records[first_record:]
        assert len(row_records) == 3 and [item['mode'] for item in row_records] == ['normal', 'kernel', 'owned']
        proof_chain = []
        for item in row_records:
            ref = item.get('receipt', item.get('reused_successful_receipt'))
            accepted = validated_receipt(Path(ref['path']), module, item['mode'], fp(source_path),
                                         fp(object_path), fp(audit_path), context)
            assert accepted is not None and same(fp(ref['path']), ref)
            proof_chain.append(ref)
        folder = run_root / module.split('.')[-1]
        stage_mkdir(stage, folder, exist_ok=True)
        dump_new_in_stage(stage, folder / 'ROW_ACCEPTED.json', {'status': 'PASS_NORMAL_KERNEL_FULL_OWNED',
            'module': module, 'original_ordinal': target['original_ordinal'],
            'source': fp(source_path), 'object': fp(object_path), 'audit': fp(audit_path),
            'chain': proof_chain, 'runtime_context_sha256': context['runtime_context_sha256'],
            'owned_declaration_count': accepted['owned_declaration_count']})
        completed_rows.append(target['original_ordinal'])
        row_durations.append(time.monotonic() - row_started)
        print(json.dumps({'row_accepted': target['original_ordinal'], 'elapsed_seconds': row_durations[-1],
                          'remaining_task_seconds': remaining()}), flush=True)
    unchanged()
    dump_new_in_stage(stage, run_root / 'SUCCESS.json', {**context, 'status': 'succeeded', 'records': records,
        'accepted_targets': len(completed_rows), 'completed_rows': completed_rows,
        'frozen_inputs_unchanged': True, 'batch_complete': True})
    print(json.dumps({'status': 'succeeded', 'run': str(run_root), 'accepted_targets': len(completed_rows),
                      'full_supplier_kernel_closed': True}), flush=True)


if __name__ == '__main__':
    main()
