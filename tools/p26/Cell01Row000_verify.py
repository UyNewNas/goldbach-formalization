#!/usr/bin/env python3
"""Execute the frozen 22-owner finite Cell01 row000 pilot on P3.

The established Geometry01 verifier supplies fingerprint, RSS and complete
owned-inventory helpers. All Lean and audit sources are prepared locally.
The original-moment bridge is held for P1 and is never a target here.
"""
from pathlib import Path
import argparse
import datetime
import errno
import json
import os
import re
import shutil
import signal
import subprocess
import time

from Geometry01Decoding_verify import ALLOWED, dump_new, fp, parse_owned, read, same, tree_rss


DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell01-row000')
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'


def install_frozen_file(source, destination, expected):
    """Install identical supplier bytes into the single project module tree."""
    source, destination = Path(source), Path(destination)
    assert same(fp(source), expected), ('Supplier installation source mismatch', str(source))
    destination.parent.mkdir(parents=True, exist_ok=True)
    method = 'existing_identical'
    if destination.exists():
        assert same(fp(destination), expected), ('Refusing supplier overwrite', str(destination))
    else:
        try:
            os.link(source, destination)
            method = 'hardlink'
        except OSError as error:
            if error.errno != errno.EXDEV:
                raise
            with source.open('rb') as incoming, destination.open('xb') as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            method = 'cross_filesystem_copy'
    installed = fp(destination)
    assert same(installed, expected), ('Installed supplier identity mismatch', str(destination))
    return {'source': fp(source), 'installed': installed, 'method': method}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--toolchain-bin', type=Path, default=Path('/toolchains/bin'))
    ap.add_argument('--mathlib', type=Path, default=Path('/mathlib'))
    ap.add_argument('--mathlib-packages', type=Path,
                    help='Built package directory; defaults to <mathlib>/.lake/packages')
    ap.add_argument('--wall-seconds', type=int, default=900)
    ap.add_argument('--rss-gib', type=int, default=24)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt)
    stage = args.stage.resolve()
    project, objects, logs = stage / 'project', stage / 'objects', stage / 'verification'
    assert project.is_dir()
    objects.mkdir(parents=True, exist_ok=True)
    verifier_path = Path(__file__).with_name('Cell01Row000_VERIFIER.json')
    supplier_path = stage / 'Cell01Row000_SUPPLIERS.json'
    verifier, supplier = read(verifier_path), read(supplier_path)
    helper = Path(__file__).with_name('Geometry01Decoding_verify.py')
    assert same(fp(Path(__file__)), verifier['driver']), 'Driver fingerprint mismatch'
    assert same(fp(helper), verifier['mature_helper']), 'Mature helper fingerprint mismatch'
    assert same(fp(supplier_path), verifier['supplier_manifest']), 'Supplier manifest mismatch'
    expected = {row['module']: row for row in verifier['targets']}
    assert len(expected) == len(verifier['targets']) == 22
    assert all(not name.endswith('OriginalFloorBridge') for name in expected)
    frozen = {}

    def freeze(path, identity):
        got = fp(path)
        assert same(got, identity), ('Frozen supplier/source mismatch', str(path))
        frozen[got['path']] = got

    supplier_roots = []
    for package in supplier['packages']:
        root = (stage / package['relative_root']).resolve()
        supplier_roots.append(root)
        freeze(root / package['manifest']['archive_member'], package['manifest'])
        for evidence in package.get('completion_evidence', []):
            freeze(root / evidence['archive_member'], evidence)
    assert [root.name for root in supplier_roots] == ['cell00', 'geometry01', 'moment01']
    installations = []
    for row in supplier['suppliers']:
        rel = Path(row['module'].replace('.', '/'))
        for location in row['locations']:
            root = (stage / location['relative_root']).resolve()
            freeze(root / location['source_member'], row['source'])
            freeze(root / location['object_member'], row['object'])
        # Lean resolves the package namespace from a search-path root; separate
        # partial ImbalancedChen trees cannot serve as an object overlay.
        # Install the verified bytes, without recompilation or source editing.
        origin = row['locations'][0]
        origin_root = (stage / origin['relative_root']).resolve()
        for kind, member, destination in [
                ('source', origin['source_member'], project / rel.with_suffix('.lean')),
                ('object', origin['object_member'], objects / rel.with_suffix('.olean'))]:
            installations.append({'module': row['module'], 'kind': kind,
                                  **install_frozen_file(origin_root / member, destination, row[kind])})
            freeze(destination, row[kind])
        # Every actual duplicate in the Lean search path must have the same
        # object and source identities, including an unexpected local shadow.
        for root in [stage, *supplier_roots]:
            obj = root / 'objects' / rel.with_suffix('.olean')
            if not obj.exists():
                continue
            freeze(obj, row['object'])
            candidates = [root / directory / rel.with_suffix('.lean')
                          for directory in ['project', 'sources']]
            present = [path for path in candidates if path.exists()]
            assert present, ('Object without a corresponding pinned source', str(obj))
            for source in present:
                freeze(source, row['source'])
    for module, item in expected.items():
        rel = Path(module.replace('.', '/'))
        freeze(project / rel.with_suffix('.lean'), item['source'])
        freeze(Path(__file__).parent / item['audit_relative_path'], item['audit'])
        assert not any((root / 'objects' / rel.with_suffix('.olean')).exists()
                       for root in supplier_roots), ('New target shadowed by supplier root', module)

    lean, checker = args.toolchain_bin / 'lean', args.toolchain_bin / 'leanchecker'
    assert lean.is_file() and checker.is_file()
    version = subprocess.run([str(lean), '--version'], text=True, capture_output=True, check=True).stdout.strip()
    assert '4.33.0-rc1' in version and LEAN_COMMIT in version, version
    required_packages = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']
    packages_root = args.mathlib_packages or args.mathlib / '.lake/packages'
    package_roots = [packages_root / name / '.lake/build/lib/lean' for name in required_packages]
    for name, path in zip(required_packages, package_roots):
        assert path.is_dir(), ('Missing required mathlib package object root', name, str(path))
    cli_objects = packages_root / 'Cli/.lake/build/lib/lean'
    if cli_objects.is_dir():
        package_roots.append(cli_objects)
    mathlib_objects = args.mathlib / '.lake/build/lib/lean'
    assert mathlib_objects.is_dir(), str(mathlib_objects)
    mathlib_commit = subprocess.run(['git', '-C', str(args.mathlib), 'rev-parse', 'HEAD'],
                                   text=True, capture_output=True, check=True).stdout.strip()
    assert mathlib_commit == MATHLIB_COMMIT, mathlib_commit
    env = os.environ.copy()
    env['PATH'] = str(args.toolchain_bin) + os.pathsep + env.get('PATH', '')
    object_roots = [objects]
    assert all(root.is_dir() for root in object_roots)
    env['LEAN_PATH'] = os.pathsep.join(str(path) for path in [*object_roots, *package_roots, mathlib_objects])
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    run_root = logs / args.attempt
    run_root.mkdir(parents=True, exist_ok=False)
    installation_path = run_root / 'SUPPLIER_INSTALLATION.json'
    dump_new(installation_path, {'single_project_object_root': str(objects),
                                'supplier_modules': len(supplier['suppliers']),
                                'entries': installations, 'suppliers_recompiled': False})
    context = {'attempt': args.attempt, 'stage': str(stage), 'lean_version': version,
               'mathlib_commit': mathlib_commit, 'required_mathlib_packages': required_packages,
               'mathlib_packages_root': str(packages_root),
               'mathlib_package_object_roots': [str(path) for path in package_roots],
               'optional_Cli_object_root_present': cli_objects.is_dir(),
               'driver': fp(Path(__file__)), 'mature_helper': fp(helper),
               'verifier_manifest': fp(verifier_path), 'supplier_manifest': fp(supplier_path),
               'supplier_installation': fp(installation_path),
               'LEAN_PATH': env['LEAN_PATH'], 'cwd': str(project),
               'wall_limit_seconds': args.wall_seconds, 'rss_limit_bytes': args.rss_gib * 1024**3,
               'cloud_source_generation': False, 'suppliers_recompiled': False,
               'pending_supplier_kernel': supplier['normal_only_suppliers'],
               'pending_supplier_kernel_job': supplier['pending_supplier_kernel_job'],
               'full_supplier_kernel_closed': not supplier['normal_only_suppliers'],
               'held_targets': verifier['held_targets']}
    dump_new(run_root / 'RUN.json', context)
    records = []

    def accepted_step(module, mode, source, obj, audit_source):
        for path in sorted(logs.glob(f'*/{module.split(".")[-1]}/{mode}-result.json')):
            previous = read(path)
            if previous.get('status') != 'succeeded' or previous.get('exit_code') != 0:
                continue
            if not same(previous.get('source'), source) or not same(previous.get('object'), obj):
                continue
            if not same(previous.get('supplier_manifest'), context['supplier_manifest']):
                continue
            if previous.get('lean_version') != version or previous.get('mathlib_commit') != mathlib_commit:
                continue
            if mode == 'owned' and not same(previous.get('audit_source'), audit_source):
                continue
            assert same(fp(previous['log']['path']), previous['log']), ('Prior log changed', str(path))
            return fp(path)
        return None

    def execute(module, mode):
        item = expected[module]
        source_path = project / (module.replace('.', '/') + '.lean')
        object_path = objects / (module.replace('.', '/') + '.olean')
        audit_path = Path(__file__).parent / item['audit_relative_path']
        source, audit_source = fp(source_path), fp(audit_path)
        assert same(source, item['source']) and same(audit_source, item['audit'])
        obj_before = fp(object_path) if object_path.exists() else None
        prior = accepted_step(module, mode, source, obj_before, audit_source)
        if prior is not None:
            records.append({'module': module, 'mode': mode, 'reused_successful_receipt': prior})
            print(json.dumps(records[-1]), flush=True)
            return
        folder = run_root / module.split('.')[-1]
        folder.mkdir(parents=True, exist_ok=True)
        object_path.parent.mkdir(parents=True, exist_ok=True)
        if mode == 'normal':
            assert not object_path.exists(), ('Refusing to overwrite an unreceipted object', str(object_path))
            argv = [str(lean), '-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0',
                    '-o', str(object_path), str(source_path.relative_to(project))]
        elif mode == 'kernel':
            assert object_path.exists(), ('Missing object', module)
            argv = [str(checker), '--verbose', module]
        else:
            assert mode == 'owned' and object_path.exists()
            argv = [str(lean), '-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0', str(audit_path)]
        command = {**context, 'module': module, 'mode': mode, 'argv': argv, 'source': source,
                   'object_before': obj_before, 'audit_source': audit_source if mode == 'owned' else None,
                   'started_unix': time.time()}
        dump_new(folder / (mode + '-command.json'), command)
        log = folder / (mode + '.log')
        started, peak, reason = time.monotonic(), 0, None
        print(json.dumps({'module': module, 'mode': mode, 'started': True}), flush=True)
        with log.open('x') as output:
            proc = subprocess.Popen(argv, cwd=project, env=env, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            while proc.poll() is None:
                rss = tree_rss(proc.pid)
                peak = max(peak, rss)
                if rss > args.rss_gib * 1024**3:
                    reason = 'rss_limit'
                elif time.monotonic() - started > args.wall_seconds:
                    reason = 'timeout'
                if reason:
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            rc = proc.wait()
        result = {**command, 'status': reason or ('succeeded' if rc == 0 else 'failed'), 'exit_code': rc,
                  'elapsed_seconds': time.monotonic() - started, 'peak_rss_bytes': peak,
                  'log': fp(log), 'object': fp(object_path) if object_path.exists() else None}
        try:
            assert same(fp(source_path), source), 'Source changed during verification'
            if mode != 'normal':
                assert same(result['object'], obj_before), 'Verified object changed'
            text = log.read_text()
            if rc == 0 and mode == 'normal':
                reported = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                            for a in group.split(',') if a.strip()}
                assert reported <= ALLOWED, ('Forbidden printed axiom', sorted(reported))
                assert result['object'] is not None, 'Successful compile without object'
                result['printed_axioms'] = sorted(reported)
            if rc == 0 and mode == 'owned':
                owned = parse_owned(text, module)
                owned_path = folder / 'owned-declarations.json'
                dump_new(owned_path, owned)
                result['owned_declarations'] = fp(owned_path)
                result['owned_declaration_count'] = owned['owned_declaration_count']
        except Exception as error:
            result['status'] = 'evidence_validation_failed'
            result['validation_error'] = repr(error)
        path = folder / (mode + '-result.json')
        dump_new(path, result)
        records.append({'module': module, 'mode': mode, 'receipt': fp(path), 'status': result['status']})
        print(json.dumps(records[-1]), flush=True)
        if result['status'] != 'succeeded':
            dump_new(run_root / 'STOPPED.json', {'failed_module': module, 'failed_mode': mode, 'records': records})
            raise SystemExit(1)

    for item in verifier['targets']:
        for mode in ['normal', 'kernel', 'owned']:
            execute(item['module'], mode)
    for path, identity in frozen.items():
        assert same(fp(path), identity), ('Frozen source/object changed', path)
    dump_new(run_root / 'SUCCESS.json', {**context, 'status': 'succeeded', 'records': records,
                                        'accepted_targets': 22, 'frozen_inputs_unchanged': True})
    print(json.dumps({'status': 'succeeded', 'run': str(run_root), 'accepted_targets': 22,
                      'pending_supplier_kernel': supplier['normal_only_suppliers']}), flush=True)


if __name__ == '__main__':
    main()
