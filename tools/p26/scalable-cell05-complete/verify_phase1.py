#!/usr/bin/env python3
"""Run only 15 supplied new owners; reuse exact old suppliers without recompiling."""
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
import sys
import time

sys.dont_write_bytecode = True
from baseline_checks import verify_baseline
from receipt_support import ALLOWED, parse_owned, tree_rss
from receipt_checks import (MODES, TOOL_REL, canonical, checked, check_context_inputs, dependency_objects,
                            disjoint, dump_new, expected_argv, fp, namespace_files, prior, read,
                            reject_missing_successful_objects, require, same, target_paths, tree_files,
                            validate_layout, validate_step, validate_success)

LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
PACKAGES = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']


def load_configuration(here):
    canonical(here, True)
    manifest = read(here / 'ROW_NETWORK_VERIFIER.json')
    require(manifest['schema'] == 'cell05_complete_frozen_verifier_v2', 'Unknown verifier schema')
    for row in manifest['workflow_files']:
        path = here / row['relative_path']
        require(same(fp(path), row), f'Workflow file pin mismatch: {path}')
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    source_manifest = read(here / 'ROW_NETWORK_SOURCE_MANIFEST.json')
    require(len(manifest['targets']) == len(source_manifest['owners']) == 15, 'Expected 15 new owners')
    require(len(registry['suppliers']) == registry['supplier_count'] == 15, 'Expected 15 old suppliers')
    source_rows = {row['module']: row for row in source_manifest['owners']}
    require(len(source_rows) == 15, 'Duplicate new source module')
    for row in manifest['targets']:
        require(same(row['source'], source_rows[row['module']]['source']), 'Verifier/source-manifest mismatch')
        require(row['project_imports'] == source_rows[row['module']]['project_imports'], 'Import graph mismatch')
        require(same(fp(here / row['audit_relative_path']), row['audit']), 'Owned audit changed')
    require(set(source_rows).isdisjoint(row['module'] for row in registry['suppliers']), 'New/old owner overlap')
    graph = {row['module']: row['project_imports'] for row in registry['suppliers'] + manifest['targets']}
    available = {row['module'] for row in registry['suppliers']}
    for row in manifest['targets']:
        require(set(row['project_imports']) <= available, f'New owner order is not topological: {row["module"]}')
        available.add(row['module'])
        seen, active = set(), set()

        def visit(module):
            require(module in graph and module not in active, f'Missing/cyclic project import: {module}')
            if module in seen:
                return
            active.add(module)
            for dependency in graph[module]:
                visit(dependency)
            active.remove(module)
            seen.add(module)

        for dependency in row['project_imports']:
            visit(dependency)
        require(row['transitive_dependencies'] == sorted(seen), 'Transitive import closure changed')
    return manifest, registry, verify_baseline(here)


def frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects):
    expected = {}

    def add(path, identity):
        path = canonical(path)
        old = expected.setdefault(str(path), {'path': str(path), 'bytes': identity['bytes'], 'sha256': identity['sha256']})
        require(same(old, identity), f'Conflicting frozen pin: {path}')

    add(here / 'ROW_NETWORK_VERIFIER.json', fp(here / 'ROW_NETWORK_VERIFIER.json'))
    for row in manifest['workflow_files']:
        add(here / row['relative_path'], row)
    for row in read(here / 'BASELINE_EVIDENCE.json')['members']:
        add(here / row['relative_path'], row)
    for row in registry['suppliers']:
        relative = Path(row['module'].replace('.', '/'))
        for kind, suffix, provider, destination in [('source', '.lean', supplier_project, stage / 'project'),
                                                   ('object', '.olean', supplier_objects, stage / 'objects')]:
            add(provider / relative.with_suffix(suffix), row[kind])
            add(destination / relative.with_suffix(suffix), row[kind])
    for row in manifest['targets']:
        relative = Path(row['module'].replace('.', '/'))
        add(stage / 'sources' / relative.with_suffix('.lean'), row['source'])
        add(stage / 'project' / relative.with_suffix('.lean'), row['source'])
        add(here / row['audit_relative_path'], row['audit'])
    return [expected[path] for path in sorted(expected)]


def bind_context_to_package(context, here, manifest, registry):
    """Exporter uses current pinned package and actual files, not receipt labels alone."""
    stage = canonical(context['stage'], True)
    require(here == stage / TOOL_REL, 'Context stage and packaged workflow differ')
    require(context['schema'] == 'cell05_complete_context_v2', 'Unknown context schema')
    require(context['targets'] == manifest['targets'] and context['suppliers'] == registry['suppliers'],
            'Context target/supplier inventory differs from pinned package')
    require(context['runtime']['mathlib_commit'] == MATHLIB_COMMIT, 'Unexpected Mathlib commit')
    require('4.33.0-rc1' in context['runtime']['lean_version'] and LEAN_COMMIT in context['runtime']['lean_version'],
            'Unexpected Lean version')
    for key in ('lean_binary', 'leanchecker_binary'):
        require(same(context['runtime'][key], registry['runtime_binaries'][key]), f'Unaccepted runtime bytes: {key}')
    supplier_project = canonical(context['supplier_project'], True)
    supplier_objects = canonical(context['supplier_objects'], True)
    disjoint(stage, supplier_project)
    disjoint(stage, supplier_objects)
    disjoint(supplier_project, supplier_objects)
    require(context['frozen_inputs'] == frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects),
            'Context does not freeze the exact current inputs')
    packages_parent = canonical(context['mathlib_dependency_parent'], True)
    roots = [str(packages_parent / name / '.lake/build/lib/lean') for name in PACKAGES]
    cli = packages_parent / 'Cli/.lake/build/lib/lean'
    if cli.exists():
        roots.append(str(cli))
    require(context['mathlib_package_object_roots'] == roots, 'Mathlib package path inventory mismatch')
    mathlib = canonical(context['mathlib'], True)
    require(context['mathlib_objects'] == str(mathlib / '.lake/build/lib/lean'), 'Mathlib object root mismatch')
    commit = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, capture_output=True, check=True).stdout.strip()
    require(commit == MATHLIB_COMMIT, 'Current Mathlib checkout changed')
    require(context['rss_limit_bytes'] > 0 and context['rss_limit_bytes'] % 1024**3 == 0
            and context['wall_limit_seconds'] > 0, 'Invalid resource limits')
    require(context['full_supplier_kernel_closed_in_combined_evidence'] is True, 'Supplier context join not closed')
    check_context_inputs(context)


def install(source, destination, identity):
    source, destination = canonical(source, True), canonical(destination)
    require(same(fp(source), identity), f'Installation source mismatch: {source}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    canonical(destination.parent, True)
    method = 'existing_identical'
    if destination.exists():
        require(same(fp(destination), identity), f'Refusing overwrite: {destination}')
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
    require(same(fp(destination), identity), f'Installed identity mismatch: {destination}')
    return {'source': fp(source), 'installed': fp(destination), 'method': method}


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization; inherited audit parser uses assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ('stage', 'supplier-project', 'supplier-objects', 'toolchain-bin', 'mathlib'):
        ap.add_argument('--' + name, type=Path, required=True)
    ap.add_argument('--mathlib-packages', type=Path)
    ap.add_argument('--rss-gib', type=int, default=6)
    ap.add_argument('--wall-seconds', type=int, default=900)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    here = canonical(Path(os.path.abspath(__file__)).parent, True)
    manifest, registry, baseline = load_configuration(here)
    targets = [row['module'] for row in manifest['targets']]
    suppliers = [row['module'] for row in registry['suppliers']]
    stage = validate_layout(args.stage, here, args.supplier_project, args.supplier_objects,
                            suppliers + targets, targets, args.attempt)
    reject_missing_successful_objects(stage, targets)
    require(args.rss_gib > 0 and args.wall_seconds > 0, 'Positive resource limits required')
    supplier_project, supplier_objects = args.supplier_project, args.supplier_objects
    plans = []
    for row in registry['suppliers']:
        relative = Path(row['module'].replace('.', '/'))
        for kind, suffix, provider, destination in [('source', '.lean', supplier_project, stage / 'project'),
                                                   ('object', '.olean', supplier_objects, stage / 'objects')]:
            source, dest = provider / relative.with_suffix(suffix), destination / relative.with_suffix(suffix)
            require(same(fp(source), row[kind]), f'Supplier bytes mismatch: {source}')
            if kind == 'object':
                require(not list(source.parent.glob(source.name + '.*')), f'Unexpected supplier object sidecars: {source}')
            if dest.exists():
                require(same(fp(dest), row[kind]), f'Existing stage supplier differs: {dest}')
            plans.append((row['module'], kind, source, dest, row[kind]))
    for row in manifest['targets']:
        relative = Path(row['module'].replace('.', '/'))
        source, dest = stage / 'sources' / relative.with_suffix('.lean'), stage / 'project' / relative.with_suffix('.lean')
        require(same(fp(source), row['source']), f'Candidate source mismatch: {source}')
        require(not (supplier_objects / relative.with_suffix('.olean')).exists(), 'New owner is shadowed by a supplier object')
        if dest.exists():
            require(same(fp(dest), row['source']), f'Existing candidate source differs: {dest}')
        plans.append((row['module'], 'new_source', source, dest, row['source']))
    # Every source and planned destination was checked above; no stage writes precede this point.
    toolchain = canonical(args.toolchain_bin, True)
    lean, checker = toolchain / 'lean', toolchain / 'leanchecker'
    for path, key in [(lean, 'lean_binary'), (checker, 'leanchecker_binary')]:
        require(same(fp(path), registry['runtime_binaries'][key]), f'Runtime binary mismatch: {path}')
    mathlib = canonical(args.mathlib, True)
    packages_parent = canonical(args.mathlib_packages or mathlib / '.lake/packages', True)
    package_roots = [packages_parent / name / '.lake/build/lib/lean' for name in PACKAGES]
    cli = packages_parent / 'Cli/.lake/build/lib/lean'
    if cli.exists():
        package_roots.append(cli)
    mathlib_objects = mathlib / '.lake/build/lib/lean'
    for root in [*package_roots, mathlib_objects]:
        canonical(root, True)
        require(root.is_dir() and not (root / 'ImbalancedChen').exists(), f'Missing package or fallback project namespace: {root}')
    env = os.environ.copy()
    env.update({'PATH': str(toolchain) + os.pathsep + env.get('PATH', ''),
                'LEAN_PATH': os.pathsep.join(str(path) for path in [stage / 'objects', *package_roots, mathlib_objects]),
                'LEAN_SYSROOT': str(toolchain.parent), 'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1'})
    version = subprocess.run([str(lean), '--version'], text=True, capture_output=True, check=True, env=env).stdout.strip()
    require('4.33.0-rc1' in version and LEAN_COMMIT in version, 'Lean version mismatch')
    commit = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, capture_output=True, check=True).stdout.strip()
    require(commit == MATHLIB_COMMIT, 'Mathlib commit mismatch')
    installed = []
    for module, kind, source, dest, identity in plans:
        installed.append({'module': module, 'kind': kind, **install(source, dest, identity)})
    frozen = frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects)
    tracked_env = {key: env[key] for key in ['PATH', 'LEAN_PATH', 'LEAN_SYSROOT', 'LEAN_NUM_THREADS', 'OMP_NUM_THREADS']}
    for key in ['LD_LIBRARY_PATH', 'LEAN_OPTS', 'LEAN_SRC_PATH']:
        tracked_env[key] = env.get(key)
    context = {'schema': 'cell05_complete_context_v2', 'stage': str(stage), 'cwd': str(stage / 'project'),
               'objects': str(stage / 'objects'), 'supplier_project': str(supplier_project), 'supplier_objects': str(supplier_objects),
               'runtime': {'lean_binary': fp(lean), 'leanchecker_binary': fp(checker), 'lean_version': version, 'mathlib_commit': commit},
               'mathlib': str(mathlib), 'mathlib_objects': str(mathlib_objects), 'mathlib_dependency_parent': str(packages_parent),
               'mathlib_package_object_roots': [str(root) for root in package_roots], 'environment': tracked_env,
               'rss_limit_bytes': args.rss_gib * 1024**3, 'wall_limit_seconds': args.wall_seconds,
               'targets': manifest['targets'], 'suppliers': registry['suppliers'], 'frozen_inputs': frozen,
               'full_supplier_kernel_closed_in_combined_evidence': baseline['full_supplier_kernel_closed_in_combined_evidence'],
               'cloud_source_generation': False, 'old_supplier_proof_commands': 0}
    bind_context_to_package(context, here, manifest, registry)
    # Validate every reusable success before creating a new attempt. No successful step is replayed.
    reusable = {(module, mode): prior(context, module, mode) for module in targets for mode in MODES}
    for module in targets:
        obj = target_paths(context, module)['object']
        require(not obj.exists() or reusable[module, 'normal'] is not None,
                f'Unreceipted object blocks compilation; preserve evidence for manual recovery: {obj}')
    run_root = stage / 'verification' / args.attempt
    run_root.mkdir(parents=True, exist_ok=False)
    run_path = run_root / 'RUN.json'
    dump_new(run_path, {'schema': 'cell05_complete_run_v2', 'attempt': args.attempt, 'context': context})
    dump_new(run_root / 'SUPPLIER_REUSE.json', {'entries': installed, 'old_supplier_proof_commands': 0,
                                               'single_project_object_root': str(stage / 'objects'), 'baseline': baseline})
    records, frozen_new = [], {}
    newly = reused = 0
    for module in targets:
        for mode in MODES:
            for path, identity in frozen_new.items():
                require(fp(path) == identity, f'Previously accepted new object changed: {path}')
            check_context_inputs(context)
            previous = reusable[module, mode]
            if previous:
                validate_step(previous['accepted'], context, module, mode, check_inputs=False)
                records.append({'module': module, 'mode': mode, 'accepted': previous['accepted'], 'disposition': 'reused'})
                frozen_new[previous['result']['object']['path']] = previous['result']['object']
                reused += 1
                print(json.dumps({'module': module, 'mode': mode, 'disposition': 'reused'}), flush=True)
                continue
            paths = target_paths(context, module)
            before = fp(paths['object']) if paths['object'].exists() else None
            require((mode == 'normal') == (before is None), f'Object existence incompatible with step: {module} / {mode}')
            folder = run_root / module.split('.')[-1]
            folder.mkdir(parents=True, exist_ok=True)
            command_path = folder / (mode + '-command.json')
            command = {'schema': 'cell05_step_command_v2', 'run': fp(run_path), 'module': module, 'mode': mode,
                       'argv': expected_argv(context, module, mode), 'cwd': context['cwd'], 'environment': tracked_env,
                       'source': fp(paths['source']), 'audit_source': fp(paths['audit']) if mode == 'owned' else None,
                       'dependency_objects': dependency_objects(context, module), 'object_before': before,
                       'started_unix': time.time()}
            dump_new(command_path, command)
            log = folder / (mode + '.log')
            print(json.dumps({'module': module, 'mode': mode, 'disposition': 'started'}), flush=True)
            started, peak, reason = time.monotonic(), 0, None
            with log.open('x') as output:
                proc = subprocess.Popen(command['argv'], cwd=context['cwd'], env=env, stdout=output,
                                        stderr=subprocess.STDOUT, start_new_session=True)
                while proc.poll() is None:
                    peak = max(peak, tree_rss(proc.pid))
                    if peak > context['rss_limit_bytes']:
                        reason = 'rss_limit'
                    elif time.monotonic() - started > context['wall_limit_seconds']:
                        reason = 'timeout'
                    if reason:
                        os.killpg(proc.pid, signal.SIGKILL)
                        break
                    time.sleep(0.1)
                rc = proc.wait()
            newly += 1
            result = {'schema': 'cell05_step_result_v2', 'run': fp(run_path), 'command': fp(command_path),
                      'module': module, 'mode': mode, 'status': reason or ('succeeded' if rc == 0 else 'failed'),
                      'exit_code': rc, 'termination_reason': reason, 'elapsed_seconds': time.monotonic() - started,
                      'peak_rss_bytes': peak, 'source': command['source'], 'audit_source': command['audit_source'],
                      'dependency_objects': command['dependency_objects'], 'log': fp(log),
                      'object': fp(paths['object']) if paths['object'].exists() else None}
            try:
                check_context_inputs(context)
                for path, identity in frozen_new.items():
                    require(fp(path) == identity, f'Previously accepted new object changed: {path}')
                require(result['dependency_objects'] == dependency_objects(context, module), 'Dependencies changed during command')
                if mode != 'normal':
                    require(result['object'] == before, 'Verified object changed during command')
                if result['status'] == 'succeeded':
                    require(result['object'] is not None, 'Successful command without object')
                    text = log.read_text()
                    if mode == 'normal':
                        axioms = sorted({a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                                         for a in group.split(',') if a.strip()})
                        require(set(axioms) <= ALLOWED, 'Forbidden printed axiom')
                        result['printed_axioms'] = axioms
                    elif mode == 'kernel':
                        require(text.strip() == 'replaying ' + module, 'Unexpected kernel target log')
                    else:
                        owned = parse_owned(text, module)
                        owned_path = folder / 'owned-declarations.json'
                        dump_new(owned_path, owned)
                        result['owned_declarations'] = fp(owned_path)
                        result['owned_declaration_count'] = owned['owned_declaration_count']
            except Exception as error:
                result['status'] = 'evidence_validation_failed'
                result['validation_error'] = repr(error)
            result_path = folder / (mode + '-result.json')
            dump_new(result_path, result)
            if result['status'] != 'succeeded':
                dump_new(run_root / 'STOPPED.json', {'status': 'stopped', 'run': fp(run_path), 'failed_result': fp(result_path),
                                                    'records': records, 'newly_executed_steps': newly, 'reused_steps': reused})
                raise SystemExit(1)
            seal_path = folder / (mode + '-accepted.json')
            dump_new(seal_path, {'schema': 'cell05_step_accepted_v2', 'status': 'accepted', 'module': module, 'mode': mode,
                                 'run': fp(run_path), 'command': fp(command_path), 'result': fp(result_path), 'object': result['object']})
            validated = validate_step(fp(seal_path), context, module, mode)
            frozen_new[result['object']['path']] = result['object']
            records.append({'module': module, 'mode': mode, 'accepted': validated['accepted'], 'disposition': 'executed'})
            print(json.dumps({'module': module, 'mode': mode, 'disposition': 'accepted',
                              'elapsed_seconds': result['elapsed_seconds'], 'peak_rss_bytes': result['peak_rss_bytes']}), flush=True)
    check_context_inputs(context)
    success_path = run_root / 'SUCCESS.json'
    dump_new(success_path, {'schema': 'cell05_complete_success_v2', 'status': 'succeeded', 'run': fp(run_path),
                            'context': context, 'records': records, 'accepted_targets': 15, 'accepted_steps': 45,
                            'newly_executed_steps': newly, 'reused_steps': reused, 'frozen_inputs_unchanged': True,
                            'whole_geometry_decoded': False, 'P2_6_complete': False})
    validate_success(success_path)
    print(json.dumps({'status': 'succeeded', 'run': str(run_root), 'accepted_targets': 15, 'accepted_steps': 45,
                      'newly_executed_steps': newly, 'reused_steps': reused, 'old_supplier_proof_commands': 0}), flush=True)


if __name__ == '__main__':
    main()
