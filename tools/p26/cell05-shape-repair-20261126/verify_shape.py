#!/usr/bin/env python3
"""Run only one supplied ShapeArrays owner; reuse exact old suppliers without recompiling."""
from pathlib import Path
import argparse
import datetime
import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from origin_join import validate_origin, require_separate_stage
from boundary import BOUNDARY, TARGET
from runtime_compat import git_commit_readonly
from receipt_support import ALLOWED, tree_rss
from receipt_checks import (MODES, TOOL_REL, canonical, checked, check_context_inputs, dependency_objects,
                            disjoint, dump_new, expected_argv, fp, namespace_files, parse_target_owned, prior, read,
                            reject_missing_successful_objects, require, same, target_paths, tree_files,
                            require_accepted_prefix, require_single_scope, validate_layout, validate_step, validate_success)

LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
PACKAGES = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']


def load_configuration(here):
    canonical(here, True)
    manifest = read(here / 'SHAPE_REPAIR_VERIFIER.json')
    require(manifest['schema'] == 'cell05_shape_repair_frozen_verifier_v1' and
            manifest['target_count'] == 1 and manifest['expected_steps'] == 3 and
            manifest['repair_source_ready'] is True, 'Unprepared or wrong single-target repair package')
    files = manifest['workflow_files']
    require(len({row['relative_path'] for row in files}) == len(files), 'Duplicate workflow file')
    required = {'verify_shape.py', 'receipt_checks.py', 'receipt_support.py', 'export_shape.py', 'stage_entry.py',
                'origin_join.py', 'boundary.py', 'BOUNDARY.json', 'SHAPE_SOURCE_MANIFEST.json'}
    required |= {row['relative_path'] for row in BOUNDARY['shared_helper_pins']}
    require(required <= {row['relative_path'] for row in files}, 'Missing frozen execution or origin helper')
    for row in files:
        path = canonical(here / row['relative_path'], True)
        require(path.is_relative_to(here) and not path.name.endswith('.olean') and
                same(fp(path), row), f'Workflow file pin mismatch: {path}')
    for row in BOUNDARY['shared_helper_pins']:
        require(same(fp(here / row['relative_path']), row), 'Original evidence helper changed')
    source_manifest = read(here / 'SHAPE_SOURCE_MANIFEST.json')
    require(source_manifest['schema'] == 'cell05_shape_repair_source_v1' and
            source_manifest['module'] == TARGET and
            source_manifest['original_source'] == BOUNDARY['original_target']['source'],
            'Replacement source provenance differs')
    joined = validate_origin()
    registry = joined['registry']
    require_single_scope({'targets': manifest['targets'], 'suppliers': registry['suppliers']})
    target = manifest['targets'][0]
    require(same(target['source'], source_manifest['source']) and
            isinstance(target['source']['bytes'], int) and target['source']['bytes'] > 0 and
            re.fullmatch('[0-9a-f]{64}', target['source']['sha256']), 'Repair source pin is unresolved or inconsistent')
    require(target['audit'] == BOUNDARY['original_target']['audit'] and
            target['source_member'] == 'sources/' + TARGET.replace('.', '/') + '.lean' and
            target['audit_relative_path'] == 'owned-audits/' + TARGET.split('.')[-1] + '.lean',
            'Repair source/audit layout or original owned audit differs')
    require(same(fp(here / target['audit_relative_path']), target['audit']), 'Original owned audit changed')
    return manifest, registry, joined


def frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects, joined):
    expected = {}

    def add(path, identity):
        path = canonical(path)
        old = expected.setdefault(str(path), {'path': str(path), 'bytes': identity['bytes'], 'sha256': identity['sha256']})
        require(same(old, identity), f'Conflicting frozen pin: {path}')

    add(here / 'SHAPE_REPAIR_VERIFIER.json', fp(here / 'SHAPE_REPAIR_VERIFIER.json'))
    for row in manifest['workflow_files']:
        add(here / row['relative_path'], row)
    for row in joined['frozen_evidence']:
        add(row['path'], row)
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


def bind_context_to_package(context, here, manifest, registry, joined=None):
    """Exporter uses current pinned package and actual files, not receipt labels alone."""
    stage = canonical(context['stage'], True)
    require(here == stage / TOOL_REL, 'Context stage and packaged workflow differ')
    require(context['schema'] == 'cell05_shape_repair_context_v1', 'Unknown context schema')
    require_single_scope(context)
    require(context['targets'] == manifest['targets'] and context['suppliers'] == registry['suppliers'],
            'Context target/supplier inventory differs from pinned package')
    joined = validate_origin() if joined is None else joined
    require_separate_stage(stage, joined)
    original = joined['fields_context']
    for key in ('runtime', 'mathlib', 'mathlib_objects', 'mathlib_dependency_parent', 'mathlib_package_object_roots'):
        require(context[key] == original[key], f'Original accepted fields runtime changed: {key}')
    environment = dict(original['environment'])
    environment['LEAN_PATH'] = os.pathsep.join([context['objects'], *context['mathlib_package_object_roots'], context['mathlib_objects']])
    require(context['environment'] == environment, 'Original accepted environment changed beyond the new object root')
    require(context['runtime_guard'] == joined['runtime_guard'] and
            context['supplier_join'] == joined['supplier_join'] and
            context['origin_stage'] == joined['origin_stage'], 'Context guard/join identity changed')
    require(context['runtime']['mathlib_commit'] == MATHLIB_COMMIT, 'Unexpected Mathlib commit')
    require('4.33.0-rc1' in context['runtime']['lean_version'] and LEAN_COMMIT in context['runtime']['lean_version'],
            'Unexpected Lean version')
    for key in ('lean_binary', 'leanchecker_binary'):
        require(same(context['runtime'][key], registry['runtime_binaries'][key]), f'Unaccepted runtime bytes: {key}')
    supplier_project = canonical(context['supplier_project'], True)
    supplier_objects = canonical(context['supplier_objects'], True)
    require(str(supplier_project) == joined['supplier_project'] and str(supplier_objects) == joined['supplier_objects'],
            'Context supplier paths differ from validated join')
    disjoint(stage, supplier_project)
    disjoint(stage, supplier_objects)
    disjoint(supplier_project, supplier_objects)
    require(context['frozen_inputs'] == frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects, joined),
            'Context does not freeze the exact current inputs')
    packages_parent = canonical(context['mathlib_dependency_parent'], True)
    roots = [str(packages_parent / name / '.lake/build/lib/lean') for name in PACKAGES]
    cli = packages_parent / 'Cli/.lake/build/lib/lean'
    if cli.exists():
        roots.append(str(cli))
    require(context['mathlib_package_object_roots'] == roots, 'Mathlib package path inventory mismatch')
    mathlib = canonical(context['mathlib'], True)
    require(context['mathlib_objects'] == str(mathlib / '.lake/build/lib/lean'), 'Mathlib object root mismatch')
    commit = git_commit_readonly(mathlib)
    require(commit == MATHLIB_COMMIT, 'Current Mathlib checkout changed')
    require(0 < context['rss_limit_bytes'] <= 12 * 1024**3 and context['rss_limit_bytes'] % 1024**3 == 0
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
        os.link(source, destination)
        method = 'hardlink'
    require(same(fp(destination), identity), f'Installed identity mismatch: {destination}')
    return {'source': fp(source), 'installed': fp(destination), 'method': method}


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization; inherited audit parser uses assertions')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, required=True)
    ap.add_argument('--rss-gib', type=int, default=6)
    ap.add_argument('--wall-seconds', type=int, default=900)
    ap.add_argument('--max-new-steps', type=int, help='Pause after 0, 1 or 2 new steps; accepted stages are reused on resume')
    ap.add_argument('--preflight-only', action='store_true', help='Validate and install exact files; execute no Lean')
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
    args = ap.parse_args()
    here = canonical(Path(os.path.abspath(__file__)).parent, True)
    manifest, registry, joined = load_configuration(here)
    require_separate_stage(args.stage, joined)
    targets = [row['module'] for row in manifest['targets']]
    suppliers = [row['module'] for row in registry['suppliers']]
    supplier_project, supplier_objects = Path(joined['supplier_project']), Path(joined['supplier_objects'])
    stage = validate_layout(args.stage, here, supplier_project, supplier_objects,
                            suppliers + targets, targets, args.attempt)
    lock_path = canonical(stage / 'EXECUTION.lock')
    lock = lock_path.open('a')
    fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    reject_missing_successful_objects(stage, targets)
    require(0 < args.rss_gib <= 12 and args.wall_seconds > 0, 'RSS must be 1..12 GiB and wall time positive')
    require(args.max_new_steps is None or 0 <= args.max_new_steps <= 3, 'Single-owner step budget must be 0..3')
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
    # Reuse the accepted P2 runtime and environment; only relocate the project object root.
    original = joined['fields_context']
    runtime = original['runtime']
    lean, checker = Path(runtime['lean_binary']['path']), Path(runtime['leanchecker_binary']['path'])
    for path, key in [(lean, 'lean_binary'), (checker, 'leanchecker_binary')]:
        require(fp(path) == runtime[key] and same(runtime[key], registry['runtime_binaries'][key]),
                f'Runtime binary mismatch: {path}')
    mathlib = canonical(original['mathlib'], True)
    packages_parent = canonical(original['mathlib_dependency_parent'], True)
    package_roots = [Path(root) for root in original['mathlib_package_object_roots']]
    mathlib_objects = canonical(original['mathlib_objects'], True)
    for root in [*package_roots, mathlib_objects]:
        canonical(root, True)
        require(root.is_dir() and not (root / 'ImbalancedChen').exists(), f'Missing package or fallback project namespace: {root}')
    tracked_env = dict(original['environment'])
    tracked_env['LEAN_PATH'] = os.pathsep.join(str(path) for path in [stage / 'objects', *package_roots, mathlib_objects])
    env = {key: value for key, value in tracked_env.items() if value is not None}
    installed = []
    for module, kind, source, dest, identity in plans:
        installed.append({'module': module, 'kind': kind, **install(source, dest, identity)})
    frozen = frozen_expected_paths(stage, here, manifest, registry, supplier_project, supplier_objects, joined)
    context = {'schema': 'cell05_shape_repair_context_v1', 'stage': str(stage), 'cwd': str(stage / 'project'),
               'objects': str(stage / 'objects'), 'supplier_project': str(supplier_project), 'supplier_objects': str(supplier_objects),
               'runtime': runtime,
               'mathlib': str(mathlib), 'mathlib_objects': str(mathlib_objects), 'mathlib_dependency_parent': str(packages_parent),
               'mathlib_package_object_roots': [str(root) for root in package_roots], 'environment': tracked_env,
               'rss_limit_bytes': args.rss_gib * 1024**3, 'wall_limit_seconds': args.wall_seconds,
               'targets': manifest['targets'], 'suppliers': registry['suppliers'], 'frozen_inputs': frozen,
               'full_supplier_kernel_closed_in_combined_evidence': joined['full_supplier_kernel_closed_in_combined_evidence'],
               'runtime_guard': joined['runtime_guard'], 'supplier_join': joined['supplier_join'],
               'origin_stage': joined['origin_stage'],
               'cloud_source_generation': False, 'old_supplier_proof_commands': 0,
               'original_thirteen_owner_proof_commands': 0}
    bind_context_to_package(context, here, manifest, registry, joined)
    # Validate every reusable success before creating a new attempt. No successful step is replayed.
    reusable = {(module, mode): prior(context, module, mode) for module in targets for mode in MODES}
    accepted_before = require_accepted_prefix(context, reusable)
    for module in targets:
        obj = target_paths(context, module)['object']
        require(not obj.exists() or reusable[module, 'normal'] is not None,
                f'Unreceipted object blocks compilation; preserve evidence for manual recovery: {obj}')
    if args.preflight_only:
        print(json.dumps({'status': 'PASS_PREFLIGHT_NO_LEAN', 'targets': 1, 'planned_steps': 3,
                          'accepted_existing_steps': accepted_before, 'suppliers': 88, 'actual_supplier_union': 42,
                          'runtime_guard': joined['runtime_guard'], 'Lean_commands_executed': 0}), flush=True)
        return
    run_root = stage / 'verification' / args.attempt
    run_root.mkdir(parents=True, exist_ok=False)
    run_path = run_root / 'RUN.json'
    dump_new(run_path, {'schema': 'cell05_shape_repair_run_v1', 'attempt': args.attempt, 'context': context})
    dump_new(run_root / 'SUPPLIER_REUSE.json', {'entries': installed, 'old_supplier_proof_commands': 0,
                                               'single_project_object_root': str(stage / 'objects'),
                                               'joined': {k: v for k, v in joined.items() if k not in ('fields_context', 'frozen_evidence', 'registry')}})
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
            if args.max_new_steps is not None and newly >= args.max_new_steps:
                dump_new(run_root / 'STOPPED.json', {'status': 'stopped', 'reason': 'new_step_budget', 'run': fp(run_path),
                                                    'records': records, 'accepted_steps': len(records),
                                                    'accepted_targets': len(records) // 3,
                                                    'newly_executed_steps': newly, 'reused_steps': reused,
                                                    'whole_geometry_decoded': False, 'P2_6_complete': False})
                print(json.dumps({'status': 'PAUSED_ACCEPTED_PREFIX', 'run': str(run_root),
                                  'accepted_steps': len(records), 'accepted_targets': len(records) // 3,
                                  'newly_executed_steps': newly, 'reused_steps': reused}), flush=True)
                return
            paths = target_paths(context, module)
            before = fp(paths['object']) if paths['object'].exists() else None
            require((mode == 'normal') == (before is None), f'Object existence incompatible with step: {module} / {mode}')
            folder = run_root / module.split('.')[-1]
            folder.mkdir(parents=True, exist_ok=True)
            command_path = folder / (mode + '-command.json')
            command = {'schema': 'cell05_shape_repair_step_command_v1', 'run': fp(run_path), 'module': module, 'mode': mode,
                       'argv': expected_argv(context, module, mode), 'cwd': context['cwd'], 'environment': tracked_env,
                       'source': fp(paths['source']), 'audit_source': fp(paths['audit']) if mode == 'owned' else None,
                       'dependency_objects': dependency_objects(context, module), 'object_before': before,
                       'started_unix': time.time()}
            dump_new(command_path, command)
            log = folder / (mode + '.log')
            print(json.dumps({'module': module, 'mode': mode, 'disposition': 'started'}), flush=True)
            started, peak, reason = time.monotonic(), 0, None
            proc, rc = None, None
            with log.open('x') as output:
                try:
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
                except (Exception, KeyboardInterrupt) as error:
                    reason = 'launch_or_wait_error'
                    output.write(repr(error) + '\n')
                    if proc is not None:
                        if proc.poll() is None:
                            os.killpg(proc.pid, signal.SIGKILL)
                        rc = proc.wait()
            newly += 1
            result = {'schema': 'cell05_shape_repair_step_result_v1', 'run': fp(run_path), 'command': fp(command_path),
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
                        owned = parse_target_owned(text, context, module)
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
            dump_new(seal_path, {'schema': 'cell05_shape_repair_step_accepted_v1', 'status': 'accepted', 'module': module, 'mode': mode,
                                 'run': fp(run_path), 'command': fp(command_path), 'result': fp(result_path), 'object': result['object']})
            validated = validate_step(fp(seal_path), context, module, mode)
            frozen_new[result['object']['path']] = result['object']
            records.append({'module': module, 'mode': mode, 'accepted': validated['accepted'], 'disposition': 'executed'})
            print(json.dumps({'module': module, 'mode': mode, 'disposition': 'accepted',
                              'elapsed_seconds': result['elapsed_seconds'], 'peak_rss_bytes': result['peak_rss_bytes']}), flush=True)
    check_context_inputs(context)
    success_path = run_root / 'SUCCESS.json'
    dump_new(success_path, {'schema': 'cell05_shape_repair_success_v1', 'status': 'succeeded', 'run': fp(run_path),
                            'context': context, 'records': records, 'accepted_targets': 1, 'accepted_steps': 3,
                            'newly_executed_steps': newly, 'reused_steps': reused, 'frozen_inputs_unchanged': True,
                            'whole_geometry_decoded': False, 'P2_6_complete': False,
                            'original_thirteen_owners_reexecuted': False})
    validate_success(success_path)
    print(json.dumps({'status': 'succeeded', 'run': str(run_root), 'accepted_targets': 1, 'accepted_steps': 3,
                      'newly_executed_steps': newly, 'reused_steps': reused, 'old_supplier_proof_commands': 0}), flush=True)


if __name__ == '__main__':
    main()
