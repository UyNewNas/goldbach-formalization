#!/usr/bin/env python3
"""Isolated read-only workers for the explicit recovery protocol, never old proofs."""
from pathlib import Path
import fcntl
import hashlib
import importlib
import json
import os
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
manifest_bytes = (HERE / 'WORKFLOW_MANIFEST.json').read_bytes()
manifest = json.loads(manifest_bytes)
if manifest.get('schema') != 'p26_runtime_recovery_workflow_v1':
    raise ValueError('Unknown recovery source manifest')
names = [row['relative_path'] for row in manifest['files']]
if len(set(names)) != len(names) or not {'recovery.py', 'recovery_worker.py', 'protocol_core.py', 'ANCHORS.json'} <= set(names):
    raise ValueError('Incomplete or duplicate recovery source manifest')
authenticated = {}
for row in manifest['files']:
    if Path(row['relative_path']).name != row['relative_path'] or row['relative_path'] in ('.', '..'):
        raise ValueError('Unsafe recovery source member')
    data = (HERE / row['relative_path']).read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise ValueError('Recovery source changed: ' + row['relative_path'])
    authenticated[row['relative_path']] = data
core = types.ModuleType('p26_recovery_core')
core.__file__ = str(HERE / 'protocol_core.py')
exec(compile(authenticated['protocol_core.py'], core.__file__, 'exec'), core.__dict__)
require, fp, read, checked, refs = core.require, core.fp, core.read, core.checked, core.refs
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,
        'Use isolated source-only Python: -I -S -B without optimization')
A = json.loads(authenticated['ANCHORS.json'])
require(core.protocol_files(HERE) == sorted([{'path': str(HERE / 'WORKFLOW_MANIFEST.json'), **core.pin(manifest_bytes)},
        *[{'path': str(HERE / name), **core.pin(body)} for name, body in authenticated.items()]], key=lambda r: r['path']),
        'Recovery bootstrap inputs changed after authentication')


def prepare(kind):
    nh, nc, ns, nf = core.authenticate_family(A['remaining9'])
    boundary = read(nh / 'BOUNDARY.json')
    require(boundary['runtime_guard'] == A['original_guard'], 'Original guard anchor differs')
    spec = A['remaining9'] if kind in ('runtime', 'remaining8', 'verify') else boundary['origins'][kind]
    here, config, sources, frozen = core.authenticate_family(spec)
    if kind == 'prefix13':
        require('prefix_validator' not in sources, 'Unexpected prefix validator shadow')
        sources['prefix_validator'] = ns['prefix_validator']
    finder = core.PinnedSourceFinder(sources)
    sys.meta_path.insert(0, finder)
    sys.path[:] = [p for p in sys.path if p and not p.startswith('/workspace/') and 'site-packages' not in p]
    sys.addaudithook(core.deny_worker_mutation)
    R = importlib.import_module('receipt_checks')
    RC = importlib.import_module('runtime_compat')
    name = {'prefix13': 'verify_connections14', 'shape1': 'verify_shape',
            'remaining8': 'verify_remaining9', 'runtime': 'verify_remaining9', 'verify': 'verify_remaining9'}[kind]
    V = importlib.import_module(name)
    finder.check_loaded()
    return nh, boundary, spec, here, config, R, RC, V, finder, [*nf, *frozen]


def package_check(path, identity, kind, config, spec):
    value = checked(identity, path) if identity else read(path)
    members = value['members']
    require(len({r['member'] for r in members}) == len(members), 'Duplicate source package member')
    schemas = {'prefix13': 'cell05_connections14_source_package_v1', 'shape1': 'cell05_shape_repair_source_package_v1',
               'remaining8': 'cell05_remaining9_source_package_v1'}
    count = {'prefix13': 14, 'shape1': 1, 'remaining8': 9}[kind]
    require(value['schema'] == schemas[kind] and value['target_count'] == count and
            value['planned_new_steps'] == 3*count and value['accepted_steps'] == 0,
            'Original source package scope differs')
    if kind == 'shape1':
        require(value['repair_source_ready'] is True, 'Original repair package is unresolved')
    tool = spec['tool_relative_path']
    expected = {'sources/' + r['module'].replace('.', '/') + '.lean': r['source'] for r in config['targets']}
    expected.update({tool + '/' + r['relative_path']: r for r in config['workflow_files']})
    expected[tool + '/' + spec['verifier_name']] = spec['verifier']
    require({r['member'] for r in members} == set(expected), 'Source package/workflow inventory differs')
    result = [fp(path)]
    for row in members:
        member = core.relative(row['member'])
        require(not str(member).endswith('.olean'), 'Unexpected object body in source package')
        p = Path(path).parent / member
        require(core.same(fp(p), row) and core.same(row, expected[row['member']]), 'Original source package member changed')
        result.append(fp(p))
    return result


def current_runtime(RC, original_context, guard):
    checked(A['original_guard'])
    snapshot = checked(A['original_snapshot'])
    require(guard['snapshot'] == A['original_snapshot'] and
            guard['logical_roots'] == RC.logical_roots({'roots': [{k: v for k, v in row.items() if k != 'files'}
                                                                for row in snapshot['roots']]}) and
            guard['all_selected_bytes_rehashed_before_guard'] is True and
            guard['historical_loaded_inventory_retroactively_claimed'] is False and
            guard['kernel_compatibility_replays_required'] == 0 and guard['normal_replays_permitted'] is False,
            'Current witness is not bound to the original full snapshot')
    RC.check_runtime_guard_value(guard)
    runtime = original_context['runtime']
    require(runtime == snapshot['runtime'], 'Recovered context runtime differs from original snapshot')
    for key in ('lean_binary', 'leanchecker_binary'):
        require(fp(runtime[key]['path']) == runtime[key], 'Actual runtime binary changed')
    require(RC.git_commit_readonly(original_context['mathlib']) == A['mathlib_commit'] == runtime['mathlib_commit'],
            'Current Mathlib commit differs')
    require('4.33.0-rc1' in runtime['lean_version'] and A['lean_commit'] in runtime['lean_version'],
            'Original Lean runtime identity differs')


def runtime_capture(nh, RC):
    SC = importlib.import_module('supplier_capsule')
    original = nh / 'original103'
    plan = SC.load_plan(original)
    summaries, snapshot = RC.runtime_evidence(original, plan)
    require(summaries['P2']['output'] == A['original_snapshot'] and len(snapshot['roots']) == 10,
            'Wrong complete original runtime snapshot')
    old = checked(A['original_guard'])
    require(old['snapshot'] == A['original_snapshot'] and old['logical_roots'] == RC.logical_roots(summaries['P2']),
            'Historical guard/snapshot link differs')
    failure = None
    try:
        RC.check_runtime_guard_value(old)
    except (ValueError, FileNotFoundError) as error:
        failure = {'type': type(error).__name__, 'message': str(error)}
    require(failure is not None, 'Expected the observed historical physical-guard failure')
    # This existing function rehashes every selected byte and rejects all missing/extra selected files.
    guard = RC.capture_runtime_guard(original, plan)
    context = SC.metadata(original, plan, 'fields73')[1]['context']
    current_runtime(RC, context, guard)
    require(fp(A['original_guard']['path']) == A['original_guard'], 'Original guard was modified')
    return {'schema': 'p26_runtime_recovery_capture_result_v1', 'status': 'COMPLETE_TEN_ROOT_CONTENT_EQUALITY',
            'original_guard': A['original_guard'], 'original_snapshot': A['original_snapshot'],
            'original_guard_current_lstat_passed': False, 'original_guard_failure': failure,
            'current_guard': guard, 'runtime': context['runtime'],
            'roots': summaries['P2']['roots'], 'Lean_commands': 0,
            'historical_loaded_runtime_inventory_claimed': False}


def fields_join(here, R):
    """Rebuild every old fields88 join relationship without its obsolete live lstat test."""
    F = importlib.import_module('fields_only_join')
    join = read(here / 'SUPPLIER_JOIN.json')
    stage = here.parents[2]
    project, objects = Path(join['supplier_project']), Path(join['supplier_objects'])
    expected_provider = Path('/workspace/p26-cell05-connections14-provider-557a12f3bcd7')
    require(project == expected_provider / 'project' and objects == expected_provider / 'objects', 'Fields provider moved')
    F.disjoint(stage, project)
    F.disjoint(stage, objects)
    data = F.fields_inputs(here, project, objects)
    F.check_provider(project, objects, data['registry'])
    guard = A['original_guard']
    require(guard['path'] == str(expected_provider / 'evidence/RUNTIME_GUARD.json'), 'Fields guard location changed')
    require(read(guard['path'])['snapshot'] == data['runtime_summaries']['P2']['output'] and
            read(guard['path'])['logical_roots'] == F.logical_roots(data['runtime_summaries']['P2']),
            'Historical fields guard/snapshot link differs')
    mapping = expected_provider / 'evidence/FIELDS73_PATH_MAP.json'
    require(read(mapping) == F.field_path_map(data, project, objects), 'Original fields path map differs')
    expected = {'schema': F.JOIN_SCHEMA, 'new_stage': str(stage),
        'supplier_plan': fp(here / 'SUPPLIER_PLAN.json'), 'supplier_registry': fp(here / 'SUPPLIER_REGISTRY.json'),
        'target_selection': fp(here / 'CONNECTION_TARGETS.json'),
        'supplier_project': str(project), 'supplier_objects': str(objects),
        'fields_archive': data['fields_spec']['archive'], 'baseline_files': data['baseline_files'],
        'old_baseline': data['baseline'], 'historical_fields73': {
            'run': data['plan']['batches']['fields73']['run'], 'success': data['plan']['batches']['fields73']['success'],
            'accepted_steps': 219, 'owned_declarations': 2875},
        'runtime_guard': guard, 'fields_path_map': fp(mapping), 'old_proof_commands': 0,
        'compatibility_kernel_replays': 0, 'existing_supplier_object_bodies_copied': 0,
        'row_capsule_required': False, 'historical_loaded_runtime_inventory_claimed': False,
        'full_supplier_kernel_closed_in_combined_evidence': True}
    require(join == expected, 'Original fields88 join document changed')
    evidence = [fp(here / 'SUPPLIER_JOIN.json'), fp(here / 'SUPPLIER_PLAN.json'), fp(here / 'SUPPLIER_REGISTRY.json'),
                fp(here / 'CONNECTION_TARGETS.json'), join['fields_archive'], guard, fp(mapping),
                data['runtime_summaries']['P2']['output'], *data['baseline_files']]
    evidence += [fp(here / row['relative_path']) for row in data['plan']['metadata_files']]
    evidence += [fp(here / 'RUNTIME_COMPATIBILITY_PINS.json')]
    evidence += [fp(here / row['relative_path']) for row in read(here / 'RUNTIME_COMPATIBILITY_PINS.json')['files']]
    return {'supplier_count': 88, 'actual_selected_supplier_union': 83,
            'fields_context': data['fields_context'], 'registry': data['registry'],
            'runtime_guard': guard, 'supplier_project': str(project), 'supplier_objects': str(objects),
            'frozen_evidence': evidence, 'full_supplier_kernel_closed_in_combined_evidence': True,
            'old_Lean_commands_executed': 0, 'compatibility_kernel_replays': 0}


def configuration(kind, here, config, R, joined):
    count = {'prefix13': 14, 'shape1': 1, 'remaining8': 9}[kind]
    schema = {'prefix13': 'cell05_connections14_frozen_verifier_v1', 'shape1': 'cell05_shape_repair_frozen_verifier_v1',
              'remaining8': 'cell05_remaining9_frozen_verifier_v1'}[kind]
    require(config['schema'] == schema and config['target_count'] == count and config['expected_steps'] == count*3,
            'Original frozen verifier scope differs')
    registry = joined['registry'] if kind == 'shape1' else read(here / 'SUPPLIER_REGISTRY.json')
    if kind == 'shape1':
        B = importlib.import_module('boundary')
        require(config['repair_source_ready'] is True, 'Original ShapeArrays source was not prepared')
        R.require_single_scope({'targets': config['targets'], 'suppliers': registry['suppliers']})
        source = read(here / 'SHAPE_SOURCE_MANIFEST.json')
        target = config['targets'][0]
        require(source['schema'] == 'cell05_shape_repair_source_v1' and source['module'] == B.TARGET and
                source['original_source'] == B.BOUNDARY['original_target']['source'] and
                core.same(target['source'], source['source']) and target['audit'] == B.BOUNDARY['original_target']['audit'],
                'Original ShapeArrays source provenance differs')
        require(target['source_member'] == 'sources/' + B.TARGET.replace('.', '/') + '.lean' and
                target['audit_relative_path'] == 'owned-audits/' + B.TARGET.split('.')[-1] + '.lean', 'Shape audit layout differs')
        for row in B.BOUNDARY['shared_helper_pins']:
            require(core.same(fp(here / row['relative_path']), row), 'Original shared Shape helper differs')
    else:
        expected_suppliers = 88 if kind == 'prefix13' else 117
        source = read(here / 'CONNECTIONS_SOURCE_MANIFEST.json')
        selection = read(here / 'CONNECTION_TARGETS.json')
        require(selection['targets'] == config['targets'] and selection['target_count'] == count and
                selection['expected_steps'] == count*3 and len(source['owners']) == count,
                'Frozen target selection/source manifest differs')
        owners = {r['module']: r for r in source['owners']}
        require(len(owners) == count, 'Duplicate source owner')
        require(len(registry['suppliers']) == registry['supplier_count'] == expected_suppliers and
                len({r['module'] for r in registry['suppliers']}) == expected_suppliers and
                all(r['must_not_recompile'] is True for r in registry['suppliers']), 'Original supplier inventory differs')
        for row in config['targets']:
            require(core.same(row['source'], owners[row['module']]['source']) and
                    row['project_imports'] == owners[row['module']]['project_imports'], 'Source contract differs')
        if kind == 'remaining8':
            importlib.import_module('scope_contract').validate_scope(config['targets'], registry['suppliers'], read(here / 'BOUNDARY.json'))
    for row in config['targets']:
        require(core.same(fp(here / row['audit_relative_path']), row['audit']), 'Original full-owned audit changed')
    graph = {r['module']: r['project_imports'] for r in [*registry['suppliers'], *config['targets']]}
    available = {r['module'] for r in registry['suppliers']}
    require(len(graph) == len(registry['suppliers']) + count, 'Target/supplier overlap')
    for row in config['targets']:
        require(set(row['project_imports']) <= available, 'Original target order changed')
        seen, active = set(), set()
        def visit(name):
            require(name in graph and name not in active, 'Missing/cyclic original dependency')
            if name in seen:
                return
            active.add(name)
            for dep in graph[name]:
                visit(dep)
            active.remove(name)
            seen.add(name)
        for dep in row['project_imports']:
            visit(dep)
        require(row['transitive_dependencies'] == sorted(seen), 'Original dependency closure differs')
        available.add(row['module'])
    return registry


def bind_context(kind, context, here, config, registry, joined, R, RC, V, guard):
    """All old bind/check_context obligations, with an explicitly separate physical witness."""
    stage = Path(context['stage'])
    expected_schema = {'prefix13': 'cell05_connections14_context_v1', 'shape1': 'cell05_shape_repair_context_v1',
                       'remaining8': 'cell05_remaining9_context_v1'}[kind]
    require(context['schema'] == expected_schema and here == stage / R.TOOL_REL, 'Original context location/schema differs')
    require(context['targets'] == config['targets'] and context['suppliers'] == registry['suppliers'], 'Original context inventory differs')
    original = joined['fields_context']
    for key in ('runtime', 'mathlib', 'mathlib_objects', 'mathlib_dependency_parent', 'mathlib_package_object_roots'):
        require(context[key] == original[key], 'Original context runtime changed: ' + key)
    env = dict(original['environment'])
    roots = [context['objects'], *context['mathlib_package_object_roots'], context['mathlib_objects']]
    env['LEAN_PATH'] = os.pathsep.join(roots)
    require(context['environment'] == env and context['cwd'] == str(stage / 'project') and
            context['objects'] == str(stage / 'objects'), 'Original context environment/cwd differs')
    require(env['LEAN_NUM_THREADS'] == env['OMP_NUM_THREADS'] == '1' and
            env['LEAN_SYSROOT'] == str(Path(context['runtime']['lean_binary']['path']).parent.parent), 'Original thread/sysroot differs')
    for root in roots:
        core.canonical(root)
    for root in roots[1:]:
        require(not (Path(root) / 'ImbalancedChen').exists(), 'Fallback project namespace appeared')
    project, objects = Path(context['supplier_project']), Path(context['supplier_objects'])
    require(str(project) == joined['supplier_project'] and str(objects) == joined['supplier_objects'], 'Supplier provider moved')
    for a, b in ((stage, project), (stage, objects), (project, objects)):
        R.disjoint(a, b)
    expected_join = joined['supplier_join'] if kind == 'shape1' else fp(here / 'SUPPLIER_JOIN.json')
    require(context['supplier_join'] == expected_join and context['runtime_guard'] == joined['runtime_guard'] == A['original_guard'],
            'Original join or guard reference changed')
    require(context['frozen_inputs'] == V.frozen_expected_paths(stage, here, config, registry, project, objects, joined),
            'Original frozen input inventory is incomplete or changed')
    refs(context['frozen_inputs'])
    require(context['runtime_guard'] in context['frozen_inputs'] and context['supplier_join'] in context['frozen_inputs'],
            'Original guard/join is not frozen')
    join = checked(context['supplier_join'])
    require(join['runtime_guard'] == A['original_guard'], 'Original join guard changed')
    if kind == 'shape1':
        B = importlib.import_module('boundary')
        importlib.import_module('origin_join').require_separate_stage(stage, joined)
        R.require_single_scope(context)
        require(context['origin_stage'] == B.BOUNDARY['original_stage'] and
                context['original_thirteen_owner_proof_commands'] == 0, 'Original isolated Shape scope differs')
    require(context['old_supplier_proof_commands'] == 0 and context['cloud_source_generation'] is False and
            context['full_supplier_kernel_closed_in_combined_evidence'] is True, 'Original proof scope differs')
    parent = Path(context['mathlib_dependency_parent'])
    package_roots = [str(parent / n / '.lake/build/lib/lean') for n in V.PACKAGES]
    cli = parent / 'Cli/.lake/build/lib/lean'
    if cli.exists():
        package_roots.append(str(cli))
    require(context['mathlib_package_object_roots'] == package_roots and
            context['mathlib_objects'] == str(Path(context['mathlib']) / '.lake/build/lib/lean'), 'Package root inventory differs')
    for key in ('lean_binary', 'leanchecker_binary'):
        require(core.same(context['runtime'][key], registry['runtime_binaries'][key]), 'Unaccepted runtime binary')
    require(0 < context['rss_limit_bytes'] <= 12*1024**3 and context['rss_limit_bytes'] % 1024**3 == 0 and
            context['wall_limit_seconds'] > 0, 'Original resource limit differs')
    R.namespace_files(stage, [r['module'] for r in [*context['suppliers'], *context['targets']]])
    R.tree_files(stage / 'project', {r['module'].replace('.', '/') + '.lean'
                                   for r in [*context['suppliers'], *context['targets']]})
    R.tree_files(stage / 'sources', {r['module'].replace('.', '/') + '.lean' for r in context['targets']})
    current_runtime(RC, context, guard)


def failed_normal(R, context, run_path, stopped):
    module = context['targets'][-1]['module']
    folder = run_path.parent / module.split('.')[-1]
    result_path, command_path = folder / 'normal-result.json', folder / 'normal-command.json'
    result = checked(stopped['failed_result'], result_path)
    command = checked(result['command'], command_path)
    family = context['schema'].removesuffix('_context_v1')
    require(result['schema'] == family + '_step_result_v1' and command['schema'] == family + '_step_command_v1', 'Failure schema differs')
    require(result['status'] == 'failed' and result['exit_code'] == 1 and result['termination_reason'] is None and
            'validation_error' not in result, 'Original failure disposition differs')
    paths = R.target_paths(context, module)
    source, deps = fp(paths['source']), R.dependency_objects(context, module)
    require(core.same(source, context['targets'][-1]['source']), 'Original failed source changed')
    for value in (command, result):
        require(value['module'] == module and value['mode'] == 'normal' and value['run'] == fp(run_path) and
                value['source'] == source and value['audit_source'] is None and value['dependency_objects'] == deps,
                'Original failed command/source/dependency link differs')
    require(command['argv'] == R.expected_argv(context, module, 'normal') and command['cwd'] == context['cwd'] and
            command['environment'] == context['environment'], 'Original failed command context differs')
    require(command['object_before'] is None and result['object'] is None and not paths['object'].exists(), 'Original failed object appeared')
    require(result['log'] == fp(folder / 'normal.log') and
            {p.name for p in R.tree_files(folder)} == {'normal-command.json', 'normal-result.json', 'normal.log'},
            'Original failure artifacts changed')
    return {'result': fp(result_path), 'command': fp(command_path), 'log': fp(folder / 'normal.log'),
            'source': source, 'module': module, 'mode': 'normal', 'status': 'failed', 'exit_code': 1,
            'accepted': False, 'object': None}


def prefix(kind, spec, context, R):
    stage = Path(spec['stage'])
    pilot_name, complete_name, n = ('ready14-pilot-v1', 'ready14-complete-v1', 13) if kind == 'prefix13' else (
        A['remaining9']['pilot'], A['remaining9']['continuation'], 8)
    require({p.name for p in (stage / 'verification').iterdir()} == {pilot_name, complete_name}, 'Unexpected historical attempt')
    require(not any((stage / 'verification' / name / 'SUCCESS.json').exists() for name in (pilot_name, complete_name)),
            'Original failed batch must not acquire a full SUCCESS')
    run_path = stage / 'verification' / complete_name / 'RUN.json'
    stopped = read(run_path.with_name('STOPPED.json'))
    run = checked(stopped['run'], run_path)
    pilot_path = stage / 'verification' / pilot_name / 'STOPPED.json'
    pilot = read(pilot_path)
    pilot_run = checked(pilot['run'], pilot_path.with_name('RUN.json'))
    schema = context['schema'].replace('_context_', '_run_')
    require(run['schema'] == pilot_run['schema'] == schema and run['attempt'] == complete_name and
            pilot_run['attempt'] == pilot_name and run['context'] == pilot_run['context'] == context, 'Original attempt/context differs')
    modules = [r['module'] for r in context['targets']]
    R.reject_missing_successful_objects(stage, modules)
    reusable = {(m, mode): R.prior(context, m, mode) for m in modules for mode in R.MODES}
    require(R.require_accepted_prefix(context, reusable) == 3*n, 'Original accepted prefix is incomplete')
    steps, objects = core.check_prefix_index(context, pilot, stopped, reusable, n, pilot_name, complete_name)
    failure = failed_normal(R, context, run_path, stopped)
    if kind == 'prefix13':
        P = importlib.import_module('prefix_validator')
        require(P.check_indexes(context, reusable, pilot, stopped) == (steps, objects), 'Original prefix index validator disagrees')
        require(P.check_failed_normal(R, context, run_path, stopped) == failure, 'Original failure validator disagrees')
        require(fp(pilot_path) == spec['pilot_index'] and fp(run_path.with_name('STOPPED.json')) == spec['failed_index'] and
                stopped['records'] == spec['records'] and objects == spec['object_pins'], 'Anchored original prefix differs')
    return {'steps': steps, 'objects': objects, 'failure': failure, 'records': stopped['records'],
            'pilot_index': fp(pilot_path), 'failed_index': fp(run_path.with_name('STOPPED.json')),
            'accepted_steps': 3*n, 'accepted_targets': n, 'context': context}


def shape_success(spec, context, R):
    success = checked(spec['success'])
    run = checked(spec['run'])
    require(success['run'] == spec['run'] and run['schema'] == 'cell05_shape_repair_run_v1' and
            success['schema'] == 'cell05_shape_repair_success_v1' and success['status'] == 'succeeded' and
            success['context'] == run['context'] == context and success['records'] == spec['records'], 'Original Shape SUCCESS differs')
    root = Path(context['stage']) / 'verification' / run['attempt']
    require(spec['success']['path'] == str(root / 'SUCCESS.json') and spec['run']['path'] == str(root / 'RUN.json'), 'Original Shape attempt path differs')
    require({p.name for p in root.parent.iterdir()} == {run['attempt']}, 'Unexpected original Shape attempt')
    module = context['targets'][0]['module']
    require([(r['module'], r['mode']) for r in success['records']] == [(module, m) for m in R.MODES], 'Shape three-check order differs')
    R.reject_missing_successful_objects(Path(context['stage']), [module])
    steps = [R.validate_step(row['accepted'], context, module, row['mode'], check_inputs=False) for row in success['records']]
    objects = {}
    for row, item in zip(success['records'], steps):
        require(row['disposition'] == 'executed' and Path(row['accepted']['path']).parent.parent == root, 'Shape reuse/attempt differs')
        obj = item['result']['object']
        require(objects.setdefault(module, obj) == obj, 'Shape steps differ in object bytes')
    require(success['accepted_targets'] == 1 and success['accepted_steps'] == success['newly_executed_steps'] == 3 and
            success['reused_steps'] == 0 and success['frozen_inputs_unchanged'] is True and
            success['whole_geometry_decoded'] is False and success['P2_6_complete'] is False and
            success['original_thirteen_owners_reexecuted'] is False, 'Original Shape success scope differs')
    return {'steps': steps, 'objects': objects, 'records': success['records'], 'success': spec['success'],
            'accepted_steps': 3, 'accepted_targets': 1, 'context': context}


def probe_result(kind, spec, context, joined, state):
    targets = context['targets'][:state['accepted_targets']]
    suppliers = []
    for row in targets:
        p = Path(context['cwd']) / (row['module'].replace('.', '/') + '.lean')
        require(core.same(fp(p), row['source']), 'Accepted original source changed')
        obj = state['objects'][row['module']]
        require(fp(obj['path']) == obj, 'Accepted original object changed')
        suppliers.append({'module': row['module'], 'source': row['source'], 'object': {k: obj[k] for k in ('bytes', 'sha256')},
                          'project_imports': row['project_imports'], 'source_path': str(p), 'object_path': obj['path']})
    require(targets == spec['target_contracts'], 'Anchored original target contracts differ')
    before = [spec['verifier'], *spec['anchors']]
    frozen = refs([*before, *context['frozen_inputs'], *joined['frozen_evidence']])
    return {'schema': 'p26_recovery_original_raw_probe_v1', 'status': 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY',
            'kind': kind, 'stage': spec['stage'], 'supplier_count': len(suppliers),
            'accepted_steps_rechecked': state['accepted_steps'], 'suppliers': suppliers, 'records': state['records'],
            'runtime_guard': A['original_guard'], 'fields_context': joined['fields_context'], 'frozen_evidence': frozen,
            'old_Lean_commands_executed': 0, 'original_evidence_rewritten': False}


def join_remaining(here, boundary, payload):
    J = importlib.import_module('join117')
    S = importlib.import_module('supplier_join')
    SC = importlib.import_module('scope_contract')
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    require(J.load_boundary(here) == (boundary, registry), 'Original117 boundary differs')
    old = Path(boundary['supplier88_root'])
    capsule = boundary['rows_receive']['capsule']
    data = S.joined_inputs(here / 'original103', Path(capsule['path']), old / 'project', old / 'objects', capsule)
    received = J.check_received(boundary, data['row_files'])
    prefix_probe, shape_probe = payload['prefix13']['probe'], payload['shape1']['probe']
    for label, probe, count, steps in [('prefix13', prefix_probe, 13, 39), ('shape1', shape_probe, 1, 3)]:
        spec = boundary['origins'][label]
        require(probe['schema'] == 'p26_recovery_original_raw_probe_v1' and
                probe['status'] == 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY' and probe['kind'] == label and
                probe['stage'] == spec['stage'] and probe['supplier_count'] == len(probe['suppliers']) == count and
                probe['accepted_steps_rechecked'] == steps and probe['records'] == spec['records'] and
                probe['runtime_guard'] == A['original_guard'] and probe['old_Lean_commands_executed'] == 0 and
                probe['original_evidence_rewritten'] is False, 'Invalid recovered original probe')
        SC.validate_origin_paths(probe['suppliers'], probe['stage'])
        refs(probe['frozen_evidence'])
    require(prefix_probe['fields_context'] == shape_probe['fields_context'] == data['fields_context'], 'Original context join disagrees')
    SC.validate_origin_groups(registry['suppliers'], data['registry']['suppliers'], prefix_probe['suppliers'], shape_probe['suppliers'])
    guard = checked(A['original_guard'])
    require(guard['snapshot'] == data['runtime_summaries']['P2']['output'] and
            guard['logical_roots'] == J.logical_roots(data['runtime_summaries']['P2']), 'Original guard linkage differs')
    original = here / 'original103'
    metadata = [fp(original / n) for n in ('SUPPLIER_PLAN.json', 'SUPPLIER_REGISTRY.json', 'RUNTIME_COMPATIBILITY_PINS.json')]
    metadata += [fp(original / r['relative_path']) for r in data['plan']['metadata_files']]
    metadata += [fp(original / r['relative_path']) for r in read(original / 'RUNTIME_COMPATIBILITY_PINS.json')['files']]
    frozen = refs([*received, *data['baseline_files'], data['fields_spec']['archive'], A['original_guard'],
                   data['runtime_summaries']['P2']['output'], *metadata, *prefix_probe['frozen_evidence'], *shape_probe['frozen_evidence']])
    J.validate_locations(here, J.PROVIDER, boundary)
    entries = J.selected_entries(here, boundary, registry, data, prefix_probe, shape_probe)
    docs, expected = J.documents(here, J.PROVIDER, boundary, registry, data, prefix_probe, shape_probe, received)
    require(read(here / 'SUPPLIER_JOIN.json') == expected, 'Original117 join document differs')
    J.preflight_documents(J.PROVIDER, docs, True)
    J.install_provider(J.PROVIDER, entries, J.protected_roots(boundary, data), completed=True)
    # Pure constructor: the original high-level validate_join is deliberately not called.
    joined = J.report(here, boundary, registry, data, frozen, docs)
    joined['status'] = 'RECOVERY_REBUILT_ORIGINAL117_RELATIONSHIPS'
    return joined


def snapshot_namespace(root, R):
    return core.namespace_snapshot(root)


def exact_verification_files(kind, context, state, R):
    """No extra failed or unindexed command can hide beside the accepted chains."""
    stage = Path(context['stage'])
    expected = {Path(p) for step in state['steps'] for p in step['evidence_files']}
    if kind != 'shape1':
        expected.update(Path(state['failure'][key]['path']) for key in ('command', 'result', 'log'))
    wanted = []
    for row in context['suppliers']:
        rel = row['module'].replace('.', '/')
        for key, suffix, provider, destination in [('source', '.lean', context['supplier_project'], context['cwd']),
                                                  ('object', '.olean', context['supplier_objects'], context['objects'])]:
            wanted.append({'module': row['module'], 'kind': key,
                           'source': fp(Path(provider) / (rel + suffix)),
                           'installed': fp(Path(destination) / (rel + suffix))})
    for row in context['targets']:
        rel = row['module'].replace('.', '/') + '.lean'
        wanted.append({'module': row['module'], 'kind': 'new_source',
                       'source': fp(stage / 'sources' / rel), 'installed': fp(stage / 'project' / rel)})
    for attempt in (stage / 'verification').iterdir():
        expected.update({attempt / 'RUN.json', attempt / 'SUPPLIER_REUSE.json',
                         attempt / ('SUCCESS.json' if kind == 'shape1' else 'STOPPED.json')})
        reused = read(attempt / 'SUPPLIER_REUSE.json')
        require(reused['old_supplier_proof_commands'] == 0 and
                reused['single_project_object_root'] == context['objects'] and
                [{k: v for k, v in row.items() if k != 'method'} for row in reused['entries']] == wanted and
                all(row['method'] in ('existing_identical', 'hardlink') for row in reused['entries']),
                'Original supplier installation record differs')
        joined = reused['joined']
        require(joined['runtime_guard'] == context['runtime_guard'] and
                joined['supplier_project'] == context['supplier_project'] and
                joined['supplier_objects'] == context['supplier_objects'] and
                joined['supplier_count'] == len(context['suppliers']) and
                joined['old_Lean_commands_executed'] == joined['compatibility_kernel_replays'] == 0 and
                joined['full_supplier_kernel_closed_in_combined_evidence'] is True,
                'Original supplier reuse scope differs')
    actual = R.verification_files(stage, [r['module'] for r in context['targets']])
    require(set(actual) == expected, 'Extra, missing or unindexed historical verification file')
    return actual


def main():
    kind = sys.argv[1]
    require(kind in ('runtime', 'prefix13', 'shape1', 'remaining8', 'verify'), 'Unknown fixed recovery worker')
    payload = json.load(sys.stdin) if kind != 'runtime' else {}
    nh, boundary, spec, here, config, R, RC, V, finder, authenticated = prepare(kind)
    if kind == 'runtime':
        result = runtime_capture(nh, RC)
        finder.check_loaded()
        print(json.dumps(result, separators=(',', ':')))
        return
    guard = payload['current_guard']
    locks = []
    for origin in sorted({spec['stage'], A['remaining9']['stage'], *[s['stage'] for s in boundary['origins'].values()]}):
        p = core.canonical(str(Path(origin) / 'EXECUTION.lock'))
        stream = p.open('rb')
        fcntl.flock(stream.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        locks.append(stream)
    if kind == 'verify':
        history = payload['history']
        current_runtime(RC, history['families']['remaining8']['original_context'], guard)
        refs(history['frozen_inputs'])
        for row in history['namespaces']:
            require(core.namespace_snapshot(row['root']) == row, 'Historical namespace changed: ' + row['root'])
        old_failure = None
        try:
            RC.check_runtime_guard_value(checked(A['original_guard']))
        except (ValueError, FileNotFoundError) as error:
            old_failure = {'type': type(error).__name__, 'message': str(error)}
        require(old_failure is not None, 'Original physical guard is no longer the recorded failure')
        current_runtime(RC, history['families']['remaining8']['original_context'], guard)
        finder.check_loaded()
        print(json.dumps({'schema': 'p26_runtime_recovery_current_check_v1', 'status': 'PASS_CURRENT_BINDINGS',
                          'original_live_guard_validator_passed': False, 'old_Lean_commands': 0}, separators=(',', ':')))
        return
    anchors = refs([spec['verifier'], *spec.get('anchors', [])])
    extra_frozen = []
    if kind in ('prefix13', 'shape1'):
        original = Path(boundary['origins']['prefix13']['stage'])
        original_here = original / boundary['origins']['prefix13']['tool_relative_path']
        _, original_config, _, original_files = core.authenticate_family(boundary['origins']['prefix13'])
        joined = fields_join(original_here, R)
        if kind == 'shape1':
            B = importlib.import_module('boundary').BOUNDARY
            require(original == Path(B['original_stage']) and core.same(fp(original / 'PACKAGE_CONTENTS.json'), B['original_package_manifest']) and
                    core.same(fp(original_here / 'CONNECTIONS14_VERIFIER.json'), B['original_verifier']) and
                    len(original_config['targets']) == 14 and original_config['targets'][-1] == B['original_target'],
                    'Original Shape repair provenance differs')
            frozen = [fp(original / 'PACKAGE_CONTENTS.json'), fp(original_here / 'CONNECTIONS14_VERIFIER.json')]
            for row in original_config['workflow_files']:
                frozen.append(fp(original_here / row['relative_path']))
            for row in original_config['targets']:
                rel = row['module'].replace('.', '/') + '.lean'
                for folder in ('sources', 'project'):
                    require(core.same(fp(original / folder / rel), row['source']), 'Original failed-stage source changed')
                    frozen.append(fp(original / folder / rel))
            require(joined['runtime_guard'] == B['runtime_guard'] and
                    joined['supplier_project'] == B['supplier_project'] and joined['supplier_objects'] == B['supplier_objects'],
                    'Original Shape supplier origin changed')
            require(joined['fields_context']['stage'] == B['original_fields_stage'], 'Original Shape fields stage differs')
            require(set(B['expected_old_dependency_modules']) <= {r['module'] for r in joined['registry']['suppliers']} and
                    B['original_target']['module'] not in {r['module'] for r in joined['registry']['suppliers']},
                    'Original Shape dependency boundary differs')
            joined.update(origin_stage=str(original), supplier_join=fp(original_here / 'SUPPLIER_JOIN.json'),
                          actual_repair_supplier_union=42, frozen_evidence=[*joined['frozen_evidence'], *frozen])
            context = checked(spec['run'])['context']
            extra_frozen = package_check(Path(spec['stage']) / 'PACKAGE_CONTENTS.json', A['shape_package'], kind, config, spec)
        else:
            context = checked(checked(spec['failed_index'])['run'])['context']
            # The original Shape boundary independently fixes this source package manifest.
            shape_spec = boundary['origins']['shape1']
            bound_pin = next(r for r in shape_spec['anchors'] if r['path'].endswith('/BOUNDARY.json'))
            B = checked(bound_pin)
            extra_frozen = package_check(original / 'PACKAGE_CONTENTS.json',
                {'path': str(original / 'PACKAGE_CONTENTS.json'), **B['original_package_manifest']}, kind, config, spec)
        authenticated += original_files
    else:
        joined = join_remaining(here, boundary, payload)
        extra_frozen = package_check(Path(spec['stage']) / 'PACKAGE_CONTENTS.json', spec['package'], kind, config, spec)
        context = checked(next(r for r in spec['anchors'] if r['path'].endswith('/' + spec['continuation'] + '/RUN.json')))['context']
    registry = configuration(kind, here, config, R, joined)
    bind_context(kind, context, here, config, registry, joined, R, RC, V, guard)
    state = shape_success(spec, context, R) if kind == 'shape1' else prefix(kind, spec, context, R)
    stage = Path(context['stage'])
    all_modules = [r['module'] for r in [*context['suppliers'], *context['targets']]]
    raw_paths = exact_verification_files(kind, context, state, R)
    raw_paths += R.namespace_files(stage, all_modules)
    frozen = refs([*anchors, *authenticated, *extra_frozen, *context['frozen_inputs'], *joined['frozen_evidence'],
                   *[fp(p) for p in raw_paths]])
    namespace_roots = {stage / name for name in ('sources', 'project', 'objects', 'verification')}
    namespace_roots |= {Path(joined['supplier_project']), Path(joined['supplier_objects'])}
    namespaces = [snapshot_namespace(path, R) for path in sorted(namespace_roots)]
    result = {'schema': 'p26_preserved_family_recovery_v1', 'kind': kind,
              'status': 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY',
              'original_live_guard_validator_passed': False, 'original_context': context,
              'state': {k: v for k, v in state.items() if k not in ('steps', 'context')},
              'owned_declaration_count': sum(s['result']['owned_declaration_count'] for s in state['steps'] if s['result']['mode'] == 'owned'),
              'frozen_inputs': frozen, 'namespaces': namespaces, 'old_Lean_commands': 0,
              'original_evidence_rewritten': False, 'P2_6_complete': False}
    if kind in ('prefix13', 'shape1'):
        result['probe'] = probe_result(kind, spec, context, joined, state)
    else:
        target = context['targets'][-1]
        suppliers = [dict(row) for row in context['suppliers']]
        for row in context['targets'][:8]:
            obj = state['objects'][row['module']]
            suppliers.append({'module': row['module'], 'source': row['source'],
                              'object': {k: obj[k] for k in ('bytes', 'sha256')}, 'project_imports': row['project_imports'],
                              'must_not_recompile': True, 'reuse_group': 'remaining8'})
        require(target['module'] == A['target'] and len(suppliers) == len({r['module'] for r in suppliers}) == 125 and
                set(target['transitive_dependencies']) == {r['module'] for r in suppliers}, 'Exact125 dependency boundary differs')
        for row in suppliers:
            rel = row['module'].replace('.', '/')
            row['source_path'], row['object_path'] = str(stage / 'project' / (rel + '.lean')), str(stage / 'objects' / (rel + '.olean'))
            require(core.same(fp(row['source_path']), row['source']) and core.same(fp(row['object_path']), row['object']), 'Current supplier differs')
        result.update(target=target, suppliers=suppliers)
    require(result['owned_declaration_count'] == {'prefix13': 112, 'shape1': 28, 'remaining8': 116}[kind], 'Original owned count differs')
    current_runtime(RC, context, guard)
    refs(frozen)
    finder.check_loaded()
    print(json.dumps(result, separators=(',', ':')))


if __name__ == '__main__':
    main()
