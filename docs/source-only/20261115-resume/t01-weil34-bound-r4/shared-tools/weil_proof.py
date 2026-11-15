"""Execute/bind the actual34 compiler, kernel and full declaration proof gates."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

from coherent_cache import checked, read, require, sha, write
from weil_cache import WeilSession, normalized_argv, physical
from weil_inputs import source_closure
from weil_scope import data, installed


def flatten(table):
    return [p for groups in table.values() for group in groups for p in group]


def canonical_path(session, value):
    p = Path(value)
    if not p.is_absolute(): p = session.project/p
    require(p.resolve().is_relative_to(session.project)
            or p.resolve().is_relative_to(Path(session.state['realbin']).parent), 'Import/library path escaped selected roots')
    return p


def setup_value(session, name, standard):
    rows = {r['module']:r for r in data()['source_rows']}
    required = set()
    def visit(module):
        if module in required: return
        required.add(module)
        for imp in rows[module]['imports']:
            if imp in rows: visit(imp)
    if name == 'T01Audit': required = set(rows)
    else:
        visit(name); required.remove(name)
    # Exact stock-produced full setups remain evidence. The new source setup
    # below is explicitly caller-produced from their resolved artifacts.
    table = {n:[[str(canonical_path(session, p)) for p in group] for group in groups]
             for n, groups in standard['importArts'].items()}
    for module in sorted(required):
        table[module] = session.artifacts(module, all_private=name == 'T01Audit')
    if name == 'T01Audit':
        # The legacy exporter loads all private data. No public/private union
        # substitutes for selected mainModule data or canonical ownership.
        for module in table:
            table[module] = session.artifacts(module, all_private=True)
    libraries = {'dynlibs':[], 'plugins':[]}
    for setup in standard['setups'].values():
        for field in libraries:
            for value in setup[field]:
                if isinstance(value, str): item = str(canonical_path(session, value))
                else: item = dict(value, path=str(canonical_path(session, value['path'])))
                if item not in libraries[field]: libraries[field].append(item)
    setup = dict(name=name, package='imbalancedChen', isModule=name != 'T01Audit',
                 imports=None, importArts=table, options={}, **libraries)
    path = session.project/'.lake/build/ir'/Path(*name.split('.')).with_suffix('.setup.json')
    files = {}
    for value in flatten(table): files[value] = physical(value)
    for field in libraries:
        for value in libraries[field]:
            p = value if isinstance(value, str) else value['path']
            files[p] = physical(p)
    # Every possible source-private fallback part is pre-bound too; a name
    # missing from the table can never silently become an accepted import.
    closure = source_closure(session, [*data()['compile_order'], 'Lean.Util.FoldConsts']) if name == 'T01Audit' else standard['source_private_closure']
    for record in closure.values():
        identity = record['identity']
        for part in [identity['source'], *identity['facets']]: files[part['path']] = part
    for module in sorted(required):
        identity = session.locate(module)
        for part in [identity['source'], *identity['facets']]: files[part['path']] = part
    return setup, path, files


def setup_for(session, name, standard):
    setup, path, files = setup_value(session, name, standard)
    write(path, setup)
    files[str(path)] = physical(path)
    source = session.project/Path(*name.split('.')).with_suffix('.lean')
    input_path = session.logs/'direct-inputs'/(name+'.json')
    receipt = dict(binding=session.binding, source=physical(source), normalized_argv=normalized_argv(name, session.project),
                   setup=setup, setup_path=str(path), files=list(files.values()),
                   setup_origin='EXPLICIT_NEW_CALLER_SETUP_NOT_A_LAKE_TRACE_OR_HISTORICAL_SETUP',
                   stock_inputs_sha256=sha(session.logs/'WEIL_STANDARD_INPUTS.json'),
                   imports_override_is_null=True, options_are_empty_profile_args_are_explicit=True)
    write(input_path, receipt)
    return input_path


def validate_direct_input(session, name, standard):
    path = session.logs/'direct-inputs'/(name+'.json')
    receipt = read(path)
    setup, setup_path, files = setup_value(session, name, standard)
    require(read(setup_path) == setup, 'Actual complete source-header-preserving ModuleSetup changed')
    files[str(setup_path)] = physical(setup_path)
    source = session.project/Path(*name.split('.')).with_suffix('.lean')
    expected = dict(binding=session.binding, source=physical(source), normalized_argv=normalized_argv(name, session.project),
        setup=setup, setup_path=str(setup_path), files=list(files.values()),
        setup_origin='EXPLICIT_NEW_CALLER_SETUP_NOT_A_LAKE_TRACE_OR_HISTORICAL_SETUP',
        stock_inputs_sha256=sha(session.logs/'WEIL_STANDARD_INPUTS.json'),
        imports_override_is_null=True, options_are_empty_profile_args_are_explicit=True)
    require(receipt == expected, 'Original direct source/setup/complete physical closure receipt changed')
    events = [json.loads(line) for line in (session.logs/'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines() if line.strip()]
    matches = [event for event in events if event['tool'] == 'lean' and event['argv'] == normalized_argv(name, session.project)]
    require(len(matches) == 1 and matches[0]['physical_inputs'] == [receipt['source'], physical(path)],
            'Original complete input receipt is not bound to the actual preexec event')
    return receipt, matches[0]


def source_compile(session, name, standard):
    session.qualification_inputs(); installed()
    if name != 'T01Audit':
        stem = session.project/'.lake/build/lib/lean'/Path(*name.split('.'))
        require(not any(Path(str(stem)+suffix).exists() for suffix in
                        ['.olean', '.olean.server', '.olean.private', '.ilean', '.ir.sig', '.ir']),
                'An exact-profile output already exists; source compilation would duplicate it')
        stem.parent.mkdir(parents=True, exist_ok=True)
    path = setup_for(session, name, standard)
    before = sha(path)
    argv = ['lake', '--no-build', 'env', 'lean', *normalized_argv(name, session.project)[3:]]
    result = session.run('weil-compile-'+name, argv)
    require(sha(path) == before, 'Prepared input binding changed during compiler execution')
    receipt = read(path)
    for row in receipt['files']: checked(row['path'], row)
    events = [json.loads(line) for line in (session.logs/'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines() if line.strip()]
    matches = [e for e in events if e['tool'] == 'lean' and e['argv'] == normalized_argv(name, session.project)]
    require(len(matches) == 1 and matches[0]['physical_inputs'] == [receipt['source'], physical(path)],
            'Actual compiler process lacks exact source/setup/import admission evidence')
    output = None if name == 'T01Audit' else session.locate(name)
    session.emit('direct-results/'+name+'.json', dict(name=name, process=result, input_binding_sha256=before,
                 input_binding=receipt, actual_preexec_event=matches[0], output_identity=output))


def compile_all():
    session = WeilSession(); standard = session.qualification_inputs()
    from qualified_direct import protected_modules,validate
    for name in data()['compile_order']:
        if name in protected_modules(): validate(session,standard)
        else: source_compile(session,name,standard)
    session.emit('WEIL_OBJECTS_BEFORE_AUDIT.json', dict(identities={name:session.locate(name) for name in data()['compile_order']},
                 compile_census=session.compile_census(True)))


def check_outputs(session):
    installed()
    standard = session.qualification_inputs()
    before = session.receipt('WEIL_OBJECTS_BEFORE_AUDIT.json')
    require(before['identities'] == {name:session.locate(name) for name in data()['compile_order']},
            'Actual34 source/public/server/private/IR objects changed during proof gates')
    from qualified_direct import protected_modules,validate
    for name in data()['compile_order']:
        if name in protected_modules():
            protected = validate(session,standard)['modules'][name]
            require(before['identities'][name]['facets'] == [*protected['current_five_facets'],protected['current_additional_ilean']],
                    'Protected actual six outputs changed')
            continue
        row = session.receipt('direct-results/'+name+'.json')
        receipt_path = session.logs/'direct-inputs'/(name+'.json')
        require(row['input_binding_sha256'] == sha(receipt_path) and row['input_binding'] == read(receipt_path)
                and row['output_identity'] == before['identities'][name], 'Exact direct compile receipt/output changed')
        expected_input, actual_event = validate_direct_input(session, name, standard)
        require(row['input_binding'] == expected_input and row['actual_preexec_event'] == actual_event, 'Original actual direct input/event record changed')
        for item in row['input_binding']['files']: checked(item['path'], item)
        process_receipt(session, row['process'], 'weil-compile-'+name,
                        ['lake', '--no-build', 'env', 'lean', *normalized_argv(name, session.project)[3:]])
    return before


def process_receipt(session, p, label, argv):
    require(p['argv'] == argv and p['cwd'] == str(session.project) and p['exit_code'] == 0
            and p['stdout'] == str(session.logs/'cache-processes'/(label+'.stdout'))
            and p['stderr'] == str(session.logs/'cache-processes'/(label+'.stderr'))
            and read(session.logs/'cache-processes'/(label+'.json')) == dict(binding=session.binding, **p)
            and sha(p['stdout']) == p['stdout_sha256'] and sha(p['stderr']) == p['stderr_sha256'],
            'Actual process argv/cwd/exit/raw-output receipt differs: '+label)


def kernel():
    session = WeilSession(); session.qualification_inputs(); check_outputs(session)
    argv = ['lake', '--no-build', 'env', 'leanchecker', '--verbose', *data()['compile_order']]
    result = session.run('weil-kernel', argv)
    replay = [line.removeprefix('replaying ') for line in Path(result['stdout']).read_text(encoding='utf-8').splitlines()
              if line.startswith('replaying ')]
    require(Counter(replay) == Counter(data()['compile_order']), 'Actual exact34 most-private kernel replay scope differs')
    check_outputs(session)
    session.emit('WEIL_KERNEL_PROCESS.json', dict(process=result, replayed_modules=replay,
                 actual_modern_private_parts_mandatory=True, unsafe_partial_skipped_by_native_checker_credit=False))


def types():
    session = WeilSession(); standard = session.qualification_inputs(); check_outputs(session)
    source_compile(session, 'T01Audit', standard)
    check_outputs(session)


def validated_inventory(session, retain_available=False):
    standard = session.qualification_inputs(); objects = check_outputs(session)
    modules = data()['compile_order']; rows = {r['module']:r for r in data()['source_rows']}
    k = session.receipt('WEIL_KERNEL_PROCESS.json')
    process_receipt(session, k['process'], 'weil-kernel', ['lake', '--no-build', 'env', 'leanchecker', '--verbose', *modules])
    replay = [line.removeprefix('replaying ') for line in Path(k['process']['stdout']).read_text(encoding='utf-8').splitlines() if line.startswith('replaying ')]
    require(Counter(replay) == Counter(modules) and k['replayed_modules'] == replay
            and k['actual_modern_private_parts_mandatory'] is True
            and k['unsafe_partial_skipped_by_native_checker_credit'] is False, 'Original actual most-private kernel replay changed')
    audit = session.receipt('direct-results/T01Audit.json')
    process_receipt(session, audit['process'], 'weil-compile-T01Audit',
                    ['lake', '--no-build', 'env', 'lean', *normalized_argv('T01Audit', session.project)[3:]])
    require(audit['input_binding_sha256'] == sha(session.logs/'direct-inputs/T01Audit.json'), 'Actual audit input receipt changed')
    expected_input, actual_event = validate_direct_input(session, 'T01Audit', standard)
    require(audit['input_binding'] == expected_input and audit['actual_preexec_event'] == actual_event, 'Actual frozen auditor input/event changed')
    for item in audit['input_binding']['files']: checked(item['path'], item)
    lines = Path(audit['process']['stdout']).read_text(encoding='utf-8').splitlines()
    def records(prefix): return [json.loads(line[len(prefix):]) for line in lines if line.startswith(prefix)]
    declarations = records('P0_ROUND6_DECL ')
    inventory = records('P0_ROUND6_SERIALIZED ')
    counts = records('P0_ROUND6_MODULE ')
    # Retain raw parsed evidence even if a later semantic cross-check rejects it.
    if retain_available:
        session.emit('WEIL_AVAILABLE_INVENTORY.json', dict(declarations=declarations, serialized=inventory, module_counts=counts,
                     module_identities=objects['identities'], compiler_stdout_sha256=audit['process']['stdout_sha256'], acceptance=False))
    require(len(inventory) == len(counts) == 34
            and Counter(r['module'] for r in inventory) == Counter(modules)
            and Counter(r['module'] for r in counts) == Counter(modules), 'Exact34 complete module census differs')
    require(declarations and len({d['name'] for d in declarations}) == len(declarations), 'Empty/duplicate actual declaration inventory')
    for module in modules:
        names = [d['name'] for d in declarations if d['module'] == module]
        i = next(r for r in inventory if r['module'] == module)
        count = next(r['count'] for r in counts if r['module'] == module)
        require(names and Counter(names) == Counter(i['serialized_constant_names']) == Counter(i['environment_constant_names'])
                and len(names) == count == i['serialized_constant_count'] and i['is_module']
                and i['has_data'] and i['import_all'], 'Exact canonical-owner/modern-private multiset differs: '+module)
    loaded = records('WEIL34_LOADED_MODULE ')
    loaded_map = {r['module']:r for r in loaded}
    closure = source_closure(session, [*modules, 'Lean.Util.FoldConsts'])
    require(len(loaded) == len(loaded_map) and loaded and set(modules) <= set(loaded_map)
            and set(loaded_map) <= set(closure), 'Actual loaded module/fallback set escaped complete prebound source-private closure')
    require(set(closure) == set(standard['source_private_closure']) | set(modules), 'Auditor private source closure differs from prepared complete coverage')
    for module, record in loaded_map.items():
        require(record['has_data'] and record['import_all']
                and record['is_module'] == closure[module]['identity']['modern'],
                'Actual legacy-private loaded mode/hasData differs: '+module)
    logical, executable = [], []
    for d in declarations:
        require(d['module'] in rows and not d['is_axiom'] and set(d['axioms']) <= set(data()['allowed_axioms'])
                and d['axiom_audit'] == 'fresh_current_checked_type_and_body'
                and all(d[key].strip() and '\u22ef' not in d[key] for key in ['type', 'readable_type']), 'Owned two-type/direct-axiom audit failed')
        dependencies = d['dependency_records']; graph = {r['name']:r for r in dependencies}
        require(len(graph) == len(dependencies) == d['axiom_visited_count'] and d['name'] in graph, 'Truncated/duplicate fresh dependency inventory')
        visited, pending = set(), [d['name']]
        while pending:
            name = pending.pop()
            if name in visited: continue
            require(name in graph, 'Fresh direct dependency graph is not closed')
            visited.add(name); pending.extend(graph[name]['used_constants'])
        require(visited == set(graph) and set(d['axioms']) == {n for n, r in graph.items() if r['is_axiom']},
                'Fresh complete raw type/body/constructor/recursor closure differs')
        require(all(r['owner_module'] in loaded_map and r['owner_module'] in closure
                    and loaded_map[r['owner_module']]['has_data'] and loaded_map[r['owner_module']]['import_all']
                    for r in graph.values()), 'A raw type/body dependency owner lacks actual private-data/physical-source binding')
        unsafe = {n for n, r in graph.items() if r['is_unsafe'] or r['is_partial']}
        implementation = d['is_unsafe'] or d['is_partial']
        require(set(d['unsafe_partial_dependencies']) == unsafe
                and d['safety_class'] == ('executable_implementation' if implementation else 'logical_safe')
                and d['kernel_replay_required'] == (not implementation)
                and d['implementation_kernel_proof_credit'] is False
                and d['implementation_termination_credit'] is False, 'Actual flag classification/zero-credit policy differs')
        if implementation:
            require(d['kind'] in {'definition', 'opaque'}, 'Unknown unsafe/partial constructor kind: HOLD')
            executable.append(d)
        else:
            require(not unsafe, 'Safe logical declaration reaches unsafe/partial implementation')
            logical.append(d)
    terminals = [d for d in declarations if d['name'] in data()['required_terminals']]
    require(Counter(d['name'] for d in terminals) == Counter(data()['required_terminals'])
            and all(d['kind'] == 'theorem' and d['safety_class'] == 'logical_safe' for d in terminals), 'Actual safe terminal theorem absent')
    return dict(declarations=declarations, serialized=inventory, module_counts=counts,
        module_identities=objects['identities'], safe_logical_names=[d['name'] for d in logical],
        executable_implementation_metadata=executable, implementation_kernel_or_termination_credit=False,
        required_terminal_full_types=terminals, actual_kernel_process=k['process'], actual_types_process=audit['process'],
        loaded_modules=loaded, complete_source_private_closure=closure,
        complete_private_generated_owned_inventory=True, adapter_stage_B='HOLD', half_support_closed=False, full_J=False)


def verify():
    session = WeilSession()
    inventory = validated_inventory(session, retain_available=True)
    session.emit('WEIL_FULL_INVENTORY.json', inventory)


if __name__ == '__main__':
    phase = sys.argv[1]
    require(phase in {'compile_all', 'kernel', 'types', 'verify'}, 'Unknown actual proof phase')
    globals()[phase]()
