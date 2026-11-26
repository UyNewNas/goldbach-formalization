#!/usr/bin/env python3
"""Shared fail-closed path, resume-chain and export validators; never runs Lean."""
from pathlib import Path
import hashlib
import json
import os
import re
import stat
import sys

sys.dont_write_bytecode = True
from receipt_support import ALLOWED, parse_owned
from runtime_compat import check_runtime_guard

MODES = ('normal', 'kernel', 'owned')
TOOL_REL = Path('tools/p26/cell05-connections14-run-20261126')
ATTEMPT = re.compile(r'[A-Za-z0-9_-]+')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(path, must_exist=False):
    """Reject symlinks in every existing ancestor before resolving or writing."""
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, f'Absolute canonical path required: {path}')
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:]):
        current /= part
        try:
            info = current.lstat()
        except FileNotFoundError:
            require(not must_exist, f'Missing required path: {current}')
            continue
        require(not stat.S_ISLNK(info.st_mode), f'Symlink path rejected before write: {current}')
        if index < len(path.parts) - 2:
            require(stat.S_ISDIR(info.st_mode), f'Non-directory ancestor: {current}')
    return path


def fp(path):
    path = canonical(path, True)
    require(stat.S_ISREG(path.lstat().st_mode), f'Regular file required: {path}')
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(a.get(k) == b.get(k) for k in ('bytes', 'sha256'))


def read(path):
    canonical(path, True)
    return json.loads(Path(path).read_text())


def checked(identity, expected_path):
    require(isinstance(identity, dict) and identity.get('path') == str(expected_path),
            f'Receipt path does not name expected file: {expected_path}')
    require(identity == fp(expected_path), f'Fingerprint changed: {expected_path}')
    return read(expected_path)


def dump_new(path, value):
    path = canonical(path)
    canonical(path.parent)
    path.parent.mkdir(parents=True, exist_ok=True)
    canonical(path.parent, True)
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2) + '\n')


def disjoint(a, b):
    require(not (a == b or a.is_relative_to(b) or b.is_relative_to(a)),
            f'Roots must be disjoint in both directions: {a} / {b}')


def tree_files(root, allowed=None):
    root = canonical(root)
    if not root.exists():
        return []
    require(root.is_dir(), f'Directory required: {root}')
    paths = []
    pending = [root]
    while pending:
        parent = pending.pop()
        for path in sorted(parent.iterdir()):
            canonical(path, True)
            if path.is_dir():
                if allowed is not None:
                    rel = str(path.relative_to(root)) + '/'
                    require(any(name.startswith(rel) for name in allowed), f'Unexpected namespace directory: {path}')
                pending.append(path)
            else:
                require(path.is_file(), f'Unexpected special file: {path}')
                if allowed is not None:
                    require(str(path.relative_to(root)) in allowed, f'Unknown module or sidecar: {path}')
                paths.append(path)
    return paths


def namespace_files(stage, modules):
    allowed = {module.replace('.', '/') + '.olean' for module in modules}
    return tree_files(stage / 'objects', allowed)


def verification_files(stage, modules):
    root = stage / 'verification'
    short_names = {module.split('.')[-1] for module in modules}
    result = tree_files(root)
    names = {mode + suffix for mode in MODES for suffix in ('-command.json', '-result.json', '-accepted.json', '.log')}
    names.add('owned-declarations.json')
    for path in result:
        rel = path.relative_to(root).parts
        require(len(rel) in (2, 3) and ATTEMPT.fullmatch(rel[0]), f'Unexpected verification path: {path}')
        if len(rel) == 2:
            require(rel[1] in ('RUN.json', 'SUCCESS.json', 'STOPPED.json', 'SUPPLIER_REUSE.json'),
                    f'Unexpected attempt file: {path}')
        else:
            require(rel[1] in short_names and rel[2] in names, f'Unexpected step file: {path}')
    return result


def validate_layout(stage, here, supplier_project, supplier_objects, modules, targets, attempt):
    """Validate all writable roots and planned destinations before any mkdir/copy."""
    stage, here = canonical(stage, True), canonical(here, True)
    require(here == stage / TOOL_REL, 'Run the exact packaged driver under STAGE/tools/p26/cell05-connections14-run-20261126')
    supplier_project = canonical(supplier_project, True)
    supplier_objects = canonical(supplier_objects, True)
    disjoint(stage, supplier_project)
    disjoint(stage, supplier_objects)
    disjoint(supplier_project, supplier_objects)
    require(ATTEMPT.fullmatch(attempt), 'Invalid attempt name')
    for root in [stage / 'sources', stage / 'project', stage / 'objects', stage / 'verification', stage / 'exports']:
        canonical(root)
    disjoint(stage / 'sources', stage / 'project')
    all_sources = {module.replace('.', '/') + '.lean' for module in modules}
    tree_files(stage / 'project', all_sources)
    namespace_files(stage, modules)
    verification_files(stage, targets)
    run_root = stage / 'verification' / attempt
    require(not run_root.exists(), f'Attempt already exists; use a new attempt name: {run_root}')
    for name in ('RUN.json', 'SUCCESS.json', 'STOPPED.json', 'SUPPLIER_REUSE.json'):
        canonical(run_root / name)
    for module in modules:
        relative = Path(module.replace('.', '/'))
        canonical(stage / 'project' / relative.with_suffix('.lean'))
        canonical(stage / 'objects' / relative.with_suffix('.olean'))
    for module in targets:
        relative = Path(module.replace('.', '/'))
        canonical(stage / 'sources' / relative.with_suffix('.lean'), True)
        canonical(here / 'owned-audits' / (relative.name + '.lean'), True)
        folder = run_root / relative.name
        for mode in MODES:
            for suffix in ('-command.json', '-result.json', '-accepted.json', '.log'):
                canonical(folder / (mode + suffix))
        canonical(folder / 'owned-declarations.json')
    return stage


def indexed_seals(stage, modules):
    """Surviving SUCCESS/STOPPED indexes cannot hide a lost accepted receipt."""
    found = {}
    for name, status in [('SUCCESS.json', 'succeeded'), ('STOPPED.json', 'stopped')]:
        for path in sorted((stage / 'verification').glob('*/' + name)):
            index = read(path)
            require(index.get('status') == status, f'Invalid attempt index: {path}')
            run = checked(index['run'], path.with_name('RUN.json'))
            require(run.get('schema') == 'cell05_connections14_run_v1' and
                    run.get('attempt') == path.parent.name and run['context']['stage'] == str(stage),
                    f'Attempt index stage/schema mismatch: {path}')
            expected = [(module, mode) for module in modules for mode in MODES]
            records = index['records']
            require(len(records) <= len(expected) and
                    [(row.get('module'), row.get('mode')) for row in records] == expected[:len(records)],
                    f'Attempt acceptance index is not an ordered prefix: {path}')
            if name == 'SUCCESS.json':
                require(index.get('schema') == 'cell05_connections14_success_v1' and
                        index.get('accepted_steps') == len(records) == 42 and index.get('accepted_targets') == 14,
                        f'Incomplete successful-attempt index: {path}')
            for record in index['records']:
                module, mode = record['module'], record['mode']
                require(module in modules and mode in MODES, f'Unknown indexed acceptance: {path}')
                identity = record['accepted']
                seal_path = canonical(identity['path'], True)
                relative = seal_path.relative_to(stage / 'verification').parts
                require(len(relative) == 3 and ATTEMPT.fullmatch(relative[0])
                        and relative[1:] == (module.split('.')[-1], mode + '-accepted.json'),
                        f'Indexed acceptance path mismatch: {seal_path}')
                require(fp(seal_path) == identity, f'Indexed accepted receipt changed: {seal_path}')
                found[seal_path] = (module, mode)
    return found


def reject_missing_successful_objects(stage, modules):
    """Any surviving result, accepted seal or attempt index is a no-replay barrier."""
    files = verification_files(stage, modules)
    seals = indexed_seals(stage, modules)
    for path in files:
        if path.name.endswith('-command.json'):
            mode_name = path.name.removesuffix('-command.json')
            require(path.with_name(mode_name + '-result.json').exists(),
                    f'Interrupted command has no result; preserve evidence and recover without replay: {path}')
        if path.name.endswith('.log'):
            require(path.with_name(path.stem + '-result.json').exists(),
                    f'Surviving log has no result; preserve evidence and recover without replay: {path}')
        mode = next((m for m in MODES if path.name in (m + '-result.json', m + '-accepted.json')), None)
        if mode is None:
            continue
        module = 'ImbalancedChen.' + path.parent.name
        if path.name.endswith('-accepted.json'):
            seals[path] = (module, mode)
            continue
        result = read(path)
        require(module in modules and result.get('module') == module and result.get('mode') == mode,
                f'Result label/path mismatch: {path}')
        if result.get('status') == 'succeeded' or result.get('exit_code') == 0:
            require(result.get('status') == 'succeeded' and result.get('exit_code') == 0,
                    f'Contradictory prior successful result: {path}')
            obj = stage / 'objects' / (module.replace('.', '/') + '.olean')
            require(obj.exists(), f'Accepted object is missing; restore exact bytes, never recompile: {obj}')
            seal_path = path.with_name(mode + '-accepted.json')
            require(seal_path.exists(), f'Successful result lacks its acceptance seal: {path}')
            seals[seal_path] = (module, mode)
    for path, (module, mode) in seals.items():
        seal = read(path)
        obj = stage / 'objects' / (module.replace('.', '/') + '.olean')
        require(obj.exists(), f'Accepted object is missing; restore exact bytes, never recompile: {obj}')
        old_run = checked(seal['run'], path.parent.parent / 'RUN.json')
        require(old_run['context']['stage'] == str(stage), f'Accepted seal stage mismatch: {path}')
        validate_step(fp(path), old_run['context'], module, mode, check_inputs=False)


def target_paths(context, module):
    stage = Path(context['stage'])
    relative = Path(module.replace('.', '/'))
    return {'source': stage / 'project' / relative.with_suffix('.lean'),
            'object': stage / 'objects' / relative.with_suffix('.olean'),
            'audit': stage / TOOL_REL / 'owned-audits' / (relative.name + '.lean')}


def expected_argv(context, module, mode):
    paths = target_paths(context, module)
    lean = context['runtime']['lean_binary']['path']
    common = [lean, '-j1', f'-M{context["rss_limit_bytes"] // 1024**2}',
              '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        return common + ['-o', str(paths['object']), module.replace('.', '/') + '.lean']
    if mode == 'kernel':
        return [context['runtime']['leanchecker_binary']['path'], '--verbose', module]
    require(mode == 'owned', f'Unknown mode: {mode}')
    return common + [str(paths['audit'])]


def dependency_objects(context, module):
    target = next(row for row in context['targets'] if row['module'] == module)
    return {dep: fp(Path(context['stage']) / 'objects' / (dep.replace('.', '/') + '.olean'))
            for dep in target['transitive_dependencies']}


def check_context_inputs(context):
    require(sys.flags.optimize == 0, 'Inherited audit parser requires Python assertions enabled')
    stage = canonical(context['stage'], True)
    require(context['cwd'] == str(stage / 'project'), 'Context cwd is not the stage project')
    require(context['objects'] == str(stage / 'objects'), 'Context object root mismatch')
    expected_roots = [context['objects'], *context['mathlib_package_object_roots'], context['mathlib_objects']]
    require(context['environment']['LEAN_PATH'] == os.pathsep.join(expected_roots), 'Context LEAN_PATH mismatch')
    require(context['environment']['LEAN_NUM_THREADS'] == context['environment']['OMP_NUM_THREADS'] == '1',
            'Thread environment mismatch')
    require(context['environment']['LEAN_SYSROOT'] == str(Path(context['runtime']['lean_binary']['path']).parent.parent),
            'Toolchain sysroot mismatch')
    for root in expected_roots:
        canonical(root, True)
    for root in expected_roots[1:]:
        require(not (Path(root) / 'ImbalancedChen').exists(), f'Fallback project namespace: {root}')
    require(context['old_supplier_proof_commands'] == 0 and not context['cloud_source_generation'],
            'Unexpected proof generation scope')
    for identity in context['frozen_inputs']:
        require(identity == fp(identity['path']), f'Frozen context input changed: {identity["path"]}')
    require(context['runtime_guard'] in context['frozen_inputs'] and
            context['supplier_join'] in context['frozen_inputs'], 'Runtime guard/join missing from frozen inputs')
    join = checked(context['supplier_join'], stage / TOOL_REL / 'SUPPLIER_JOIN.json')
    require(join['runtime_guard'] == context['runtime_guard'], 'A different runtime guard cannot resume accepted steps')
    check_runtime_guard(context['runtime_guard'])
    for key in ('lean_binary', 'leanchecker_binary'):
        require(context['runtime'][key] == fp(context['runtime'][key]['path']), f'Runtime binary changed: {key}')
    namespace_files(stage, [row['module'] for row in context['suppliers']] + [row['module'] for row in context['targets']])


def parse_target_owned(log, context, module):
    """Keep the original full declaration audit and bind its actual project imports."""
    owned = parse_owned(log, module)
    marker = 'P26_GEOMETRY01_AUDIT_IMPORTS '
    imports = [json.loads(line[len(marker):]) for line in log.splitlines() if line.startswith(marker)]
    require(len(imports) == 1 and isinstance(imports[0], list) and
            all(isinstance(name, str) and name for name in imports[0]) and
            len(imports[0]) == len(set(imports[0])), 'Missing, duplicate or invalid imported-module inventory')
    target = next(row for row in context['targets'] if row['module'] == module)
    project = {name for name in imports[0] if name.startswith('ImbalancedChen.')}
    require(project == set(target['transitive_dependencies']) | {module}, 'Actual owned project import closure differs')
    return owned


def validate_step(accepted_identity, context, module, mode, check_inputs=True):
    """Validate RUN -> command -> result -> accepted seal and current exact files."""
    require(mode in MODES and module in {row['module'] for row in context['targets']}, 'Unknown requested step')
    if check_inputs:
        check_context_inputs(context)
    stage = canonical(context['stage'], True)
    seal_path = canonical(accepted_identity['path'], True)
    relative = seal_path.relative_to(stage / 'verification').parts
    require(len(relative) == 3 and ATTEMPT.fullmatch(relative[0]), 'Accepted receipt is outside an attempt')
    require(relative[1] == module.split('.')[-1] and relative[2] == mode + '-accepted.json',
            'Accepted receipt module/mode path mismatch')
    folder = seal_path.parent
    run_path = folder.parent / 'RUN.json'
    command_path = folder / (mode + '-command.json')
    result_path = folder / (mode + '-result.json')
    seal = checked(accepted_identity, seal_path)
    require(seal.get('schema') == 'cell05_connections14_step_accepted_v1', 'Unknown accepted-step schema')
    require(seal.get('module') == module and seal.get('mode') == mode and seal.get('status') == 'accepted',
            'Accepted-step labels mismatch')
    run = checked(seal['run'], run_path)
    require(run.get('schema') == 'cell05_connections14_run_v1' and run.get('attempt') == relative[0], 'RUN attempt mismatch')
    require(run.get('context') == context, 'Prior RUN differs in frozen inputs, cwd, environment, runtime or package roots')
    command = checked(seal['command'], command_path)
    result = checked(seal['result'], result_path)
    require(command.get('schema') == 'cell05_connections14_step_command_v1', 'Unknown command schema')
    require(result.get('schema') == 'cell05_connections14_step_result_v1', 'Unknown result schema')
    for value in (command, result):
        require(value.get('module') == module and value.get('mode') == mode, 'Explicit module/mode mismatch')
        require(value.get('run') == fp(run_path), 'RUN fingerprint link mismatch')
    require(result.get('command') == fp(command_path), 'Command fingerprint link mismatch')
    require(command.get('argv') == expected_argv(context, module, mode), 'Exact argv mismatch')
    require(command.get('cwd') == context['cwd'] and command.get('environment') == context['environment'],
            'Command cwd/environment mismatch')
    require(result.get('status') == 'succeeded' and result.get('exit_code') == 0 and result.get('termination_reason') is None,
            'Step did not succeed normally')
    paths = target_paths(context, module)
    target = next(row for row in context['targets'] if row['module'] == module)
    source, obj = fp(paths['source']), fp(paths['object'])
    require(same(source, target['source']), 'Target source pin mismatch')
    expected_audit = fp(paths['audit']) if mode == 'owned' else None
    if mode == 'owned':
        require(same(expected_audit, target['audit']), 'Owned audit pin mismatch')
    dependencies = dependency_objects(context, module)
    for value in (command, result):
        require(value.get('source') == source and value.get('audit_source') == expected_audit,
                'Source/audit must name current exact stage files')
        require(value.get('dependency_objects') == dependencies, 'Dependency object paths/bytes mismatch')
    require(command.get('object_before') == (None if mode == 'normal' else obj), 'object_before semantics mismatch')
    require(result.get('object') == seal.get('object') == obj, 'Result must name current exact stage object')
    log_path = folder / (mode + '.log')
    require(result.get('log') == fp(log_path), 'Log path or fingerprint mismatch')
    log = log_path.read_text()
    files = [seal_path, run_path, command_path, result_path, log_path]
    if mode == 'normal':
        reported = sorted({a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', log)
                           for a in group.split(',') if a.strip()})
        require(set(reported) <= ALLOWED and result.get('printed_axioms') == reported, 'Printed axiom mismatch')
    elif mode == 'kernel':
        require(log.strip() == 'replaying ' + module, 'Kernel log does not identify the exact target')
    else:
        owned_path = folder / 'owned-declarations.json'
        owned = checked(result['owned_declarations'], owned_path)
        require(parse_target_owned(log, context, module) == owned, 'Full owned inventory does not match its log')
        require(result.get('owned_declaration_count') == owned['owned_declaration_count'], 'Owned count mismatch')
        files.append(owned_path)
    require(isinstance(result.get('elapsed_seconds'), (int, float)) and result['elapsed_seconds'] >= 0,
            'Invalid elapsed time')
    require(isinstance(result.get('peak_rss_bytes'), int) and result['peak_rss_bytes'] >= 0, 'Invalid RSS count')
    return {'accepted': fp(seal_path), 'result': result, 'evidence_files': files}


def prior(context, module, mode):
    stage = Path(context['stage'])
    found = []
    prefix = '*/' + module.split('.')[-1] + '/' + mode
    results = sorted((stage / 'verification').glob(prefix + '-result.json'))
    seals = set((stage / 'verification').glob(prefix + '-accepted.json'))
    seals.update(path for path, key in indexed_seals(stage, [row['module'] for row in context['targets']]).items()
                 if key == (module, mode))
    for path in results:
        result = read(path)
        require(result.get('module') == module and result.get('mode') == mode, f'Prior explicit labels mismatch: {path}')
        if result.get('status') != 'succeeded' and result.get('exit_code') != 0:
            continue
        require(result.get('status') == 'succeeded' and result.get('exit_code') == 0, f'Contradictory successful receipt: {path}')
        obj = target_paths(context, module)['object']
        require(obj.exists(), f'Accepted object missing; restore exact bytes without recompiling: {obj}')
        seal = path.with_name(mode + '-accepted.json')
        require(seal.exists(), f'Successful result lacks its acceptance seal; manual evidence recovery required: {path}')
        seals.add(seal)
    for seal in sorted(seals):
        obj = target_paths(context, module)['object']
        require(obj.exists(), f'Accepted object missing; restore exact bytes without recompiling: {obj}')
        found.append(validate_step(fp(seal), context, module, mode, check_inputs=False))
    require(len(found) <= 1, f'Multiple executions claim acceptance for one step: {module} / {mode}')
    return found[0] if found else None


def require_accepted_prefix(context, reusable):
    """An interrupted sequential run cannot supply a later stage across a gap."""
    missing = False
    accepted = set()
    new_modules = {row['module'] for row in context['targets']}
    for target in context['targets']:
        module = target['module']
        for mode in MODES:
            item = reusable[module, mode]
            if item is None:
                missing = True
                continue
            require(not missing, 'Accepted steps contain a gap; restore missing evidence without replay')
            for dependency in set(target['transitive_dependencies']) & new_modules:
                require(all((dependency, previous) in accepted for previous in MODES),
                        'Accepted step lacks its fully accepted new dependency')
            require(all((module, previous) in accepted for previous in MODES[:MODES.index(mode)]),
                    'Accepted step lacks its preceding normal/kernel stage')
            accepted.add((module, mode))
    return len(accepted)


def validate_success(success_path):
    success_path = canonical(success_path, True)
    success = read(success_path)
    require(success.get('schema') == 'cell05_connections14_success_v1' and success.get('status') == 'succeeded',
            'Unknown or unsuccessful completion receipt')
    run = checked(success['run'], success_path.with_name('RUN.json'))
    require(run.get('schema') == 'cell05_connections14_run_v1' and ATTEMPT.fullmatch(run.get('attempt', '')),
            'SUCCESS references an invalid RUN schema/attempt')
    context = run['context']
    stage = canonical(context['stage'], True)
    require(success_path == stage / 'verification' / run['attempt'] / 'SUCCESS.json', 'SUCCESS path/context mismatch')
    require(success.get('context') == context, 'SUCCESS/RUN context mismatch')
    check_context_inputs(context)
    targets = [row['module'] for row in context['targets']]
    require(len(targets) == len(set(targets)) == 14, 'Exactly 14 new owners required')
    expected = [(module, mode) for module in targets for mode in MODES]
    records = success['records']
    require([(row.get('module'), row.get('mode')) for row in records] == expected, '42-step order/coverage mismatch')
    checked_steps, objects, newly, reused = [], {}, 0, 0
    for row in records:
        item = validate_step(row['accepted'], context, row['module'], row['mode'], check_inputs=False)
        require(row.get('disposition') in ('executed', 'reused'), 'Unknown step disposition')
        owner_attempt = Path(row['accepted']['path']).parent.parent.name
        require((owner_attempt == run['attempt']) == (row['disposition'] == 'executed'), 'Execution/reuse attempt mismatch')
        newly += row['disposition'] == 'executed'
        reused += row['disposition'] == 'reused'
        module, obj = row['module'], item['result']['object']
        objects.setdefault(module, obj)
        require(objects[module] == obj, 'Three-step final objects differ')
        checked_steps.append(item)
    require(success.get('accepted_steps') == 42 and success.get('newly_executed_steps') == newly
            and success.get('reused_steps') == reused, 'Actual execution counts mismatch')
    require(success.get('accepted_targets') == 14 and success.get('frozen_inputs_unchanged') is True,
            'Completion scope mismatch')
    require(success.get('whole_geometry_decoded') is False and success.get('P2_6_complete') is False,
            'Fourteen-owner completion scope expanded')
    return context, checked_steps
