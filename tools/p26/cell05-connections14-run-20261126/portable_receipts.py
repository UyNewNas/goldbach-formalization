#!/usr/bin/env python3
"""Validate the original v3 receipt semantics through an explicit read-only view.

Original JSON, cwd, environment, argv and absolute paths are never rewritten.
Physical installation identities are deliberately outside this historical view.
"""
from pathlib import PurePosixPath as P
import json
import re

from evidence_io import absolute, pin, require, same
from receipt_support import ALLOWED, parse_owned

MODES = ('normal', 'kernel', 'owned')
ATTEMPT = re.compile(r'[A-Za-z0-9_-]+')
PACKAGES = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']


def target_paths(context, module, tool_rel):
    stage = absolute(context['stage'])
    relative = P(module.replace('.', '/'))
    return {'source': stage / 'project' / relative.with_suffix('.lean'),
            'object': stage / 'objects' / relative.with_suffix('.olean'),
            'audit': stage / tool_rel / 'owned-audits' / (relative.name + '.lean')}


def expected_argv(context, module, mode, tool_rel):
    paths = target_paths(context, module, tool_rel)
    common = [context['runtime']['lean_binary']['path'], '-j1', f'-M{context["rss_limit_bytes"] // 1024**2}',
              '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        return common + ['-o', str(paths['object']), module.replace('.', '/') + '.lean']
    if mode == 'kernel':
        return [context['runtime']['leanchecker_binary']['path'], '--verbose', module]
    require(mode == 'owned', 'Unknown historical step mode')
    return common + [str(paths['audit'])]


def validate_context(view, context, expected_context):
    require(context == expected_context, 'Historical RUN differs from its independently pinned context')
    require(context['schema'] == 'cell05_complete_context_v2', 'Unknown historical context schema')
    stage = absolute(context['stage'])
    require(context['cwd'] == str(stage / 'project') and context['objects'] == str(stage / 'objects'),
            'Historical stage/cwd/object layout differs')
    roots = [context['objects'], *context['mathlib_package_object_roots'], context['mathlib_objects']]
    require(context['environment']['LEAN_PATH'] == ':'.join(roots), 'Historical LEAN_PATH order differs')
    parent = absolute(context['mathlib_dependency_parent'])
    package_roots = [str(parent / name / '.lake/build/lib/lean') for name in PACKAGES]
    require(context['mathlib_package_object_roots'] in [package_roots, package_roots + [str(parent / 'Cli/.lake/build/lib/lean')]],
            'Historical package names/order differ')
    require(context['mathlib_objects'] == str(absolute(context['mathlib']) / '.lake/build/lib/lean'),
            'Historical Mathlib object root differs')
    env = context['environment']
    require(env['LEAN_NUM_THREADS'] == env['OMP_NUM_THREADS'] == '1', 'Historical threading differs')
    require(env['LEAN_SYSROOT'] == str(absolute(context['runtime']['lean_binary']['path']).parent.parent),
            'Historical sysroot differs')
    require(context['old_supplier_proof_commands'] == 0 and context['cloud_source_generation'] is False,
            'Historical scope changed')
    identities = context['frozen_inputs']
    require(len({row['path'] for row in identities}) == len(identities), 'Duplicate frozen historical path')
    for identity in identities:
        require(view.fp(identity['path']) == identity, f'Frozen historical file differs: {identity["path"]}')
    for key in ('lean_binary', 'leanchecker_binary'):
        identity = context['runtime'][key]
        require(view.fp(identity['path']) == identity, f'Historical binary bytes differ: {key}')


def validate_step(view, accepted_identity, context, module, mode, tool_rel):
    require(mode in MODES and module in {row['module'] for row in context['targets']}, 'Unknown requested historical step')
    stage = absolute(context['stage'])
    seal_path = absolute(accepted_identity['path'])
    relative = seal_path.relative_to(stage / 'verification').parts
    require(len(relative) == 3 and ATTEMPT.fullmatch(relative[0])
            and relative[1:] == (module.split('.')[-1], mode + '-accepted.json'), 'Historical accepted path/module/mode differs')
    folder = seal_path.parent
    run_path, command_path, result_path = folder.parent / 'RUN.json', folder / (mode + '-command.json'), folder / (mode + '-result.json')
    seal = view.checked(accepted_identity, seal_path)
    require(seal.get('schema') == 'cell05_step_accepted_v2' and seal.get('status') == 'accepted'
            and seal.get('module') == module and seal.get('mode') == mode, 'Historical accepted seal labels differ')
    run = view.checked(seal['run'], run_path)
    require(run.get('schema') == 'cell05_complete_run_v2' and run.get('attempt') == relative[0]
            and run.get('context') == context, 'Historical accepted RUN/context link differs')
    command, result = view.checked(seal['command'], command_path), view.checked(seal['result'], result_path)
    require(command.get('schema') == 'cell05_step_command_v2' and result.get('schema') == 'cell05_step_result_v2',
            'Unknown historical command/result schema')
    for value in (command, result):
        require(value.get('module') == module and value.get('mode') == mode, 'Historical explicit module/mode differs')
        require(value.get('run') == view.fp(run_path), 'Historical RUN fingerprint link differs')
    require(result.get('command') == view.fp(command_path), 'Historical command fingerprint link differs')
    require(command.get('argv') == expected_argv(context, module, mode, tool_rel), 'Historical exact argv differs')
    require(command.get('cwd') == context['cwd'] and command.get('environment') == context['environment'],
            'Historical command cwd/environment differs')
    require(result.get('status') == 'succeeded' and result.get('exit_code') == 0 and result.get('termination_reason') is None,
            'Historical proof step did not succeed normally')
    target = next(row for row in context['targets'] if row['module'] == module)
    paths = target_paths(context, module, tool_rel)
    source, obj = view.fp(paths['source']), view.fp(paths['object'])
    require(same(source, target['source']), 'Historical source pin differs')
    audit = view.fp(paths['audit']) if mode == 'owned' else None
    require(mode != 'owned' or same(audit, target['audit']), 'Historical audit pin differs')
    deps = {dependency: view.fp(stage / 'objects' / (dependency.replace('.', '/') + '.olean'))
            for dependency in target['transitive_dependencies']}
    for value in (command, result):
        require(value.get('source') == source and value.get('audit_source') == audit, 'Historical source/audit path differs')
        require(value.get('dependency_objects') == deps, 'Historical dependency object path/bytes differ')
    require(command.get('object_before') == (None if mode == 'normal' else obj), 'Historical object_before semantics differ')
    require(result.get('object') == seal.get('object') == obj, 'Historical final object path/bytes differ')
    log_path = folder / (mode + '.log')
    require(result.get('log') == view.fp(log_path), 'Historical log path/hash differs')
    log = view.raw(log_path).decode()
    evidence = [seal_path, run_path, command_path, result_path, log_path]
    if mode == 'normal':
        axioms = sorted({a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', log)
                         for a in group.split(',') if a.strip()})
        require(set(axioms) <= ALLOWED and result.get('printed_axioms') == axioms, 'Historical normal axiom report differs')
    elif mode == 'kernel':
        require(log.strip() == 'replaying ' + module, 'Historical kernel target log differs')
    else:
        owned_path = folder / 'owned-declarations.json'
        owned = view.checked(result['owned_declarations'], owned_path)
        require(parse_owned(log, module) == owned and result.get('owned_declaration_count') == owned['owned_declaration_count'],
                'Historical complete owned declarations differ')
        evidence.append(owned_path)
    require(isinstance(result.get('elapsed_seconds'), (float, int)) and result['elapsed_seconds'] >= 0,
            'Historical time is invalid')
    require(isinstance(result.get('peak_rss_bytes'), int) and result['peak_rss_bytes'] >= 0, 'Historical RSS is invalid')
    return {'accepted': view.fp(seal_path), 'result': result, 'evidence_paths': [str(path) for path in evidence]}


def validate_success(view, success_identity, expected_context, tool_rel, target_count):
    success_path = absolute(success_identity['path'])
    success = view.checked(success_identity, success_path)
    require(success.get('schema') == 'cell05_complete_success_v2' and success.get('status') == 'succeeded',
            'Unknown historical success schema/status')
    run = view.checked(success['run'], success_path.with_name('RUN.json'))
    require(run.get('schema') == 'cell05_complete_run_v2' and ATTEMPT.fullmatch(run.get('attempt', '')),
            'Invalid historical RUN schema/attempt')
    context = run['context']
    require(success_path == absolute(context['stage']) / 'verification' / run['attempt'] / 'SUCCESS.json',
            'Historical success path differs from RUN')
    require(success.get('context') == context, 'Historical SUCCESS/RUN context differs')
    validate_context(view, context, expected_context)
    targets = [row['module'] for row in context['targets']]
    require(len(targets) == len(set(targets)) == target_count, 'Historical target count differs')
    expected = [(module, mode) for module in targets for mode in MODES]
    require([(row.get('module'), row.get('mode')) for row in success['records']] == expected,
            'Historical ordered step coverage differs')
    checked_steps, objects, newly, reused = [], {}, 0, 0
    for record in success['records']:
        module, mode = record['module'], record['mode']
        checked = validate_step(view, record['accepted'], context, module, mode, tool_rel)
        disposition = record.get('disposition')
        require(disposition in ('executed', 'reused'), 'Unknown historical disposition')
        attempt = absolute(record['accepted']['path']).parent.parent.name
        require((attempt == run['attempt']) == (disposition == 'executed'), 'Historical execution/reuse attempt differs')
        newly += disposition == 'executed'
        reused += disposition == 'reused'
        obj = checked['result']['object']
        require(objects.setdefault(module, obj) == obj, 'Historical three steps accepted different objects')
        checked_steps.append(checked)
    require(success.get('accepted_steps') == target_count * 3 and success.get('accepted_targets') == target_count
            and success.get('newly_executed_steps') == newly and success.get('reused_steps') == reused,
            'Historical actual step counts differ')
    require(success.get('frozen_inputs_unchanged') is True and success.get('whole_geometry_decoded') is False
            and success.get('P2_6_complete') is False, 'Historical limited acceptance scope changed')
    return {'target_count': target_count, 'accepted_steps': target_count * 3,
            'newly_executed_steps': newly, 'reused_steps': reused,
            'owned_declaration_count': sum(row['result']['owned_declaration_count'] for row in checked_steps
                                           if row['result']['mode'] == 'owned'),
            'objects': objects, 'steps': checked_steps}
