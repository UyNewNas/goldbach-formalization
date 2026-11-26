#!/usr/bin/env python3
"""Validate Archive bridges, reusing exact accepted steps from a partial attempt.

The fixed Geometry01 retry runs only its normal/kernel/owned checks. The two
compatibility checks and three accepted Cell00 checks are verified and reused.
"""
import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sys
import uuid


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def merge_supplier(namespace, row, variants):
    """Earlier accepted decoder suppliers are canonical for identical sources."""
    module = row['module']
    previous = namespace.get(module)
    if previous is None:
        namespace[module] = row
        return
    need(previous['source']['sha256'] == row['source']['sha256'],
         f'Different source bytes for the same module: {module}')
    if previous['object']['sha256'] != row['object']['sha256']:
        variants.append({'module': module, 'source_sha256': row['source']['sha256'],
            'canonical': previous, 'historical_alternative': row,
            'policy': 'retain_the_already_accepted_decoder_instance'})


def load_shared(path, expected):
    import hashlib
    need(hashlib.sha256(path.read_bytes()).hexdigest() == expected['sha256'],
         'Shared verification helper fingerprint differs')
    spec = importlib.util.spec_from_file_location('p26_cell00_shared', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def logical_context_signature(snapshot):
    """Compare imported bytes while allowing a fresh attempt root/new proof source."""
    def pin(row):
        return row['sha256'], row['bytes']
    return {
        'canonical_modules': {module: (pin(row['source']), pin(row['object']))
            for module, row in snapshot['canonical_modules'].items()},
        'project_objects_and_sidecars': sorted((row['module'], Path(row['path']).name, pin(row))
            for row in snapshot['project_object_union']),
        'external_modules': {row['module']: (pin(row['source']), pin(row['object']),
            sorted((Path(side['path']).name, pin(side)) for side in row.get('sidecars', [])))
            for row in snapshot['external_modules']},
        'literal_inputs_and_manifests': sorted((row['path'], pin(row)) for row in snapshot['files']
            if 'original-inputs' in Path(row['path']).parts or Path(row['path']).name in {
                'MANIFEST.json', 'HIGHER_MOMENTS_PINNED_CLOSURE.json', 'ANALYTIC_FREEZE.json',
                'ARCHIVE_EXTRA_PINNED_CLOSURE.json', 'ARCHIVE_EXTRA_FREEZE.json',
                'ORIGINAL_INPUT_SOURCE_MANIFEST.json'})}


def reuse_partial_attempt(shared, prior, current_context, current_inputs, registry, remember):
    """Validate five successful chains without requiring the cancelled run's RESULT."""
    prior = Path(prior).resolve()
    stage = Path(current_context['stage'])
    need(prior.is_relative_to(stage / 'attempts'), 'Prior partial attempt is outside this stage')
    need(prior.name == registry['retry']['prior_attempt_name'], 'Unexpected prior partial attempt')
    run_path, inputs_path = prior / 'RUN.json', prior / 'INPUT_FINGERPRINTS.json'
    run_pin = remember(run_path, root=prior)
    old_context = shared.read_json(run_path)
    for key in ('driver', 'registry'):
        expected = registry['retry']['previous_' + key]
        need(all(old_context[key][part] == expected[part] for part in ('sha256', 'bytes')),
             f'Prior accepted {key} differs from the preserved revision')
    inputs_pin = remember(inputs_path, old_context['inputs'], prior)
    old_inputs = shared.read_json(inputs_path)
    need(old_context['canonical_project_modules'] == 1034, 'Prior namespace is incomplete')
    for key in ('lean_version', 'package_revisions', 'shared_driver', 'mixed_object_modules'):
        need(old_context[key] == current_context[key], f'Reuse runtime/context differs: {key}')
    for key in ('lean_binary', 'leanchecker_binary'):
        need(old_context[key] == current_context[key], f'Reuse runtime binary differs: {key}')
        remember(old_context[key]['path'], old_context[key], Path(old_context[key]['path']).parent)
    need(old_context['LEAN_PATH'].split(os.pathsep)[1:] ==
         current_context['LEAN_PATH'].split(os.pathsep)[1:], 'Reuse external search paths differ')
    need(logical_context_signature(old_inputs) == logical_context_signature(current_inputs),
         'Prior accepted supplier/source/object/literal context differs')
    # Rehash the old namespace as well as the current namespace. The original
    # attempt's copied sources remain immutable even if stage/new-sources changes.
    for row in old_inputs['canonical_modules'].values():
        for key in ('source', 'object'):
            remember(row[key]['path'], row[key], Path(row[key]['path']).parent)
    for row in old_inputs['project_object_union']:
        remember(row['path'], row, prior)
    for row in old_inputs['external_modules']:
        for ref in [row['source'], row['object'], *row.get('sidecars', [])]:
            remember(ref['path'], ref, Path(ref['path']).parent)
    old_geometry = prior / 'project' / registry['retry']['geometry_source_relative_path']
    preserved_geometry = remember(old_geometry, registry['retry']['previous_geometry_source'], prior)
    geometry_module = registry['retry']['only_target_module']
    for mode in ('normal', 'kernel', 'owned'):
        need(not (prior / 'steps' / geometry_module.split('.')[-1] / mode / 'ACCEPTED_STEP.json').exists(),
             f'Geometry01 {mode} became accepted; refusing to repeat it')
    cell00 = next(row for row in registry['targets'] if row['key'] == 'cell00')
    requested = [(module, 'kernel_compatibility') for module in registry['compatibility_targets']]
    requested += [(cell00['module'], mode) for mode in ('normal', 'kernel', 'owned')]
    reused, cell00_phases = [], []
    for module, mode in requested:
        folder = prior / 'steps' / module.split('.')[-1] / mode
        receipt_pin = remember(folder / 'ACCEPTED_STEP.json', root=prior)
        accepted = shared.read_json(receipt_pin['path'])
        need(accepted['module'] == module and accepted['mode'] == mode and
             accepted['status'] == 'succeeded' and accepted['all_frozen_inputs_unchanged'],
             f'Prior step was not accepted: {module}/{mode}')
        need(accepted['context'] == run_pin, 'Prior step/context binding differs')
        for key in ('source', 'object', 'command_result', 'log'):
            ref = accepted[key]
            remember(ref['path'], ref, prior if key != 'source' else Path(ref['path']).parent)
        for ref in accepted.get('object_sidecars', []):
            remember(ref['path'], ref, prior)
        expected_source = (current_inputs['canonical_modules'][module]['source']
            if mode == 'kernel_compatibility' else cell00['source'])
        need(all(accepted['source'][key] == expected_source[key] for key in ('sha256', 'bytes')),
             f'Prior accepted source differs: {module}')
        if mode == 'kernel_compatibility':
            expected_object = current_inputs['canonical_modules'][module]['object']
            need(all(accepted['object'][key] == expected_object[key] for key in ('sha256', 'bytes')),
                 f'Prior compatibility object differs: {module}')
        else:
            cell00_phases.append(accepted)
        result = shared.read_json(accepted['command_result']['path'])
        need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
             not result['timed_out'] and result['error'] is None, 'Prior command failed')
        command_pin = remember(result['command']['path'], result['command'], prior)
        command = shared.read_json(command_pin['path'])
        need(all(result[key] == value for key, value in command.items()), 'Prior command/result differs')
        need(result['module'] == module and result['mode'] == mode and
             result['source'] == accepted['source'] and result['log'] == accepted['log'] and
             result['input_fingerprints'] == inputs_pin and
             result['LEAN_PATH'] == old_context['LEAN_PATH'] and
             result['cwd'] == old_context['project'], 'Prior command bindings differ')
        if mode in ('kernel', 'kernel_compatibility'):
            need(result['argv'] == [old_context['leanchecker_binary']['path'], '--verbose', module],
                 'Prior accepted command was not the requested independent kernel check')
            need(result['object_before'] == accepted['object'], 'Prior kernel object binding differs')
        elif mode == 'normal':
            argv = result['argv']
            need(argv[0] == old_context['lean_binary']['path'] and result['object_before'] is None and
                 argv[-3:] == ['-o', accepted['object']['path'], cell00['source_relative_path']],
                 'Prior normal command target/output differs')
        else:
            audit_pin = remember(accepted['audit_source']['path'], accepted['audit_source'], prior)
            need(all(audit_pin[key] == cell00['audit'][key] for key in ('sha256', 'bytes')) and
                 result['audit_source'] == audit_pin and result['object_before'] == accepted['object'] and
                 result['argv'][0] == old_context['lean_binary']['path'] and
                 result['argv'][-1] == audit_pin['path'], 'Prior owned-audit bindings differ')
            prefix = registry['owned_audit_marker_prefix']
            normalized = '\n'.join('P26_CELL00_AUDIT_' + line[len(prefix):]
                if line.startswith(prefix) else line for line in Path(accepted['log']['path']).read_text().splitlines())
            need(shared.parse_owned(normalized, module) == accepted['owned'], 'Prior full owned audit differs')
        reused.append({'module': module, 'mode': mode, 'receipt': receipt_pin,
            'source': accepted['source'], 'object': accepted['object'], 'reused': True,
            'command_result': accepted['command_result'], 'command': command_pin, 'log': accepted['log']})
    need(all(row['source'] == cell00_phases[0]['source'] and row['object'] == cell00_phases[0]['object']
             for row in cell00_phases), 'Prior Cell00 phases bound different source/object bytes')
    return {'status': 'FIVE_ACCEPTED_STEPS_REUSED', 'prior_attempt': str(prior),
        'prior_attempt_state': 'cancelled_partial', 'prior_final_result_required': False,
        'prior_run': run_pin, 'prior_inputs': inputs_pin, 'preserved_previous_geometry_source': preserved_geometry,
        'same_logical_supplier_source_object_runtime_literal_context': True, 'steps': reused,
        'compatibility_kernel_receipts_reused': 2, 'already_accepted_owner_receipts_reused': 3,
        'prior_commands_reexecuted': 0}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--registry', type=Path, default=Path(__file__).with_name('ArchiveBridges_REGISTRY.json'))
    ap.add_argument('--shared-driver', type=Path,
                    default=Path(__file__).with_name('Cell00OriginalFloor_continue.py'))
    ap.add_argument('--stage', type=Path)
    ap.add_argument('--cell00-stage', type=Path)
    ap.add_argument('--geometry01-stage', type=Path)
    ap.add_argument('--cell00-attempt', type=Path)
    ap.add_argument('--reuse-passed-attempt', type=Path,
                    help='Cancelled partial archive attempt containing the five accepted steps')
    ap.add_argument('--geometry-pins', type=Path,
                    default=Path(__file__).with_name('GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json'))
    ap.add_argument('--target', choices=('all', 'cell00', 'geometry01'), default='geometry01')
    ap.add_argument('--lean-bin', type=Path,
                    default=Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin'))
    ap.add_argument('--mathlib', type=Path,
                    default=Path('/workspace/blue-member-build/.lake/packages/mathlib'))
    ap.add_argument('--goldbach', type=Path)
    ap.add_argument('--leanarchitect', type=Path)
    ap.add_argument('--rss-gib', type=int, default=14)
    ap.add_argument('--wall-seconds', type=int, default=1800)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime(
        '%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8])
    args = ap.parse_args()
    registry = json.loads(args.registry.read_text())
    shared = load_shared(args.shared_driver.resolve(), registry['cell00_shared_driver'])
    need(shared.fp(__file__)['sha256'] == registry['driver']['sha256'], 'Archive verifier fingerprint differs')
    need(args.attempt and all(c.isalnum() or c in '_-' for c in args.attempt), 'Invalid attempt name')
    stage = (args.stage or Path(registry['stage'])).resolve()
    cell00 = (args.cell00_stage or Path(registry['cell00_stage'])).resolve()
    geometry = (args.geometry01_stage or Path(registry['geometry01_stage'])).resolve()
    prior = (args.cell00_attempt or Path(registry['cell00_accepted_attempt'])).resolve()
    retry_prior = (args.reuse_passed_attempt or Path(registry['retry']['prior_attempt'])).resolve()
    need(args.target == 'geometry01', 'This retry is restricted to the unaccepted Geometry01 owner')
    extra = cell00 / 'archive-extra'
    attempt = stage / 'attempts' / args.attempt
    attempt.mkdir(parents=True, exist_ok=False)
    records, owner_results, phase = [], [], 'preflight'
    try:
        frozen, namespace, variants = {}, {}, []

        def remember(path, pin=None, root=None):
            path = Path(path).absolute()
            root = Path(root or path.parent).resolve()
            actual = shared.require_pin(path, pin or shared.fp(path), root)
            frozen[str(path)] = {**actual, 'root': str(root)}
            return actual

        def add(module, source, obj, source_sha, object_sha, object_bytes, origin, root, source_bytes=None):
            sp = {'sha256': source_sha}
            if source_bytes is not None:
                sp['bytes'] = source_bytes
            row = {'module': module, 'source': remember(source, sp, root),
                   'object': remember(obj, {'sha256': object_sha, 'bytes': object_bytes}, root),
                   'origin': origin}
            merge_supplier(namespace, row, variants)
            return row

        # Canonical precedence: the current cell00 decoder, the P3 geometry01
        # decoder, then the original P1 Core alternatives. Source changes stop.
        manifest_path = cell00 / 'MANIFEST.json'
        remember(manifest_path, registry['cell00_bundle_manifest'], cell00)
        manifest = shared.read_json(manifest_path)
        by_module = {}
        for row in manifest['files']:
            if row['role'] in ('project_source', 'project_object'):
                by_module.setdefault(row['module'], {})[row['role']] = row
        need(len(by_module) == 480, 'Incomplete cell00 supplier bundle')
        for module, pair in by_module.items():
            s, o = pair['project_source'], pair['project_object']
            add(module, cell00 / s['archive_path'], cell00 / o['archive_path'],
                s['sha256'], o['sha256'], o['bytes'], 'accepted_cell00', cell00, s['bytes'])
        analytic_path = cell00 / 'HIGHER_MOMENTS_PINNED_CLOSURE.json'
        remember(analytic_path, registry['higher_analytic_pins'], cell00)
        analytic = shared.read_json(analytic_path)
        freeze_path = cell00 / 'ANALYTIC_FREEZE.json'
        remember(freeze_path, root=cell00)
        af = shared.read_json(freeze_path)
        need(af['status'] == 'exact_accepted_suppliers_frozen' and af['analytic_modules'] == 224,
             'Analytic freeze did not succeed')
        need(af['pins_sha256'] == registry['higher_analytic_pins']['sha256'], 'Analytic freeze pin mismatch')
        af_rows = {r['module']: r for r in af['analytic_rows']}
        need(len(analytic['rows']) == len(af_rows) == 224, 'Incomplete analytic freeze')
        for row in analytic['rows']:
            module = row['module']
            source = cell00 / 'analytic/sources' / shared.module_path(module, '.lean')
            obj = cell00 / 'analytic/objects' / shared.module_path(module, '.olean')
            bound = af_rows[module]
            need(bound['source_sha256'] == row['source_sha256'] and
                 bound['object_sha256'] == row['object_sha256'] and
                 bound['frozen_source'] == str(source) and bound['frozen_object'] == str(obj),
                 f'Analytic freeze row mismatch: {module}')
            add(module, source, obj, row['source_sha256'], row['object_sha256'], row['bytes'],
                'accepted_analytic', cell00)
        remember(args.geometry_pins, registry['geometry01_accepted_pins'], args.geometry_pins.parent)
        gp = shared.read_json(args.geometry_pins)
        need(gp['module_count'] == len(gp['rows']) == 311, 'Expected all 311 accepted geometry suppliers')
        for row in gp['rows']:
            need(row['normal_kernel_accepted'], 'Unaccepted geometry supplier')
            add(row['module'], geometry / row['source_member'], geometry / row['object_member'],
                row['source_sha256'], row['object_sha256'], row['bytes'],
                'accepted_geometry01', geometry, row['source_bytes'])
        extra_path = extra / 'ARCHIVE_EXTRA_PINNED_CLOSURE.json'
        remember(extra_path, registry['archive_extra_pins'], extra)
        xp = shared.read_json(extra_path)
        extra_freeze_path = extra / 'ARCHIVE_EXTRA_FREEZE.json'
        remember(extra_freeze_path, registry['archive_extra_freeze'], extra)
        xf = shared.read_json(extra_freeze_path)
        need(xf['status'] == 'exact_archive_extra_frozen' and xf['module_count'] == 26,
             'Archive extra freeze did not succeed')
        need(xf['pins']['sha256'] == registry['archive_extra_pins']['sha256'], 'Archive freeze pin differs')
        need(xf['raw_json_input_count'] == 26, 'Original JSON inputs were not preserved')
        need(xf['historical_core_result']['sha256'] == xp['core_result_sha256'], 'Historical Core result differs')
        for row in xf['files']:
            remember(row['path'], row, extra)
        remember(xf['original_input_pins']['path'], xf['original_input_pins'], extra)
        remember(extra / 'ORIGINAL_INPUT_SOURCE_MANIFEST.json', xp['original_input_pin_manifest'], extra)
        for raw in xp['original_json_inputs']:
            remember(extra / 'original-inputs' / Path(raw['loader_absolute_path']).name, raw, extra)
        for row in xp['rows']:
            module = row['module']
            add(module, extra / 'sources' / shared.module_path(module, '.lean'),
                extra / 'objects' / shared.module_path(module, '.olean'),
                row['source_sha256'], row['object_sha256'], row['bytes'],
                'historical_P1_core_extra', extra, row['source_bytes'])
        # The four Core dependencies already supplied by cell00 have different
        # historical object bytes. Preserve both fingerprints without replacing
        # the canonical decoder objects or claiming the old context is identical.
        for old in xp['already_supplied']:
            canonical = namespace[old['module']]
            need(canonical['source']['sha256'] == old['source_sha256'], 'Historical Core source changed')
            if canonical['object']['sha256'] != old['object_sha256']:
                variants.append({'module': old['module'], 'source_sha256': old['source_sha256'],
                    'canonical': canonical, 'historical_alternative': old,
                    'policy': 'retain_the_already_accepted_decoder_instance'})
        need({r['module'] for r in variants} == set(registry['mixed_object_modules']),
             'Unexpected mixed-context module inventory')
        # Only the two accepted continuation owners are imported from the prior
        # attempt. Do not bulk-copy its 704 suppliers over this canonical union.
        previous_result = shared.read_json(prior / 'RESULT.json')
        need(previous_result['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED', 'Cell00 continuation did not pass')
        remember(prior / 'RESULT.json', root=cell00)
        old_records = previous_result['records']
        for module in registry['cell00_continuation_owners']:
            phases = {}
            for mode in ('normal', 'kernel', 'owned'):
                found = [r for r in old_records if r['module'] == module and r['mode'] == mode]
                need(len(found) == 1, f'Missing accepted continuation {mode}: {module}')
                ref = found[0]['receipt']
                remember(ref['path'], ref, cell00)
                step = shared.read_json(ref['path'])
                need(step['status'] == 'succeeded' and step['all_frozen_inputs_unchanged'],
                     f'Unaccepted continuation step: {module}')
                remember(step['command_result']['path'], step['command_result'], cell00)
                result = shared.read_json(step['command_result']['path'])
                need(result['status'] == 'succeeded' and result['exit_code'] == 0, 'Prior command failed')
                remember(result['command']['path'], result['command'], cell00)
                remember(step['log']['path'], step['log'], cell00)
                need(result['log'] == step['log'], 'Prior continuation log binding differs')
                phases[mode] = step
            accepted = phases['owned']
            shared.parse_owned(Path(accepted['log']['path']).read_text(), module)
            need(all(phases[mode]['source']['sha256'] == accepted['source']['sha256'] and
                     phases[mode]['object']['sha256'] == accepted['object']['sha256']
                     for mode in ('normal', 'kernel')), 'Continuation phases bound different bytes')
            add(module, accepted['source']['path'], accepted['object']['path'],
                accepted['source']['sha256'], accepted['object']['sha256'], accepted['object']['bytes'],
                'accepted_cell00_continuation', cell00, accepted['source']['bytes'])
        need(len(namespace) == 1034, 'Unexpected canonical project namespace size')
        project, objects = attempt / 'project', attempt / 'objects'
        project.mkdir()
        objects.mkdir()
        union = shared.copy_project_union(objects, {m: r['object'] for m, r in namespace.items()})
        for row in union:
            remember(row['path'], row, attempt)
        targets = [row for row in registry['targets'] if args.target in ('all', row['key'])]
        new_files = {}
        for target in targets:
            module = target['module']
            source = stage / 'new-sources' / target['source_relative_path']
            audit = stage / 'audits' / target['audit_file']
            remember(source, target['source'], stage)
            remember(audit, target['audit'], stage)
            destination = project / target['source_relative_path']
            audit_copy = attempt / 'audits' / target['audit_file']
            for original, copy, pin in ((source, destination, target['source']),
                                        (audit, audit_copy, target['audit'])):
                copy.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(original, copy)
                remember(copy, pin, attempt)
            new_files[module] = {'source': destination, 'audit': audit_copy}
        external_pin_path = args.shared_driver.with_name('Cell00OriginalFloor_EXTERNAL_PINS.json')
        remember(external_pin_path, registry['external_source_pins'], external_pin_path.parent)
        packages = {'goldbach': (args.goldbach or args.mathlib.parent / 'goldbach').resolve(),
                    'LeanArchitect': (args.leanarchitect or args.mathlib.parent / 'LeanArchitect').resolve()}
        external = shared.external_inputs(shared.read_json(external_pin_path), packages)
        for row in external['files']:
            remember(row['path'], row, row['root'])
        runtime_roots = shared.package_roots(args.mathlib) + external['object_roots']
        lean, checker = args.lean_bin.resolve() / 'lean', args.lean_bin.resolve() / 'leanchecker'
        env = os.environ.copy()
        env.pop('LEAN_SRC_PATH', None)
        env.pop('LEAN_SYSROOT', None)
        env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
        env['LEAN_PATH'] = os.pathsep.join(str(p) for p in [objects, *runtime_roots])
        env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
        version = shared.run_command([str(lean), '--version'], project, env, attempt / 'runtime/lean', 30)
        version_text = Path(version['log']['path']).read_text().strip()
        need('4.33.0-rc1' in version_text and shared.LEAN_COMMIT in version_text, 'Unexpected Lean runtime')
        revisions = {}
        for name, root, pin in [('mathlib', args.mathlib, shared.MATHLIB_COMMIT),
                *[(name, root, shared.EXTERNAL_COMMITS[name]) for name, root in packages.items()]]:
            result = shared.run_command(['git', '-C', str(root), 'rev-parse', 'HEAD'], project, env,
                                        attempt / 'runtime' / name, 30)
            revision = Path(result['log']['path']).read_text().strip()
            need(revision == pin, f'External source Git pin differs: {name}')
            revisions[name] = revision
        inputs = {'files': list(frozen.values()),
            'canonical_modules': namespace, 'mixed_object_context': variants,
            'project_object_union': union, 'external_modules': external['modules']}
        shared.write_json(attempt / 'INPUT_FINGERPRINTS.json', inputs)
        input_pin = shared.fp(attempt / 'INPUT_FINGERPRINTS.json')
        context = {'schema': 'p26_archive_bridge_retry_attempt_v2', 'attempt': args.attempt,
            'stage': str(stage), 'project': str(project), 'LEAN_PATH': env['LEAN_PATH'],
            'registry': shared.fp(args.registry), 'driver': shared.fp(__file__),
            'shared_driver': shared.fp(args.shared_driver), 'lean_version': version_text,
            'lean_binary': shared.fp(lean), 'leanchecker_binary': shared.fp(checker),
            'package_revisions': revisions, 'inputs': input_pin, 'canonical_project_modules': 1034,
            'mixed_object_modules': [r['module'] for r in variants],
            'historical_core_context_identical_claimed': False,
            'generic_normal_recompilation': False, 'cloud_lean_source_generation': False,
            'previous_attempt': str(retry_prior), 'previous_attempt_state': 'cancelled_partial',
            'new_context_compatibility_kernel_count': 0, 'compatibility_receipts_reused': 2,
            'already_accepted_owner_receipts_reused': 3}
        shared.write_json(attempt / 'RUN.json', context)

        def unchanged():
            for row in frozen.values():
                shared.require_pin(row['path'], row, row['root'])

        def step(module, mode, source, audit=None):
            unchanged()
            obj = objects / shared.module_path(module, '.olean')
            before = shared.fp(obj) if obj.exists() else None
            flags = ['-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
            if mode == 'normal':
                need(module in new_files and before is None, 'Refusing existing owner normal compilation')
                obj.parent.mkdir(parents=True, exist_ok=True)
                argv = [str(lean), *flags, '-o', str(obj), str(Path(source).relative_to(project))]
            elif mode in ('kernel', 'kernel_compatibility'):
                need(before is not None, 'Missing kernel target object')
                argv = [str(checker), '--verbose', module]
            else:
                need(mode == 'owned' and audit is not None and before is not None, 'Invalid owned audit')
                argv = [str(lean), *flags, str(audit)]
            folder = attempt / 'steps' / module.split('.')[-1] / mode
            result = shared.run_command(argv, project, env, folder, args.wall_seconds,
                {'module': module, 'mode': mode, 'source': shared.fp(source), 'object_before': before,
                 'audit_source': shared.fp(audit) if audit else None, 'input_fingerprints': input_pin})
            unchanged()
            after = remember(obj, root=attempt)
            if before:
                need(before['sha256'] == after['sha256'], 'Object changed during validation')
            output_sidecars = []
            for extra_output in (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir')):
                if extra_output.exists():
                    output_sidecars.append(remember(extra_output, root=attempt))
            accepted = {'module': module, 'mode': mode, 'status': 'succeeded',
                'source': shared.fp(source), 'object': after, 'command_result': shared.fp(folder / 'result.json'),
                'log': result['log'], 'all_frozen_inputs_unchanged': True,
                'object_sidecars': output_sidecars,
                'context': shared.fp(attempt / 'RUN.json')}
            if mode == 'owned':
                text = Path(result['log']['path']).read_text()
                prefix = registry['owned_audit_marker_prefix']
                normalized = '\n'.join('P26_CELL00_AUDIT_' + line[len(prefix):]
                    if line.startswith(prefix) else line for line in text.splitlines())
                accepted['owned'] = shared.parse_owned(normalized, module)
                accepted['audit_source'] = shared.fp(audit)
            shared.write_json(folder / 'ACCEPTED_STEP.json', accepted)
            record = {'module': module, 'mode': mode, 'receipt': shared.fp(folder / 'ACCEPTED_STEP.json')}
            records.append(record)
            print(json.dumps({'accepted': record}), flush=True)
            return record

        phase = 'reuse_five_accepted_partial_attempt_steps'
        reuse = reuse_partial_attempt(shared, retry_prior, context, inputs, registry, remember)
        shared.write_json(attempt / 'REUSED_ACCEPTED_STEPS.json', reuse)
        for previous_step in reuse['steps']:
            records.append(previous_step)
        cell00_records = [row for row in reuse['steps'] if row['mode'] != 'kernel_compatibility']
        owner_results.append({'module': cell00_records[0]['module'],
            'status': 'PASS_NORMAL_KERNEL_FULL_OWNED', 'reused': True, 'records': cell00_records})
        print(json.dumps({'reused_accepted_steps': 5, 'prior_attempt': str(retry_prior),
            'only_new_target': registry['retry']['only_target_module']}), flush=True)
        for target in targets:
            module = target['module']
            phase = module
            own_records = []
            try:
                for mode in ('normal', 'kernel', 'owned'):
                    own_records.append(step(module, mode, new_files[module]['source'], new_files[module]['audit']))
                owner_results.append({'module': module, 'status': 'PASS_NORMAL_KERNEL_FULL_OWNED',
                                      'records': own_records})
            except Exception as exc:
                # These two owners do not import each other. Preserve the
                # failed phase and allow the other independent owner to run.
                owner_results.append({'module': module, 'status': 'FAILED_STOPPED_OWNER',
                    'failed_mode': mode, 'error': f'{type(exc).__name__}: {exc}', 'records': own_records,
                    'partial_object': shared.fp(objects / shared.module_path(module, '.olean'))
                        if (objects / shared.module_path(module, '.olean')).exists() else None})
            shared.write_json(attempt / 'owners' / (module.split('.')[-1] + '.json'), owner_results[-1])
        unchanged()
        passed = all(r['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED' for r in owner_results)
        result = {'status': 'PASS_ARCHIVE_BRIDGES' if passed else 'PARTIAL_FAILED_OWNER',
            'owner_results': owner_results, 'records': records, 'context': shared.fp(attempt / 'RUN.json'),
            'mixed_context_compatibility_passed': True,
            'compatibility_evidence': 'two_accepted_receipts_reused_in_the_same_byte_context',
            'reused_steps': shared.fp(attempt / 'REUSED_ACCEPTED_STEPS.json'),
            'new_proof_commands_executed': sum(1 for row in records if not row.get('reused')),
            'P2_6_complete_claimed': False}
        shared.write_json(attempt / 'RESULT.json', result)
        print(json.dumps({'status': result['status'], 'result': str(attempt / 'RESULT.json')}), flush=True)
        return 0 if passed else 1
    except Exception as exc:
        shared.write_json(attempt / 'RESULT.json', {'status': 'FAILED_STOPPED_STAGE', 'phase': phase,
            'error': f'{type(exc).__name__}: {exc}', 'owner_results': owner_results,
            'accepted_steps': records, 'P2_6_complete_claimed': False})
        print(f'FAILED_STOPPED_STAGE: {exc}; {attempt / "RESULT.json"}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
