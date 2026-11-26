#!/usr/bin/env python3
"""Verify only Cell01 row000's original-floor bridge with exact accepted suppliers.

No supplier compilation or kernel replay occurs. All Lean sources and the
complete serialized/environment ownership audit are supplied as fixed files.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import sys
import uuid

TARGET = 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'
PREFIX = 'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix'
RECURRENCE = 'ImbalancedChen.P2Winner9HomogeneousRecurrence'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def same(a, b):
    return all(a[key] == b[key] for key in ('sha256', 'bytes'))


def member_path(root, member):
    member = str(member)
    path = Path(member)
    need(member and not path.is_absolute() and '..' not in path.parts and path.parts,
         'Unsafe archive member')
    return Path(root) / path


def merge_exact(namespace, row):
    previous = namespace.get(row['module'])
    if previous is not None:
        need(same(previous['source'], row['source']) and same(previous['object'], row['object']),
             f'Conflicting accepted supplier: {row["module"]}')
    else:
        namespace[row['module']] = row


def load_helper(path, pin, name):
    data = Path(path).read_bytes()
    need(len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'],
         f'Helper fingerprint differs: {name}')
    spec = importlib.util.spec_from_file_location(name, path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    return helper


class Frozen:
    def __init__(self, shared):
        self.shared, self.files = shared, {}

    def add(self, path, pin=None, root=None):
        path = Path(path).absolute()
        root = Path(root or path.parent).resolve()
        actual = self.shared.require_pin(path, pin or self.shared.fp(path), root)
        previous = self.files.get(str(path))
        need(previous is None or same(previous, actual), f'Input changed during staging: {path}')
        self.files[str(path)] = {**actual, 'root': str(root)}
        return actual

    def unchanged(self):
        for row in self.files.values():
            self.shared.require_pin(row['path'], row, row['root'])


class AcceptedExport:
    """Resolve immutable exported references without depending on old cloud paths."""
    def __init__(self, root, manifest_path, pin, frozen):
        self.root, self.frozen = Path(root), frozen
        self.manifest_pin = frozen.add(manifest_path, pin)
        self.manifest = frozen.shared.read_json(manifest_path)
        self.by_member, self.by_original = {}, {}
        for row in self.manifest['files']:
            member = row['archive_member']
            need(member not in self.by_member, 'Duplicate exported evidence member')
            self.by_member[member] = row
            self.by_original.setdefault(row['path'], []).append(row)
            frozen.add(member_path(self.root, member), row, self.root)

    def member(self, ref):
        row = self.by_member[ref['archive_member']]
        need(same(row, ref), 'Exported reference differs from pinned file inventory')
        return self.frozen.add(member_path(self.root, ref['archive_member']), ref, self.root)

    def original(self, ref):
        matches = [row for row in self.by_original.get(ref['path'], []) if same(row, ref)]
        need(len(matches) == 1, f'No unique pinned original reference: {ref["path"]}')
        return self.member(matches[0])

    def read_member(self, ref):
        return self.frozen.shared.read_json(self.member(ref)['path'])

    def read_original(self, ref):
        return self.frozen.shared.read_json(self.original(ref)['path'])


def verify_p3(export, owned_helper):
    """Check the existing 66 proof receipts by reading them; execute no Lean."""
    manifest, shared = export.manifest, export.frozen.shared
    need(manifest['status'] == 'succeeded' and manifest['accepted_targets'] == 22 and
         manifest['accepted_proof_commands'] == 66 and manifest['owned_declarations'] == 313,
         'Unexpected accepted P3 owner export')
    run_member = 'verification/' + manifest['successful_attempt'] + '/RUN.json'
    run = export.read_member(export.by_member[run_member])
    success = export.read_member(export.by_member[run_member.replace('/RUN.json', '/SUCCESS.json')])
    need(success['status'] == 'succeeded' and success['frozen_inputs_unchanged'] and
         success['accepted_targets'] == 22 and len(success['records']) == 66,
         'P3 accepted run was not complete')
    need(all(success.get(key) == value for key, value in run.items()), 'P3 success/context differs')
    need(shared.LEAN_COMMIT in run['lean_version'] and run['mathlib_commit'] == shared.MATHLIB_COMMIT,
         'P3 runtime source pins differ')
    need(run['pending_supplier_kernel'] == [RECURRENCE] and not run['full_supplier_kernel_closed'],
         'Original P3 pending-kernel history was changed')
    supplier = export.read_original(run['supplier_manifest'])
    installation = export.read_original(run['supplier_installation'])
    need(len(supplier['suppliers']) == supplier['existing_supplier_count'] == 398,
         'Expected 398 historical P3 suppliers')
    need(len(installation['entries']) == 796 and installation['suppliers_recompiled'] is False,
         'Unexpected P3 supplier installation')
    installed = {(row['module'], row['kind']): row for row in installation['entries']}
    for row in supplier['suppliers']:
        for kind in ('source', 'object'):
            need(same(installed[(row['module'], kind)]['source'], row[kind]) and
                 same(installed[(row['module'], kind)]['installed'], row[kind]),
                 'P3 installed supplier pin differs')
    receipt_pins = {(row['module'], row['mode']): row['receipt'] for row in success['records']}
    need(len(receipt_pins) == 66, 'Duplicate P3 accepted proof step')
    count = 0
    for module, owner in manifest['owners'].items():
        need(module != TARGET and set(owner['steps']) == {'normal', 'kernel', 'owned'},
             'Wrong P3 accepted target set')
        export.member(owner['source'])
        export.member(owner['object'])
        for mode in ('normal', 'kernel', 'owned'):
            ref = owner['steps'][mode]
            result = export.read_member(ref)
            need(same(receipt_pins[(module, mode)], ref), 'P3 success/owner receipt differs')
            need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
                 result['module'] == module and result['mode'] == mode,
                 'Unaccepted P3 proof step')
            need(all(result.get(key) == value for key, value in run.items()), 'P3 command/context differs')
            command_member = ref['archive_member'].replace(mode + '-result.json', mode + '-command.json')
            command = export.read_member(export.by_member[command_member])
            need(all(result.get(key) == value for key, value in command.items()), 'P3 command/result differs')
            need(same(result['source'], owner['source']) and same(result['object'], owner['object']),
                 'P3 owner bytes changed between phases')
            export.original(result['source'])
            export.original(result['object'])
            log = export.original(result['log'])
            argv = result['argv']
            if mode == 'normal':
                need(result['object_before'] is None and argv[0] == owner['lean_binary_path'] and
                     argv[-3:] == ['-o', result['object']['path'], module.replace('.', '/') + '.lean'] and
                     set(result['printed_axioms']) <= shared.ALLOWED_AXIOMS,
                     'P3 normal command target/axioms differ')
            else:
                need(same(result['object_before'], owner['object']), 'P3 checked object differs')
                if mode == 'kernel':
                    need(argv == [str(Path(owner['lean_binary_path']).with_name('leanchecker')),
                                  '--verbose', module], 'P3 independent kernel command differs')
                else:
                    export.original(result['audit_source'])
                    need(same(result['audit_source'], owner['audit']) and
                         argv[0] == owner['lean_binary_path'] and argv[-1] == result['audit_source']['path'],
                         'P3 owned audit command differs')
                    parsed = owned_helper.parse_owned(Path(log['path']).read_text(), module)
                    need(parsed == export.read_member(owner['owned_declarations']) and
                         parsed['owned_declaration_count'] == owner['owned_declaration_count'],
                         'P3 full owned inventory differs')
                    count += parsed['owned_declaration_count']
    need(count == 313, 'P3 total owned declaration count differs')
    return {'proof_steps': 66, 'owned_declarations': count, 'supplier_rows': supplier['suppliers'],
            'installation': installation, 'run': run, 'supplier_kernel_closed_at_original_run': False}


def verify_p1_suppliers(export):
    """Verify the accepted prefix and two historical kernel backfills, without replay."""
    manifest, shared = export.manifest, export.frozen.shared
    need(manifest['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED', 'P1 continuation export is not accepted')
    owner = manifest['new_owners'][PREFIX]
    requested = [(PREFIX, mode, owner['steps'][mode], owner) for mode in ('normal', 'kernel', 'owned')]
    for module, backfill in manifest['kernel_backfills'].items():
        requested.append((module, 'kernel', backfill['kernel_receipt'], backfill))
    need(len(requested) == 5 and set(manifest['kernel_backfills']) == set(shared.BACKFILL),
         'Unexpected P1 accepted supplier steps')
    records, contexts = [], {}
    for module, mode, receipt_ref, target in requested:
        accepted = export.read_member(receipt_ref)
        need(accepted['module'] == module and accepted['mode'] == mode and
             accepted['status'] == 'succeeded' and accepted['all_frozen_inputs_unchanged'],
             'Unaccepted P1 supplier step')
        need(same(accepted['source'], target['source']) and same(accepted['object'], target['object']),
             'P1 supplier source/object differs')
        for key in ('source', 'object', 'log', 'command_result'):
            export.original(accepted[key])
        result = export.read_original(accepted['command_result'])
        command = export.read_original(result['command'])
        need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
             result['error'] is None and not result['timed_out'] and
             all(result.get(key) == value for key, value in command.items()), 'P1 command chain differs')
        need(result['module'] == module and result['mode'] == mode and
             result['source'] == accepted['source'] and result['log'] == accepted['log'],
             'P1 proof metadata differs')
        input_ref = result['input_fingerprints']
        export.original(input_ref)
        run_member = str(Path(receipt_ref['archive_member']).parents[2] / 'RUN.json')
        context = export.read_member(export.by_member[run_member])
        contexts[run_member] = context
        need(context['input_fingerprints'] == input_ref and context['LEAN_PATH'] == result['LEAN_PATH'] and
             context['project'] == result['cwd'], 'P1 input/runtime context binding differs')
        if mode == 'normal':
            need(result['object_before'] is None and
                 result['argv'][-3:] == ['-o', accepted['object']['path'], module.replace('.', '/') + '.lean'],
                 'P1 normal target/output differs')
        elif mode == 'kernel':
            need(result['argv'] == [context['leanchecker_binary']['path'], '--verbose', module] and
                 result['object_before'] == accepted['object'], 'P1 independent kernel check differs')
        else:
            audit = export.original(result['audit_source'])
            need(same(audit, target['audit']) and result['argv'][-1] == result['audit_source']['path'] and
                 result['object_before'] == accepted['object'], 'P1 owned command differs')
            parsed = shared.parse_owned(Path(export.original(accepted['log'])['path']).read_text(), module)
            need(parsed == accepted['owned'] and parsed['count'] == target['owned_declaration_count'],
                 'P1 prefix complete owned audit differs')
        records.append({'module': module, 'mode': mode, 'receipt': export.member(receipt_ref),
                        'source': export.member(target['source']), 'object': export.member(target['object'])})
    return {'records': records, 'runtime_contexts': list(contexts.values()), 'prefix': owner}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--registry', type=Path,
                    default=Path(__file__).with_name('Cell01Row000OriginalFloor_REGISTRY.json'))
    ap.add_argument('--stage', type=Path)
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
    stage = (args.stage or Path(registry['stage'])).resolve()
    shared = load_helper(stage / 'Cell00OriginalFloor_continue.py', registry['shared_driver'], 'p26_row000_shared')
    owned_helper = load_helper(stage / 'export_cell01_row000.py', registry['owned_parser'], 'p26_row000_owned_parser')
    need(same(shared.fp(__file__), registry['driver']), 'One-owner verifier fingerprint differs')
    need(args.attempt and all(c.isalnum() or c in '_-' for c in args.attempt), 'Invalid attempt identifier')
    attempt = stage / 'attempts' / args.attempt
    attempt.mkdir(parents=True, exist_ok=False)
    phase, records = 'preflight', []
    try:
        frozen, namespace = Frozen(shared), {}
        for path, pin in [(args.registry, shared.fp(args.registry)), (Path(__file__), registry['driver']),
                (stage / 'Cell00OriginalFloor_continue.py', registry['shared_driver']),
                (stage / 'export_cell01_row000.py', registry['owned_parser'])]:
            frozen.add(path, pin)
        roots = {label: Path(path).resolve() for label, path in registry['supplier_stages'].items()}
        cell00, geometry, moment, completed = [roots[label] for label in
                                               ('cell00', 'geometry01', 'moment01', 'p3_completed')]

        def add(module, source, obj, source_pin, object_pin, origin, root):
            row = {'module': module, 'source': frozen.add(source, source_pin, root),
                   'object': frozen.add(obj, object_pin, root), 'origin': origin}
            merge_exact(namespace, row)

        p1 = AcceptedExport(cell00, stage / 'CELL00_ORIGINAL_FLOOR_EXPORT_MANIFEST.json',
                            registry['p1_export_manifest'], frozen)
        p1_verified = verify_p1_suppliers(p1)
        cell00_manifest_path = cell00 / 'MANIFEST.json'
        frozen.add(cell00_manifest_path, registry['cell00_manifest'], cell00)
        cell00_manifest = shared.read_json(cell00_manifest_path)
        pairs = {}
        for row in cell00_manifest['files']:
            if row['role'] in ('project_source', 'project_object'):
                pairs.setdefault(row['module'], {})[row['role']] = row
        need(len(pairs) == 480, 'Expected 480 cell00 suppliers')
        for module, pair in pairs.items():
            source, obj = pair['project_source'], pair['project_object']
            add(module, member_path(cell00, source['archive_path']), member_path(cell00, obj['archive_path']),
                source, obj, 'accepted_cell00', cell00)
        analytic_path = cell00 / 'HIGHER_MOMENTS_PINNED_CLOSURE.json'
        frozen.add(analytic_path, registry['analytic_pins'], cell00)
        analytic = shared.read_json(analytic_path)
        freeze_path = cell00 / 'ANALYTIC_FREEZE.json'
        frozen.add(freeze_path, registry['analytic_freeze'], cell00)
        freeze = shared.read_json(freeze_path)
        need(freeze['status'] == 'exact_accepted_suppliers_frozen' and freeze['analytic_modules'] == 224 and
             freeze['pins_sha256'] == registry['analytic_pins']['sha256'], 'Analytic freeze is not exact')
        bound = {row['module']: row for row in freeze['analytic_rows']}
        need(len(analytic['rows']) == len(bound) == 224, 'Incomplete analytic closure')
        for row in analytic['rows']:
            module = row['module']
            source = cell00 / 'analytic/sources' / shared.module_path(module, '.lean')
            obj = cell00 / 'analytic/objects' / shared.module_path(module, '.olean')
            need(bound[module]['source_sha256'] == row['source_sha256'] and
                 bound[module]['object_sha256'] == row['object_sha256'] and
                 bound[module]['frozen_source'] == str(source) and bound[module]['frozen_object'] == str(obj),
                 'Analytic row/source/object binding differs')
            add(module, source, obj, {'sha256': row['source_sha256']},
                {'sha256': row['object_sha256'], 'bytes': row['bytes']}, 'accepted_analytic', cell00)
        geometry_pin_path = stage / 'GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json'
        frozen.add(geometry_pin_path, registry['geometry_pins'], stage)
        geometry_pins = shared.read_json(geometry_pin_path)
        need(geometry_pins['module_count'] == len(geometry_pins['rows']) == 311,
             'Incomplete geometry01 accepted closure')
        for row in geometry_pins['rows']:
            need(row['normal_kernel_accepted'], 'Unaccepted geometry01 supplier')
            add(row['module'], member_path(geometry, row['source_member']),
                member_path(geometry, row['object_member']),
                {'sha256': row['source_sha256'], 'bytes': row['source_bytes']},
                {'sha256': row['object_sha256'], 'bytes': row['bytes']}, 'accepted_geometry01', geometry)
        frozen.add(member_path(geometry, registry['geometry_original_input']['archive_member']),
                   registry['geometry_original_input'], geometry)
        moment_manifest_path = stage / 'Moment01_SUPPLIERS.json'
        frozen.add(moment_manifest_path, registry['moment_manifest'], stage)
        moment_manifest = shared.read_json(moment_manifest_path)
        need(moment_manifest['status'] == 'EXACT_SOURCE_OBJECT_NORMAL_KERNEL_RECEIPTS_RECHECKED' and
             len(moment_manifest['accepted']) == moment_manifest['project_closure_count'] == 88,
             'Incomplete accepted moment01 closure')
        for member, pin in moment_manifest['all_archive_members'].items():
            frozen.add(member_path(moment, member), pin, moment)
        for row in moment_manifest['accepted']:
            add(row['module'], member_path(moment, row['source']['archive_member']),
                member_path(moment, row['object']['archive_member']), row['source'], row['object'],
                'accepted_moment01', moment)
        need(len(namespace) == 1088, 'Unexpected base supplier overlap')
        p3 = AcceptedExport(completed, completed / 'CELL01_ROW000_EXPORT_MANIFEST.json',
                            registry['p3_export_manifest'], frozen)
        p3_verified = verify_p3(p3, owned_helper)
        for row in p3_verified['supplier_rows']:
            need(row['module'] in namespace and same(namespace[row['module']]['source'], row['source']) and
                 same(namespace[row['module']]['object'], row['object']),
                 f'P3 accepted dependency context differs: {row["module"]}')
        for module, row in p3.manifest['owners'].items():
            add(module, member_path(completed, row['source']['archive_member']),
                member_path(completed, row['object']['archive_member']), row['source'], row['object'],
                'accepted_P3_row000_owner', completed)
        prefix = p1_verified['prefix']
        add(PREFIX, member_path(cell00, prefix['source']['archive_member']),
            member_path(cell00, prefix['object']['archive_member']), prefix['source'], prefix['object'],
            'accepted_P1_HigherMomentsPrefix', cell00)
        need(len(namespace) == registry['canonical_supplier_modules'] == 1111 and TARGET not in namespace,
             'Unexpected single-owner supplier count')
        need(not any(module.endswith(('ArchiveCore', 'ArchivePackedInputs')) for module in namespace),
             'Unrelated Archive closure entered the one-owner stage')
        for row in p1_verified['records']:
            expected = namespace[row['module']]
            need(same(row['source'], expected['source']) and same(row['object'], expected['object']),
                 'P1 accepted supplier bytes differ from canonical namespace')
        addendum_path = stage / 'SUPPLIER_KERNEL_COMPLETION.json'
        frozen.add(addendum_path, registry['supplier_kernel_completion'], stage)
        addendum = shared.read_json(addendum_path)
        need(addendum['module'] == RECURRENCE and addendum['supplier_kernel_closed_in_combined_evidence'] and
             addendum['original_P3_records_unchanged'] and not addendum['full_supplier_kernel_closed_at_original_P3_run'] and
             addendum['remaining_pending_supplier_kernel_modules'] == [], 'Invalid Recurrence evidence addendum')
        for key in ('source', 'object'):
            need(same(addendum[key], namespace[RECURRENCE][key]), 'Recurrence exact-byte join differs')
        p1.member(addendum['P1_kernel_receipt'])
        p1.member(addendum['P1_kernel_result'])
        p1.member(addendum['P1_kernel_log'])
        p3.member(addendum['P3_installation_snapshot'])

        project, objects = attempt / 'project', attempt / 'objects'
        project.mkdir()
        objects.mkdir()
        union = shared.copy_project_union(objects, {module: row['object'] for module, row in namespace.items()})
        for row in union:
            frozen.add(row['path'], row, attempt)
            frozen.add(row['origin'], row, Path(row['origin']).parent)
        target = registry['target']
        need(target['module'] == TARGET, 'Unexpected new owner')
        held = p3.manifest['held_targets']
        need(len(held) == 1 and held[0]['module'] == TARGET and same(held[0]['source'], target['source']),
             'New source differs from the held original-floor bridge')
        source = project / shared.module_path(TARGET, '.lean')
        audit = attempt / 'audits' / (TARGET.split('.')[-1] + '.lean')
        for original, destination, pin in [
                (stage / 'new-sources' / shared.module_path(TARGET, '.lean'), source, target['source']),
                (stage / 'audits' / audit.name, audit, target['audit'])]:
            frozen.add(original, pin, stage)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, destination)
            frozen.add(destination, pin, attempt)
        for module, path in [(module, row['source']['path']) for module, row in namespace.items()] + [(TARGET, source)]:
            imports = re.findall(r'^import\s+(ImbalancedChen\.[A-Za-z0-9_.]+)', Path(path).read_text(), re.M)
            need(all(name in namespace for name in imports), f'Missing exact project import: {module}')

        external_pins_path = stage / 'Cell00OriginalFloor_EXTERNAL_PINS.json'
        frozen.add(external_pins_path, registry['external_pins'], stage)
        packages = {'goldbach': (args.goldbach or args.mathlib.parent / 'goldbach').resolve(),
                    'LeanArchitect': (args.leanarchitect or args.mathlib.parent / 'LeanArchitect').resolve()}
        external = shared.external_inputs(shared.read_json(external_pins_path), packages)
        for row in external['files']:
            frozen.add(row['path'], row, row['root'])
        prior_input_member = ('attempts/' + p1.manifest['successful_attempt'] + '/INPUT_FINGERPRINTS.json')
        prior_inputs = p1.read_member(p1.by_member[prior_input_member])
        def external_signature(rows):
            return {row['module']: (row['source']['sha256'], row['source']['bytes'],
                    row['object']['sha256'], row['object']['bytes'],
                    sorted((Path(side['path']).name, side['sha256'], side['bytes'])
                           for side in row.get('sidecars', []))) for row in rows}
        need(external_signature(external['modules']) == external_signature(prior_inputs['external_modules']),
             'Existing external object context differs from accepted P1 prefix suppliers')
        runtime_roots = shared.package_roots(args.mathlib) + external['object_roots']
        lean, checker = args.lean_bin.resolve() / 'lean', args.lean_bin.resolve() / 'leanchecker'
        frozen.add(lean)
        frozen.add(checker)
        env = os.environ.copy()
        env.pop('LEAN_SRC_PATH', None)
        env.pop('LEAN_SYSROOT', None)
        env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
        env['LEAN_PATH'] = os.pathsep.join(str(path) for path in [objects, *runtime_roots])
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
            need(revision == pin, f'External Git source pin differs: {name}')
            revisions[name] = revision
        for old in p1_verified['runtime_contexts']:
            need(old['lean_version'] == version_text and old['mathlib_commit'] == shared.MATHLIB_COMMIT and
                 same(old['lean_binary'], shared.fp(lean)) and same(old['leanchecker_binary'], shared.fp(checker)),
                 'P1 accepted supplier runtime differs')
        shared.write_json(attempt / 'INPUT_FINGERPRINTS.json', {'files': list(frozen.files.values()),
            'canonical_modules': namespace, 'project_object_union': union, 'external_modules': external['modules'],
            'P3_proof_steps_reused': 66, 'P3_owned_declarations_reused': 313,
            'P1_supplier_steps_reused': p1_verified['records'], 'supplier_kernel_addendum': shared.fp(addendum_path)})
        input_pin = shared.fp(attempt / 'INPUT_FINGERPRINTS.json')
        context = {'schema': 'p26_cell01_row000_original_floor_attempt_v1', 'attempt': args.attempt,
            'stage': str(stage), 'project': str(project), 'LEAN_PATH': env['LEAN_PATH'],
            'target': TARGET, 'registry': shared.fp(args.registry), 'driver': shared.fp(__file__),
            'lean_version': version_text, 'lean_binary': shared.fp(lean), 'leanchecker_binary': shared.fp(checker),
            'package_revisions': revisions, 'inputs': input_pin, 'canonical_project_suppliers': 1111,
            'old_supplier_normal_recompilation': False, 'old_supplier_kernel_replay': False,
            'external_supplier_bytes_match_accepted_P1_prefix_context': True,
            'cloud_lean_source_generation': False, 'full_supplier_kernel_closed_at_original_P3_run': False,
            'historical_P3_records_unchanged': True, 'supplier_kernel_closed_by_separate_same_byte_evidence': True,
            'cell01_rows_in_this_owner': [0], 'remaining_cell01_rows_outside_this_owner': 143,
            'P2_6_complete_claimed': False}
        shared.write_json(attempt / 'RUN.json', context)
        print(json.dumps({'preflight': 'passed', 'canonical_suppliers': 1111, 'target': TARGET,
                          'new_proof_commands': 3, 'supplier_proof_commands': 0}), flush=True)
        obj = objects / shared.module_path(TARGET, '.olean')
        flags = ['-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
        for mode in ('normal', 'kernel', 'owned'):
            phase = mode
            frozen.unchanged()
            before = shared.fp(obj) if obj.exists() else None
            if mode == 'normal':
                need(before is None, 'Refusing an existing owner normal compilation')
                argv = [str(lean), *flags, '-o', str(obj), str(source.relative_to(project))]
            elif mode == 'kernel':
                need(before is not None, 'Missing new owner object')
                argv = [str(checker), '--verbose', TARGET]
            else:
                need(before is not None, 'Missing owned-audit target object')
                argv = [str(lean), *flags, str(audit)]
            folder = attempt / 'steps' / mode
            print(json.dumps({'running': {'module': TARGET, 'mode': mode}}), flush=True)
            result = shared.run_command(argv, project, env, folder, args.wall_seconds,
                {'module': TARGET, 'mode': mode, 'source': shared.fp(source), 'object_before': before,
                 'audit_source': shared.fp(audit), 'input_fingerprints': input_pin})
            frozen.unchanged()
            after = frozen.add(obj, root=attempt)
            need(before is None or same(before, after), 'New owner object changed during checking')
            sidecars = []
            for output in (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir')):
                if output.exists():
                    sidecars.append(frozen.add(output, root=attempt))
            accepted = {'module': TARGET, 'mode': mode, 'status': 'succeeded', 'source': shared.fp(source),
                'object': after, 'object_sidecars': sidecars, 'command_result': shared.fp(folder / 'result.json'),
                'log': result['log'], 'all_frozen_inputs_unchanged': True, 'context': shared.fp(attempt / 'RUN.json')}
            if mode == 'owned':
                owned = owned_helper.parse_owned(Path(result['log']['path']).read_text(), TARGET)
                shared.write_json(folder / 'owned-declarations.json', owned)
                accepted.update({'audit_source': shared.fp(audit),
                    'owned_declarations': shared.fp(folder / 'owned-declarations.json'),
                    'owned_declaration_count': owned['owned_declaration_count'], 'axioms_union': owned['axioms_union']})
            shared.write_json(folder / 'ACCEPTED_STEP.json', accepted)
            record = {'module': TARGET, 'mode': mode, 'receipt': shared.fp(folder / 'ACCEPTED_STEP.json')}
            records.append(record)
            print(json.dumps({'accepted': record}), flush=True)
        frozen.unchanged()
        result = {'status': 'PASS_CELL01_ROW000_ORIGINAL_FLOOR', 'module': TARGET, 'records': records,
            'context': shared.fp(attempt / 'RUN.json'), 'source': shared.fp(source), 'object': shared.fp(obj),
            'cell01_row': 0, 'remaining_cell01_rows_outside_this_owner': 143,
            'supplier_proof_commands': 0, 'new_proof_commands': 3, 'P2_6_complete_claimed': False}
        shared.write_json(attempt / 'RESULT.json', result)
        print(json.dumps({'status': result['status'], 'result': str(attempt / 'RESULT.json')}), flush=True)
        return 0
    except Exception as exc:
        shared.write_json(attempt / 'RESULT.json', {'status': 'FAILED_STOPPED', 'phase': phase,
            'error': f'{type(exc).__name__}: {exc}', 'accepted_steps': records,
            'supplier_proof_commands': 0, 'P2_6_complete_claimed': False})
        print(f'FAILED_STOPPED: {exc}; {attempt / "RESULT.json"}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
