#!/usr/bin/env python3
"""Verify the two cell00 continuation owners in an isolated P1 attempt.

The stage supplies immutable sources/, objects/, analytic/{sources,objects},
new-sources/ImbalancedChen, and audits/.  This driver copies supplied Lean
files without generating or editing Lean. It never builds a supplier module.
"""
import argparse
import datetime
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell00')
BACKFILL = ('ImbalancedChen.P2OriginalSaving19CharacterCore00',
            'ImbalancedChen.P2Winner9HomogeneousRecurrence')
TARGETS = ('ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix',
           'ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge')
REQUIRED_PACKAGES = ('LeanSearchClient', 'Qq', 'aesop', 'batteries',
                     'importGraph', 'plausible', 'proofwidgets')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
EXTERNAL_COMMITS = {'goldbach': '09b97db5764ade1246bfb77206baa1b124760958',
                    'LeanArchitect': '78dd66840d3efe8c824c699fc03381cec817c271'}


class VerificationError(RuntimeError):
    pass


def need(condition, message):
    if not condition:
        raise VerificationError(message)


def fp(path):
    path = Path(path)
    digest = hashlib.sha256()
    size = 0
    with path.open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            size += len(chunk)
            digest.update(chunk)
    return {'path': str(path), 'bytes': size, 'sha256': digest.hexdigest()}


def require_pin(path, expected, root):
    path, root = Path(path), Path(root).resolve()
    need(path.is_file(), f'Missing pinned file: {path}')
    need(path.resolve().is_relative_to(root), f'File escapes isolated root: {path}')
    need(path.resolve() == path.absolute(), f'Frozen supplier cannot be a symlink: {path}')
    actual = fp(path)
    need(actual['sha256'] == expected['sha256'], f'SHA256 mismatch: {path}')
    if 'bytes' in expected:
        need(actual['bytes'] == expected['bytes'], f'Size mismatch: {path}')
    return actual


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as output:
        output.write(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def package_roots(mathlib):
    """P1 places mathlib's dependencies beside mathlib, not inside it."""
    mathlib = Path(mathlib).resolve()
    roots = [mathlib / '.lake/build/lib/lean']
    for name in REQUIRED_PACKAGES:
        roots.append(mathlib.parent / name / '.lake/build/lib/lean')
    for path in roots:
        need(path.is_dir(), f'Missing required package objects: {path}')
    cli = mathlib.parent / 'Cli/.lake/build/lib/lean'
    if cli.is_dir():
        roots.append(cli)
    return roots


def external_inputs(pins, packages):
    """Bind needed external sources and snapshot their already-built objects."""
    need(pins['package_pins'] == EXTERNAL_COMMITS, 'External package pin mismatch')
    need(pins['module_count'] == len(pins['rows']) > 0, 'Incomplete external source pins')
    roots = {name: Path(path).resolve() for name, path in packages.items()}
    need(set(roots) == set(EXTERNAL_COMMITS), 'Unexpected external package provider')
    objects = {name: (path / '.lake/build/lib/lean').resolve() for name, path in roots.items()}
    for path in objects.values():
        need(path.is_dir(), f'Missing accepted external object root: {path}')
        need(not (path / 'ImbalancedChen').exists(),
             f'External provider contains a project-object fallback: {path}')
    files, modules, seen = [], [], set()
    for row in pins['rows']:
        module, package = row['module'], row['package']
        need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*', module),
             'Invalid external module name')
        need(module not in seen and package in roots, 'Duplicate or unknown external supplier')
        need((package == 'LeanArchitect' and module.split('.')[0] == 'Architect') or
             (package == 'goldbach' and module.split('.')[0] in
              {'MathlibNt', 'AnalyticNumberTheory', 'PrimeNumberTheoremAnd'}),
             f'External module/provider mismatch: {module}')
        seen.add(module)
        relative = module.replace('.', '/')
        source = require_pin(roots[package] / (relative + '.lean'),
            {'sha256': row['source_sha256'], 'bytes': row['bytes']}, roots[package])
        obj = objects[package] / (relative + '.olean')
        object_pin = require_pin(obj, fp(obj), objects[package])
        files.extend([{**source, 'root': str(roots[package]), 'role': 'external_source'},
                      {**object_pin, 'root': str(objects[package]), 'role': 'external_object'}])
        sidecars = []
        for extra in (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir')):
            if extra.exists():
                actual = require_pin(extra, fp(extra), objects[package])
                files.append({**actual, 'root': str(objects[package]), 'role': 'external_sidecar'})
                sidecars.append(actual)
        historical = row.get('historical_p3_object_sha256', [])
        modules.append({'module': module, 'package': package, 'source': source,
            'object': object_pin, 'sidecars': sidecars,
            'object_pin_basis': 'current_existing_package_object_before_execution',
            'historical_p3_object_sha256': historical,
            'matches_historical_p3_object': object_pin['sha256'] in historical if historical else None,
            'historical_P1_object_pin_claimed': False})
    return {'object_roots': [objects[name] for name in EXTERNAL_COMMITS],
            'files': files, 'modules': modules}


def run_command(argv, cwd, env, folder, wall_seconds, metadata=None):
    """A failed/timed-out command always leaves a receipt and stops its caller."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=False)
    log = folder / 'output.log'
    command = {**(metadata or {}), 'argv': [str(x) for x in argv],
               'cwd': str(cwd), 'LEAN_PATH': env.get('LEAN_PATH'),
               'wall_limit_seconds': wall_seconds, 'started_unix': time.time()}
    write_json(folder / 'command.json', command)
    child, error, timed_out, code = None, None, False, None
    with log.open('xb') as output:
        try:
            child = subprocess.Popen(argv, cwd=cwd, env=env, stdout=output,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            code = child.wait(timeout=wall_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGKILL)
            code = child.wait()
            error = f'Wall limit exceeded: {wall_seconds}s'
        except BaseException as exc:
            error = f'{type(exc).__name__}: {exc}'
            if child is not None and child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait()
    result = {**command, 'finished_unix': time.time(), 'exit_code': code,
              'timed_out': timed_out, 'error': error,
              'status': 'succeeded' if code == 0 and error is None else 'failed',
              'command': fp(folder / 'command.json'), 'log': fp(log)}
    write_json(folder / 'result.json', result)
    need(result['status'] == 'succeeded', f'Command failed; see {folder / "result.json"}')
    return result


def parse_owned(text, module):
    buckets = {'INVENTORY': [], 'DECL': [], 'COMPLETE': []}
    for line in text.splitlines():
        for marker, bucket in buckets.items():
            prefix = 'P26_CELL00_AUDIT_' + marker + ' '
            if line.startswith(prefix):
                bucket.append(json.loads(line[len(prefix):]))
    need(len(buckets['INVENTORY']) == len(buckets['COMPLETE']) == 1,
         'Missing or duplicate owned inventory/completion marker')
    inventory, complete = buckets['INVENTORY'][0], buckets['COMPLETE'][0]
    names = inventory['names']
    declarations = buckets['DECL']
    need(inventory['module'] == complete['module'] == module, 'Owned audit module mismatch')
    need(names and len(names) == len(set(names)), 'Empty or repeated owned names')
    need(sorted(row['name'] for row in declarations) == sorted(names),
         'Owned declaration inventory is incomplete')
    need(complete['count'] == len(names), 'Owned completion count mismatch')
    for row in declarations:
        need(row['module'] == module and row['type'] and '⋯' not in row['type'],
             f'Missing or truncated owned type: {row.get("name")}')
        need(not row['unsafe'] and not row['partial'] and not row['axiom'],
             f'Unsafe/partial/new axiom declaration: {row["name"]}')
        need(set(row['axioms']) <= ALLOWED_AXIOMS, f'Forbidden axiom: {row["name"]}')
    return {'module': module, 'count': len(names), 'inventory': inventory,
            'declarations': declarations,
            'axioms_union': sorted({ax for row in declarations for ax in row['axioms']})}


def module_path(module, suffix):
    need(re.fullmatch(r'ImbalancedChen(?:\.[A-Za-z0-9_]+)+', module), 'Invalid module name')
    return Path(module.replace('.', '/') + suffix)


def copy_project_union(objects, suppliers):
    """Lean selects the first root directory for a namespace; stage it once."""
    copied = []
    for module, expected in sorted(suppliers.items()):
        source = Path(expected['path'])
        need(fp(source)['sha256'] == expected['sha256'], f'Supplier changed: {module}')
        destination = objects / module_path(module, '.olean')
        pairs = [(source, destination, expected)]
        for suffix in ('.server', '.private'):
            extra = Path(str(source) + suffix)
            if extra.exists():
                pairs.append((extra, Path(str(destination) + suffix), fp(extra)))
        if source.with_suffix('.ir').exists():
            pairs.append((source.with_suffix('.ir'), destination.with_suffix('.ir'), fp(source.with_suffix('.ir'))))
        for original, target, pin in pairs:
            target.parent.mkdir(parents=True, exist_ok=True)
            need(not target.exists(), f'Object union collision: {target}')
            try:
                os.link(original, target)
                method = 'hardlink'
            except OSError as exc:
                if exc.errno != errno.EXDEV:
                    raise
                shutil.copyfile(original, target)
                method = 'copy_across_filesystems'
            actual = require_pin(target, pin, objects)
            copied.append({**actual, 'module': module, 'origin': str(original), 'method': method})
    return copied


def reuse_backfill(prior_attempt, module, source, obj, context, inputs):
    """Reuse only the successful exact-byte kernel evidence, without replay."""
    prior_attempt = Path(prior_attempt).resolve()
    stage = Path(context['stage'])
    need(prior_attempt.is_relative_to(stage / 'attempts'), 'Backfill attempt is outside this stage')
    previous = read_json(prior_attempt / 'RESULT.json')
    references = previous.get('accepted_steps', previous.get('records', []))
    matches = [r for r in references if r['module'] == module and r['mode'] == 'kernel']
    need(len(matches) == 1, f'No unique successful backfill receipt: {module}')
    accepted_ref = matches[0]['receipt']
    require_pin(accepted_ref['path'], accepted_ref, prior_attempt)
    accepted = read_json(accepted_ref['path'])
    need(accepted['status'] == 'succeeded' and accepted['all_frozen_inputs_unchanged'],
         f'Unaccepted prior backfill: {module}')
    for key, expected in [('source', fp(source)), ('object', fp(obj))]:
        need(all(accepted[key][k] == expected[k] for k in ('sha256', 'bytes')),
             f'Backfill {key} differs: {module}')
    command_ref = accepted['command_result']
    require_pin(command_ref['path'], command_ref, prior_attempt)
    command_result = read_json(command_ref['path'])
    need(command_result['status'] == 'succeeded' and command_result['exit_code'] == 0,
         'Prior kernel command did not succeed')
    for key in ('command', 'log'):
        require_pin(command_result[key]['path'], command_result[key], prior_attempt)
    need(command_result['log'] == accepted['log'], 'Prior kernel log binding differs')
    old_context = read_json(prior_attempt / 'RUN.json')
    need(command_result['argv'] == [old_context['leanchecker_binary']['path'], '--verbose', module],
         'Prior command is not the requested independent kernel replay')
    need(command_result['LEAN_PATH'] == old_context['LEAN_PATH'], 'Prior command/context path mismatch')
    for key in ('lean_version', 'mathlib_commit', 'package_object_roots'):
        need(old_context[key] == context[key], f'Backfill runtime context differs: {key}')
    for key in ('lean_binary', 'leanchecker_binary'):
        need(all(old_context[key][k] == context[key][k] for k in ('sha256', 'bytes', 'path')),
             f'Backfill runtime binary differs: {key}')
    for package in EXTERNAL_COMMITS:
        need(all(old_context['external_packages'][package][key] ==
                 context['external_packages'][package][key] for key in ('path', 'commit')),
             f'Backfill external package differs: {package}')
    old_input_ref = command_result['input_fingerprints']
    require_pin(old_input_ref['path'], old_input_ref, prior_attempt)
    need(old_input_ref == old_context['input_fingerprints'], 'Prior input/context binding differs')
    old_inputs = read_json(old_input_ref['path'])
    roots = [stage / name for name in ('sources', 'objects', 'analytic/sources', 'analytic/objects')]
    manifests = {stage / name for name in ('MANIFEST.json', 'HIGHER_MOMENTS_PINNED_CLOSURE.json',
                                         'ANALYTIC_FREEZE.json')}
    def baseline(data):
        return {row['path']: (row['bytes'], row['sha256']) for row in data['files']
                if Path(row['path']) in manifests or
                any(Path(row['path']).is_relative_to(root) for root in roots)}
    need(baseline(old_inputs) == baseline(inputs) and len(baseline(inputs)) >= 1408,
         'Backfill project supplier byte context differs')
    def external(data):
        return {row['path']: (row['bytes'], row['sha256']) for row in data['external_files']}
    need(external(old_inputs) == external(inputs), 'Backfill external object/source byte context differs')
    return {'module': module, 'mode': 'kernel', 'status': 'succeeded', 'reused': True,
            'source': fp(source), 'object': fp(obj), 'receipt': accepted_ref,
            'previous_result': fp(prior_attempt / 'RESULT.json'),
            'previous_run': fp(prior_attempt / 'RUN.json'), 'previous_inputs': old_input_ref,
            'same_logical_source_object_runtime_context': True,
            'search_path_replaced_by_equivalent_single_project_namespace': True}


def freeze_inputs(stage, verifier, pins_path, attempt):
    frozen = {}
    def add(path, pin):
        actual = require_pin(path, pin, stage)
        frozen[str(path)] = actual
        return actual

    manifest_path = stage / 'MANIFEST.json'
    add(manifest_path, verifier['cell00_manifest'])
    add(pins_path, verifier['analytic_pins'])
    suppliers, pins = read_json(manifest_path), read_json(pins_path)
    freeze_path = stage / 'ANALYTIC_FREEZE.json'
    add(freeze_path, fp(freeze_path))
    freeze = read_json(freeze_path)
    need(freeze['status'] == 'exact_accepted_suppliers_frozen', 'Analytic freeze did not succeed')
    need(freeze['pins_sha256'] == verifier['analytic_pins']['sha256'] and
         freeze['cell00_manifest_sha256'] == verifier['cell00_manifest']['sha256'],
         'Analytic freeze is bound to different supplier manifests')
    need(freeze['analytic_modules'] == len(freeze['analytic_rows']) == 224,
         'Incomplete analytic freeze inventory')
    need(freeze['proof_sources_generated'] is False and freeze['accepted_modules_recompiled'] is False,
         'Analytic freeze changed the accepted supplier boundary')
    freeze_rows = {row['module']: row for row in freeze['analytic_rows']}
    need(len(freeze_rows) == 224, 'Duplicate analytic freeze module')
    rows = [row for row in suppliers['files']
            if row['role'] in ('project_source', 'project_object')]
    need(len(rows) == 960 and suppliers['project_modules'] == 480,
         'Expected the pinned 480-module cell00/Q96 bundle')
    need(sorted(suppliers['normal_only_modules']) == sorted(BACKFILL),
         'Unexpected normal-only supplier boundary')
    known_objects = {}
    for row in rows:
        member = Path(row['archive_path'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe archive member')
        actual = add(stage / member, row)
        if row['role'] == 'project_object':
            known_objects[row['module']] = actual
    need(pins['module_count'] == len(pins['rows']) == 224, 'Expected 224 analytic pins')
    need(set(freeze_rows) == {row['module'] for row in pins['rows']},
         'Analytic freeze module inventory differs from strict pins')
    for row in pins['rows']:
        module = row['module']
        need(module not in known_objects, f'Duplicate supplier namespace: {module}')
        frozen_row = freeze_rows[module]
        for key in ('source_sha256', 'object_sha256', 'originalpath', 'bytes'):
            need(frozen_row[key] == row[key], f'Analytic freeze fingerprint differs: {module}, {key}')
        source_path = stage / 'analytic/sources' / module_path(module, '.lean')
        object_path = stage / 'analytic/objects' / module_path(module, '.olean')
        need(frozen_row['frozen_source'] == str(source_path) and
             frozen_row['frozen_object'] == str(object_path),
             f'Analytic freeze points outside expected isolated paths: {module}')
        add(source_path,
            {'sha256': row['source_sha256']})
        known_objects[module] = add(object_path,
            {'sha256': row['object_sha256'], 'bytes': row['bytes']})
    need(len(known_objects) == 704, 'Supplier object inventory is not unique')
    found = {str(p) for root in (stage / 'objects', stage / 'analytic/objects')
             for p in root.rglob('*.olean')}
    need(found == {row['path'] for row in known_objects.values()},
         'Unexpected or missing project .olean in a supplier object root')
    sidecars = []
    for row in known_objects.values():
        obj = Path(row['path'])
        for extra in (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir')):
            if extra.exists():
                actual = add(extra, fp(extra))
                sidecars.append({**actual, 'historical_pin_available': False})
    targets = {row['module']: row for row in verifier['targets']}
    need(set(targets) == set(TARGETS), 'Unexpected new target list')
    new_files = {}
    for module in TARGETS:
        row = targets[module]
        source = stage / 'new-sources' / module_path(module, '.lean')
        audit = stage / 'audits' / row['audit_file']
        add(source, row['source'])
        add(audit, row['audit'])
        source_copy = attempt / 'project' / module_path(module, '.lean')
        audit_copy = attempt / 'audits' / row['audit_file']
        for original, copy, pin in ((source, source_copy, row['source']),
                                    (audit, audit_copy, row['audit'])):
            copy.parent.mkdir(parents=True, exist_ok=True)
            need(not copy.exists(), f'Attempt file already exists: {copy}')
            shutil.copyfile(original, copy)
            add(copy, pin)
        new_files[module] = {'source': source_copy, 'audit': audit_copy}
    return frozen, known_objects, new_files, sidecars


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--lean-bin', type=Path,
                    default=Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin'))
    ap.add_argument('--mathlib', type=Path,
                    default=Path('/workspace/blue-member-build/.lake/packages/mathlib'))
    ap.add_argument('--goldbach', type=Path)
    ap.add_argument('--leanarchitect', type=Path)
    ap.add_argument('--reuse-backfill-attempt', type=Path, required=True)
    ap.add_argument('--analytic-pins', type=Path)
    ap.add_argument('--verifier', type=Path,
                    default=Path(__file__).with_name('Cell00OriginalFloor_VERIFIER.json'))
    ap.add_argument('--wall-seconds', type=int, default=1800)
    ap.add_argument('--rss-gib', type=int, default=24)
    ap.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime(
        '%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8])
    args = ap.parse_args()
    need(re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt), 'Invalid attempt identifier')
    need(args.wall_seconds > 0 and args.rss_gib > 0, 'Invalid resource limit')
    stage = args.stage.resolve()
    need(stage.is_dir(), f'Missing stage: {stage}')
    attempt = stage / 'attempts' / args.attempt
    attempt.mkdir(parents=True, exist_ok=False)
    records, current = [], None
    try:
        verifier = read_json(args.verifier)
        need(fp(__file__)['sha256'] == verifier['driver']['sha256'], 'Driver SHA256 mismatch')
        pins_path = args.analytic_pins or stage / 'HIGHER_MOMENTS_PINNED_CLOSURE.json'
        frozen, suppliers, new_files, sidecars = freeze_inputs(stage, verifier, pins_path, attempt)
        external_pin_path = Path(__file__).with_name('Cell00OriginalFloor_EXTERNAL_PINS.json')
        external_pin = require_pin(external_pin_path, verifier['external_source_pins'],
                                   external_pin_path.parent)
        external_packages = {'goldbach': (args.goldbach or args.mathlib.parent / 'goldbach').resolve(),
            'LeanArchitect': (args.leanarchitect or args.mathlib.parent / 'LeanArchitect').resolve()}
        external = external_inputs(read_json(external_pin_path), external_packages)
        objects = attempt / 'objects'
        objects.mkdir()
        union = copy_project_union(objects, suppliers)
        for row in union:
            frozen[row['path']] = row
        write_json(attempt / 'PROJECT_OBJECT_UNION.json', union)
        input_path = attempt / 'INPUT_FINGERPRINTS.json'
        input_data = {'files': list(frozen.values()), 'sidecars': sidecars,
            'external_files': external['files'], 'external_modules': external['modules'],
            'external_source_pins': external_pin}
        write_json(input_path, input_data)
        lean, checker = args.lean_bin.resolve() / 'lean', args.lean_bin.resolve() / 'leanchecker'
        need(lean.is_file() and checker.is_file(), 'Missing lean/leanchecker executable')
        runtime_roots = package_roots(args.mathlib) + external['object_roots']
        env = os.environ.copy()
        env.pop('LEAN_SRC_PATH', None)
        env.pop('LEAN_SYSROOT', None)
        env['PATH'] = str(args.lean_bin.resolve()) + os.pathsep + env.get('PATH', '')
        env['LEAN_PATH'] = os.pathsep.join(str(p) for p in
            [objects, *runtime_roots])
        env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
        version_run = run_command([str(lean), '--version'], stage, env,
                                  attempt / 'runtime/lean-version', 30)
        version = Path(version_run['log']['path']).read_text().strip()
        need('4.33.0-rc1' in version and LEAN_COMMIT in version, 'Unexpected Lean version/commit')
        mathlib_run = run_command(['git', '-C', str(args.mathlib), 'rev-parse', 'HEAD'],
                                 stage, env, attempt / 'runtime/mathlib-pin', 30)
        mathlib_commit = Path(mathlib_run['log']['path']).read_text().strip()
        need(mathlib_commit == MATHLIB_COMMIT, f'Mathlib pin mismatch: {mathlib_commit}')
        external_versions = {}
        for package, package_path in external_packages.items():
            package_run = run_command(['git', '-C', str(package_path), 'rev-parse', 'HEAD'],
                stage, env, attempt / 'runtime' / (package + '-pin'), 30)
            commit = Path(package_run['log']['path']).read_text().strip()
            need(commit == EXTERNAL_COMMITS[package], f'{package} git pin mismatch: {commit}')
            external_versions[package] = {'path': str(package_path), 'commit': commit,
                                         'command_result': fp(attempt / 'runtime' / (package + '-pin') / 'result.json')}
        plan = [(module, 'kernel') for module in BACKFILL]
        plan += [(module, mode) for module in TARGETS for mode in ('normal', 'kernel', 'owned')]
        context = {'schema': 'p26_cell00_isolated_continuation_v1', 'attempt': args.attempt,
            'stage': str(stage), 'project': str(attempt / 'project'),
            'LEAN_PATH': env['LEAN_PATH'], 'lean_version': version,
            'mathlib_commit': mathlib_commit, 'mathlib_path': str(args.mathlib.resolve()),
            'package_object_roots': [str(p) for p in runtime_roots],
            'external_packages': external_versions, 'external_module_count': len(external['modules']),
            'external_source_pins': external_pin,
            'lean_binary': fp(lean), 'leanchecker_binary': fp(checker),
            'driver': fp(__file__), 'verifier': fp(args.verifier),
            'analytic_freeze': fp(stage / 'ANALYTIC_FREEZE.json'),
            'input_fingerprints': fp(input_path),
            'supplier_modules': len(suppliers), 'cloud_lean_source_generation': False,
            'project_object_union': fp(attempt / 'PROJECT_OBJECT_UNION.json'),
            'supplier_normal_recompilation': False, 'plan': plan}
        write_json(attempt / 'RUN.json', context)

        def unchanged():
            for path, pin in frozen.items():
                require_pin(path, pin, stage)
            require_pin(external_pin_path, external_pin, external_pin_path.parent)
            for pin in external['files']:
                require_pin(pin['path'], pin, pin['root'])

        for index, (module, mode) in enumerate(plan):
            current = {'module': module, 'mode': mode, 'index': index}
            unchanged()
            if module in BACKFILL:
                source = stage / 'sources' / module_path(module, '.lean')
                obj = objects / module_path(module, '.olean')
                reused = reuse_backfill(args.reuse_backfill_attempt, module, source, obj, context, input_data)
                write_json(attempt / 'reused-backfills' / (module.split('.')[-1] + '.json'), reused)
                records.append({**current, 'reused': True, 'receipt': reused['receipt']})
                print(json.dumps({'reused_backfill': module, 'receipt': reused['receipt']}), flush=True)
                continue
            else:
                source, audit = new_files[module]['source'], new_files[module]['audit']
                obj = objects / module_path(module, '.olean')
            source_pin = fp(source)
            object_before = fp(obj) if obj.exists() else None
            flags = ['-j1', f'-M{args.rss_gib * 1024}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
            if mode == 'normal':
                need(module in TARGETS and not obj.exists(), 'Refusing supplier build or object overwrite')
                obj.parent.mkdir(parents=True, exist_ok=True)
                argv = [str(lean), *flags, '-o', str(obj), str(source.relative_to(attempt / 'project'))]
            elif mode == 'kernel':
                need(obj.is_file(), f'Missing kernel target: {module}')
                argv = [str(checker), '--verbose', module]
            else:
                need(mode == 'owned' and audit is not None and obj.is_file(), 'Invalid owned audit')
                argv = [str(lean), *flags, str(audit)]
            folder = attempt / 'steps' / f'{index:02d}-{module.split(".")[-1]}-{mode}'
            result = run_command(argv, attempt / 'project', env, folder, args.wall_seconds,
                {**current, 'source': source_pin, 'object_before': object_before,
                 'audit_source': fp(audit) if audit is not None else None,
                 'input_fingerprints': fp(input_path)})
            unchanged()
            need(obj.is_file(), f'Normal command produced no object: {module}')
            object_after = fp(obj)
            if object_before is not None:
                need(object_before['sha256'] == object_after['sha256'], 'Object changed during check')
            frozen[str(obj)] = object_after
            output_sidecars = []
            for extra in (Path(str(obj) + '.server'), Path(str(obj) + '.private'), obj.with_suffix('.ir')):
                if extra.exists():
                    frozen[str(extra)] = fp(extra)
                    output_sidecars.append(frozen[str(extra)])
            accepted = {**current, 'status': 'succeeded', 'source': source_pin,
                'object': object_after, 'object_sidecars': output_sidecars,
                'command_result': fp(folder / 'result.json'), 'log': result['log'],
                'all_frozen_inputs_unchanged': True}
            if mode == 'owned':
                accepted['owned'] = parse_owned(Path(result['log']['path']).read_text(), module)
                accepted['audit_source'] = fp(audit)
            write_json(folder / 'ACCEPTED_STEP.json', accepted)
            records.append({**current, 'receipt': fp(folder / 'ACCEPTED_STEP.json')})
            print(json.dumps({'accepted': current, 'receipt': str(folder / 'ACCEPTED_STEP.json')}), flush=True)
        unchanged()
        write_json(attempt / 'RESULT.json', {'status': 'PASS_NORMAL_KERNEL_FULL_OWNED',
            'new_owners': list(TARGETS), 'kernel_backfills': list(BACKFILL),
            'records': records, 'context': fp(attempt / 'RUN.json'),
            'P2_6_complete_claimed': False, 'supplier_normal_recompilation': False})
        print(json.dumps({'status': 'PASS_NORMAL_KERNEL_FULL_OWNED',
                          'result': str(attempt / 'RESULT.json')}), flush=True)
        return 0
    except BaseException as exc:
        write_json(attempt / 'RESULT.json', {'status': 'FAILED_STOPPED',
            'error': f'{type(exc).__name__}: {exc}', 'failed_step': current,
            'accepted_steps': records, 'P2_6_complete_claimed': False})
        print(f'FAILED_STOPPED: {exc}; evidence: {attempt / "RESULT.json"}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
