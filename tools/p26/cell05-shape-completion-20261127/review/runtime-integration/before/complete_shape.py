#!/usr/bin/env python3
"""Execute or revalidate exactly the three repaired Cell05 Shape proof steps on P2."""
from contextlib import ExitStack, contextmanager
import argparse
import fcntl
import hashlib
import importlib.abc
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import time

OLD = Path('/workspace/p26-cell05-remaining9-stage-v2-557a12f3bcd7')
STAGE = Path('/workspace/p26-cell05-shape-completion-20261127-v1')
OLD_TOOL = OLD / 'tools/p26/cell05-remaining9-run-20261126'
TOOL = STAGE / 'tools/p26/cell05-shape-completion-20261127'
SHORT = 'P2OriginalSaving19Geometry05ScalableShape'
MODULE = 'ImbalancedChen.' + SHORT
REL = Path('ImbalancedChen') / SHORT
SOURCE = STAGE / 'project' / REL.with_suffix('.lean')
OBJECT = STAGE / 'objects' / REL.with_suffix('.olean')
AUDIT = TOOL / 'owned-audits' / (SHORT + '.lean')
RECEIPTS = STAGE / 'verification'
RUN = RECEIPTS / 'RUN.json'
PREFIX = STAGE / 'PREFIX8_VALIDATED.json'
MODES = ('normal', 'kernel', 'owned')
PILOT = 'remaining9-pilot-v1'
CONT = 'remaining9-complete-v1'
SCOPE = 'Cell05 parse/decode/finite shape only'
LIMIT = 12 * 1024**3
WALL = 900
PINS_SHA = 'be4fc8f2064e9ba988a8eaed42b54831635eca9a297abf57bd08c08446b5be86'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def strict_path(p):
    p = Path(p)
    require(p.is_absolute() and '..' not in p.parts and p.resolve(strict=True) == p,
            f'Expected an existing canonical path: {p}')
    return p


def verified_bytes(path, pin):
    path = strict_path(path)
    require(stat.S_ISREG(path.stat().st_mode), f'Expected regular file: {path}')
    body = path.read_bytes()
    require(len(body) == pin['bytes'] and hashlib.sha256(body).hexdigest() == pin['sha256'],
            f'Frozen file changed: {path}')
    return body


def check_child_import_root(root, manifest):
    """Only authenticated top-level Python source and inert workflow data may be visible."""
    rows = {Path(row['relative_path']): row for row in manifest['workflow_files']}
    directories = {parent for path in rows for parent in path.parents}
    for relative, row in rows.items():
        require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe original workflow member')
        verified_bytes(root / relative, row)
    pending = [root]
    while pending:
        parent = pending.pop()
        for path in parent.iterdir():
            strict_path(path)
            relative = path.relative_to(root)
            if path.is_dir():
                require(relative in directories and path.name != '__pycache__',
                        f'Unexpected child import directory: {path}')
                pending.append(path)
            else:
                require(path.is_file(), f'Unexpected child import inode: {path}')
                if path.suffix == '.py':
                    require(path.parent == root and relative in rows and path.name != '__init__.py',
                            f'Unpinned child Python source: {path}')
                else:
                    require(path.suffix in ('.json', '.md', '.lean', '.txt'),
                            f'Unexpected child import file: {path}')


@contextmanager
def child_import_boundary(here, pins):
    """The original probes start fresh -I -B interpreters with ordinary file loaders."""
    manifest = json.loads(verified_bytes(here / 'REMAINING9_VERIFIER.json', pins['original_verifier']))
    boundary_pin = next(r for r in manifest['workflow_files'] if r['relative_path'] == 'BOUNDARY.json')
    boundary = json.loads(verified_bytes(here / 'BOUNDARY.json', boundary_pin))
    require(set(boundary['origins']) == {'prefix13', 'shape1'}, 'Unexpected child validator families')
    roots = [(here, manifest)]
    with ExitStack() as locks:
        for name in ('prefix13', 'shape1'):
            origin = boundary['origins'][name]
            stage = strict_path(origin['stage'])
            root = strict_path(stage / origin['tool_relative_path'])
            root.relative_to(stage)
            lock = locks.enter_context(strict_path(stage / 'EXECUTION.lock').open('rb'))
            fcntl.flock(lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
            verifier = strict_path(root / origin['verifier_name'])
            require(str(verifier) == origin['verifier']['path'], 'Child verifier path mismatch')
            roots.append((root, json.loads(verified_bytes(verifier, origin['verifier']))))
        for root, config in roots:
            check_child_import_root(root, config)
        yield
        for root, config in roots:
            check_child_import_root(root, config)


class PinnedSource(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    """Import only authenticated source bytes, without consulting .pyc or adding a search root."""
    def __init__(self, files):
        self.files = files

    def find_spec(self, fullname, path=None, target=None):
        if fullname in self.files:
            return importlib.util.spec_from_loader(fullname, self, origin=str(self.files[fullname][0]))
        return None

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        path, body = self.files[module.__name__]
        module.__file__ = str(path)
        exec(compile(body, str(path), 'exec'), module.__dict__)


def bootstrap(old, old_tool, pins):
    package = json.loads(verified_bytes(old / 'PACKAGE_CONTENTS.json', pins['original_package']))
    manifest_path = old_tool / 'REMAINING9_VERIFIER.json'
    manifest = json.loads(verified_bytes(manifest_path, pins['original_verifier']))
    packaged = {row['member']: row for row in package['members']}
    files = {}
    for row in manifest['workflow_files']:
        path = strict_path(old_tool / row['relative_path'])
        path.relative_to(old_tool)
        member = str(path.relative_to(old))
        require(all(packaged[member][k] == row[k] for k in ('sha256', 'bytes')), 'Package/verifier disagreement')
        body = verified_bytes(path, row)
        if path.parent == old_tool and path.suffix == '.py':
            files[path.stem] = path, body
    require(not (files.keys() & sys.modules.keys()), 'Original helper module already imported')
    sys.meta_path.insert(0, PinnedSource(files))
    import receipt_checks as R
    import verify_remaining9 as V
    import export_remaining9 as E
    for name, (path, _) in files.items():
        if name in sys.modules:
            require(sys.modules[name].__file__ == str(path), 'Mixed original helper families')
    return R, V, E


def recorded(R, path, data):
    """Append or compare reproducible summary data. Never repair an existing record."""
    if path.exists():
        require(R.read(path) == data, f'Existing evidence differs: {path}')
    else:
        R.dump_new(path, data)


def check_raw(R, pins):
    expected = pins['original_raw']
    files = R.tree_files(OLD / 'verification')
    require({str(p.relative_to(OLD)) for p in files} == expected.keys(), 'Original raw receipt inventory differs')
    rows = []
    for p in sorted(files):
        row = R.fp(p)
        require(R.same(row, expected[str(p.relative_to(OLD))]), f'Original raw receipt changed: {p}')
        rows.append(row)
    return rows


def validate_original(R, V, pins):
    raw = check_raw(R, pins)
    manifest, registry, joined = V.load_configuration(OLD_TOOL)
    pilot_path = OLD / 'verification' / PILOT / 'STOPPED.json'
    cont_path = OLD / 'verification' / CONT / 'STOPPED.json'
    pilot, cont = R.read(pilot_path), R.read(cont_path)
    prun = R.checked(pilot['run'], pilot_path.with_name('RUN.json'))
    crun = R.checked(cont['run'], cont_path.with_name('RUN.json'))
    original = crun['context']
    require(prun['context'] == original and original['stage'] == str(OLD), 'Original RUN contexts differ')
    V.bind_context_to_package(original, OLD_TOOL, manifest, registry, joined)
    R.check_context_inputs(original)
    targets = [r['module'] for r in manifest['targets']]
    require(len(targets) == 9 and targets[-1] == MODULE, 'Unexpected last owner')
    R.reject_missing_successful_objects(OLD, targets)
    steps = {(m, mode): R.prior(original, m, mode) for m in targets for mode in MODES}
    require(R.require_accepted_prefix(original, steps) == 24, 'Expected exactly 8 fully accepted owners')
    require((pilot['reason'], pilot['accepted_steps'], pilot['accepted_targets'], pilot['newly_executed_steps'],
             pilot['reused_steps']) == ('new_step_budget', 3, 1, 3, 0), 'Wrong pilot stop')
    require((cont['newly_executed_steps'], cont['reused_steps']) == (22, 3), 'Wrong continuation stop')
    expected = []
    for m in targets[:-1]:
        for mode in MODES:
            seal = steps[m, mode]['accepted']
            attempt = PILOT if m == targets[0] else CONT
            require(Path(seal['path']).parent.parent.name == attempt, 'Wrong step origin')
            expected.append({'module': m, 'mode': mode, 'accepted': seal,
                             'disposition': 'reused' if attempt == PILOT else 'executed'})
    require(cont['records'] == expected and pilot['records'] ==
            [dict(row, disposition='executed') for row in expected[:3]], 'Wrong ordered acceptance records')
    folder = cont_path.parent / SHORT
    result = R.checked(cont['failed_result'], folder / 'normal-result.json')
    command = R.checked(result['command'], folder / 'normal-command.json')
    fail_log = R.fp(folder / 'normal.log')
    paths = R.target_paths(original, MODULE)
    deps = R.dependency_objects(original, MODULE)
    require(result['schema'] == 'cell05_remaining9_step_result_v1' and
            command['schema'] == 'cell05_remaining9_step_command_v1' and
            command['argv'] == R.expected_argv(original, MODULE, 'normal') and
            command['cwd'] == original['cwd'] and command['environment'] == original['environment'] and
            command['object_before'] is None and result['object'] is None and not paths['object'].exists() and
            result['status'] == 'failed' and result['exit_code'] == 1 and result['termination_reason'] is None and
            result['log'] == fail_log and 'error:' in (folder / 'normal.log').read_text(), 'Wrong Shape failure chain')
    for item in (command, result):
        require((item['run'], item['module'], item['mode']) == (cont['run'], MODULE, 'normal') and
                item['audit_source'] is None and item['source'] == R.fp(paths['source']) and
                item['dependency_objects'] == deps, 'Wrong failed Shape inputs')
    target = manifest['targets'][-1]
    supplier_by_module = {r['module']: r for r in registry['suppliers']}
    accepted_by_module = {r['module']: r for r in manifest['targets'][:-1]}
    require(set(target['transitive_dependencies']) == deps.keys() == supplier_by_module.keys() | accepted_by_module.keys()
            and len(deps) == 125, 'Unexpected Shape dependency closure')
    dependencies = {}
    for m, obj in sorted(deps.items()):
        if m in supplier_by_module:
            row = supplier_by_module[m]
            expected_object = row['object']
        else:
            row = accepted_by_module[m]
            expected_object = steps[m, 'owned']['result']['object']
        source = R.fp(OLD / 'project' / (m.replace('.', '/') + '.lean'))
        require(R.same(obj, expected_object) and R.same(source, row['source']), f'Unaccepted dependency: {m}')
        dependencies[m] = {'source': source, 'object': obj}
    R.check_context_inputs(original)
    require(check_raw(R, pins) == raw, 'Raw inputs changed during historical validation')
    prefix = {'schema': 'cell05_original_prefix8_validation_v1', 'status': 'PREFIX8_VALIDATED',
              'original_schema': original['schema'], 'original_stage': str(OLD), 'pilot_run': pilot['run'],
              'pilot_stop': R.fp(pilot_path), 'pilot_new_successes': 3, 'pilot_reason': pilot['reason'],
              'continuation_run': cont['run'], 'continuation_stop': R.fp(cont_path),
              'continuation_reused_steps': 3, 'continuation_new_successes': 21, 'continuation_new_commands': 22,
              'accepted_targets': 8, 'accepted_steps': 24, 'records': expected,
              'failed_normal': {'command': result['command'], 'result': cont['failed_result'], 'log': fail_log,
                                'source': result['source'], 'exit_code': 1, 'object': None},
              'runtime_guard': original['runtime_guard'], 'raw_receipts': raw,
              'recovery_archive_sha256': pins['original_recovery_sha256'], 'P2_6_complete': False}
    return original, target, dependencies, prefix


def actual_namespace(R, root, allowed, required):
    found = {str(p.relative_to(root)) for p in R.tree_files(root, allowed)}
    require(required <= found <= allowed, f'Namespace missing or unexpected file: {root}')


def validate_namespaces(R, original, deps):
    old_objects = {str(Path(row['object']['path']).relative_to(OLD / 'objects')) for row in deps.values()}
    old_sources = {str(Path(row['source']['path']).relative_to(OLD / 'project')) for row in deps.values()}
    relative_object = str(REL.with_suffix('.olean'))
    relative_source = str(REL.with_suffix('.lean'))
    actual_namespace(R, OLD / 'objects', old_objects, old_objects)
    actual_namespace(R, OLD / 'project', old_sources | {relative_source}, old_sources | {relative_source})
    actual_namespace(R, STAGE / 'objects', old_objects | {relative_object}, old_objects)
    actual_namespace(R, STAGE / 'project', old_sources | {relative_source}, old_sources | {relative_source})
    for root in [*original['mathlib_package_object_roots'], original['mathlib_objects'],
                 str(Path(original['environment']['LEAN_SYSROOT']) / 'lib/lean')]:
        path = R.canonical(root, True)
        require(path.is_dir() and not os.path.lexists(path / 'ImbalancedChen') and
                not os.path.lexists(path / 'ImbalancedChen.olean'), f'Fallback project namespace: {path}')


def install_selected(R, dependencies):
    """Install ordinary copies, with no inode shared with historical accepted evidence."""
    retained = RUN.exists() or bool(R.tree_files(RECEIPTS))
    for module, row in dependencies.items():
        for kind, folder, suffix in [('source', 'project', '.lean'), ('object', 'objects', '.olean')]:
            origin = row[kind]
            dest = R.canonical(STAGE / folder / (module.replace('.', '/') + suffix))
            if not dest.exists():
                require(not retained, f'Missing frozen dependency in existing run: {dest}')
                data = verified_bytes(origin['path'], origin)
                dest.parent.mkdir(parents=True, exist_ok=True)
                R.canonical(dest.parent, True)
                with dest.open('xb') as output:
                    output.write(data)
            installed = R.fp(dest)
            require(R.same(installed, origin) and not dest.samefile(origin['path']), f'Wrong dependency copy: {dest}')
            row['installed_' + kind] = installed


def make_context(R, original, old_target, deps, prefix, pins):
    source, audit = R.fp(SOURCE), R.fp(AUDIT)
    require(R.same(source, pins['repaired_source']) and R.same(audit, pins['owned_audit']) and
            R.same(audit, old_target['audit']) and not R.same(source, old_target['source']), 'Wrong repair/audit bytes')
    imports = re.findall(r'^import (ImbalancedChen\.[\w.]+)$', SOURCE.read_text(), re.M)
    require(imports == old_target['project_imports'], 'Repaired project imports changed')
    original_roots = original['environment']['LEAN_PATH'].split(os.pathsep)
    require(original_roots[0] == str(OLD / 'objects'), 'Original Lean path mismatch')
    environment = dict(original['environment'])
    environment['LEAN_PATH'] = os.pathsep.join([str(STAGE / 'objects'), *original_roots[1:]])
    require(all(environment[k] is None for k in ('LD_LIBRARY_PATH', 'LEAN_OPTS', 'LEAN_SRC_PATH')),
            'Unexpected runtime environment override')
    target = {'module': MODULE, 'source': source, 'audit': audit, 'project_imports': imports,
              'transitive_dependencies': sorted(deps)}
    return {'schema': 'cell05_single_shape_run_v1', 'stage': str(STAGE), 'original_stage': str(OLD),
            'cwd': str(STAGE / 'project'), 'environment': environment, 'runtime': original['runtime'],
            'runtime_guard': original['runtime_guard'], 'mathlib': original['mathlib'],
            'mathlib_objects': original['mathlib_objects'], 'mathlib_package_object_roots': original['mathlib_package_object_roots'],
            'targets': [target], 'dependencies': deps, 'prefix8': R.fp(PREFIX), 'original_run': prefix['continuation_run'],
            'original_frozen_inputs': original['frozen_inputs'], 'original_raw_receipts': prefix['raw_receipts'],
            'driver': R.fp(TOOL / 'complete_shape.py'), 'configuration': R.fp(TOOL / 'PINS.json'),
            'old_package': R.fp(OLD / 'PACKAGE_CONTENTS.json'), 'rss_limit_bytes': LIMIT, 'wall_limit_seconds': WALL,
            'scope': SCOPE, 'old_proof_commands': 0, 'P2_6_complete': False}


def check_inputs(R, V, context, original, prefix, pins):
    R.check_context_inputs(original)
    require(V.git_commit_readonly(Path(original['mathlib'])) == V.MATHLIB_COMMIT, 'Mathlib commit changed')
    require(check_raw(R, pins) == context['original_raw_receipts'], 'Original evidence changed')
    validate_namespaces(R, original, context['dependencies'])
    require(R.read(PREFIX) == prefix and R.read(RUN) == context, 'Run or prefix context changed')
    files = [context[k] for k in ('driver', 'configuration', 'old_package', 'prefix8', 'original_run')]
    files += [context['targets'][0][k] for k in ('source', 'audit')]
    for dep in context['dependencies'].values():
        files.extend(dep.values())
    for row in files:
        require(R.fp(row['path']) == row, f'Input changed: {row["path"]}')


def command_fields(R, ctx, mode, previous):
    require(mode in MODES and ((mode == 'normal') == (previous is None)), 'Invalid command stage')
    target = ctx['targets'][0]
    common = [ctx['runtime']['lean_binary']['path'], '--trust=0', '-DwarningAsError=true', '-j1', '-M12288',
              '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
    if mode == 'normal':
        argv = common + ['-o', str(OBJECT), str(REL.with_suffix('.lean'))]
    elif mode == 'kernel':
        argv = [ctx['runtime']['leanchecker_binary']['path'], '--verbose', MODULE]
    else:
        argv = common + [str(AUDIT)]
    return {'schema': 'cell05_single_shape_command_v1', 'run': R.fp(RUN), 'module': MODULE, 'mode': mode,
            'previous_accepted': previous, 'argv': argv, 'cwd': ctx['cwd'], 'environment': ctx['environment'],
            'source': target['source'], 'audit_source': target['audit'], 'object_before': None if previous is None else R.fp(OBJECT),
            'dependencies': ctx['dependencies']}


def log_facts(R, ctx, mode, log):
    require(not re.search(r'(?:^|:\s*|\s)(?:warning|error|fatal error):', log, re.M | re.I), 'Diagnostic in successful log')
    if mode == 'kernel':
        require(log.strip() == 'replaying ' + MODULE, 'Wrong kernel replay log')
        return {}
    if mode == 'owned':
        markers = ('P26_GEOMETRY01_AUDIT_IMPORTS ', 'P26_GEOMETRY01_AUDIT_INVENTORY ',
                   'P26_GEOMETRY01_AUDIT_DECL ', 'P26_GEOMETRY01_AUDIT_COMPLETE ')
        require(all(line.startswith(markers) for line in log.splitlines() if line.strip()), 'Unexpected owned log output')
        return {'owned': R.parse_target_owned(log, ctx, MODULE)}
    names = [MODULE + '.' + n for n in re.findall(r'^#print axioms (\w+)$', SOURCE.read_text(), re.M)]
    require(bool(names), 'No printed declarations')
    pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*"
    rows = list(re.finditer(pattern, log))
    require(''.join(m.group(0) for m in rows) == log and [m[1] for m in rows] == names,
            'Incomplete or unexpected printed-axiom output')
    axioms = {a.strip() for m in rows for a in (m[2] or '').split(',') if a.strip()}
    require(axioms <= R.ALLOWED, 'Forbidden printed axiom')
    return {'printed_axioms': sorted(axioms), 'printed_declarations': names}


def step_paths(mode):
    return tuple(RECEIPTS / (mode + suffix) for suffix in ('-command.json', '.log', '-result.json', '-accepted.json'))


def witness_path(mode):
    return STAGE / 'launch-witnesses' / (mode + '.json')


def witness_fields(R, mode, command_pin):
    return {'schema': 'cell05_single_shape_launch_v1', 'module': MODULE, 'mode': mode,
            'run': R.fp(RUN), 'command': command_pin}


def sync_directory(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def publish_witness(R, mode, command_pin):
    """Make the independent no-replay barrier durable before the process can start."""
    witness = witness_path(mode)
    R.dump_new(witness, witness_fields(R, mode, command_pin))
    for path in (RUN, Path(command_pin['path']), witness):
        with R.canonical(path, True).open('rb') as stream:
            os.fsync(stream.fileno())
    for directory in (RECEIPTS, witness.parent, STAGE):
        sync_directory(directory)
    return verify_witness(R, mode, command_pin)


def verify_witness(R, mode, command_pin):
    path = witness_path(mode)
    require(R.read(path) == witness_fields(R, mode, command_pin), f'Launch witness disagrees with RUN/command: {mode}')
    return R.fp(path)


def metrics_ok(result, started):
    vals = (started, result['finished_unix'], result['elapsed_seconds'])
    return (all(type(v) in (int, float) and math.isfinite(v) and v > 0 for v in vals) and
            result['started_unix'] == started and result['finished_unix'] >= started and result['elapsed_seconds'] <= WALL and
            type(result['peak_rss_bytes']) is int and 0 <= result['peak_rss_bytes'] <= LIMIT)


def verify_step(R, ctx, mode, previous):
    cmd_path, log_path, result_path, seal_path = step_paths(mode)
    command = R.read(cmd_path)
    expected = command_fields(R, ctx, mode, previous)
    require('started_unix' in command and {k: v for k, v in command.items() if k != 'started_unix'} == expected,
            'Command diverged from frozen execution plan')
    witness = verify_witness(R, mode, R.fp(cmd_path))
    result = R.read(result_path)
    require(result['launch_witness'] == witness and result['schema'] == 'cell05_single_shape_result_v1' and result['status'] == 'succeeded' and
            type(result['exit_code']) is int and result['exit_code'] == 0 and result['termination_reason'] is None and
            metrics_ok(result, command['started_unix']), 'Unsuccessful command or invalid metrics')
    for key in ('run', 'module', 'mode', 'source', 'audit_source', 'dependencies'):
        require(result[key] == command[key], f'Result/command mismatch: {key}')
    require(result['command'] == R.fp(cmd_path) and result['log'] == R.fp(log_path) and result['object'] == R.fp(OBJECT)
            and result['object']['bytes'] > 0, 'Result evidence changed')
    facts = log_facts(R, ctx, mode, log_path.read_text())
    if mode == 'owned':
        owned = facts.pop('owned')
        require(R.checked(result['owned_declarations'], RECEIPTS / 'owned-declarations.json') == owned and
                result['owned_declaration_count'] == owned['owned_declaration_count'], 'Incomplete owned evidence')
    require(all(result.get(k) == v for k, v in facts.items()), 'Inconsistent normal axiom evidence')
    seal = {'schema': 'cell05_single_shape_accepted_v1', 'status': 'accepted', 'run': R.fp(RUN),
            'module': MODULE, 'mode': mode, 'launch_witness': witness, 'command': R.fp(cmd_path),
            'result': R.fp(result_path), 'object': R.fp(OBJECT)}
    require(R.read(seal_path) == seal, 'Seal mismatch')
    return R.fp(seal_path)


def prior_steps(R, ctx):
    names = {'RUN.json', 'SUCCESS.json', 'STOPPED.json', 'owned-declarations.json'}
    names.update(p.name for mode in MODES for p in step_paths(mode))
    R.tree_files(RECEIPTS, names)
    R.tree_files(STAGE / 'launch-witnesses', {m + '.json' for m in MODES})
    accepted = []
    for mode in MODES:
        paths = step_paths(mode)
        present = [p.exists() for p in paths]
        witness = witness_path(mode)
        if not any(present) and not witness.exists():
            continue
        require(witness.exists() and present[0], f'Orphan launch witness or missing witness; preserve without replay: {mode}')
        verify_witness(R, mode, R.fp(paths[0]))
        require(all(present) and len(accepted) == MODES.index(mode), 'Incomplete or non-prefix receipts; preserve without replay')
        accepted.append(verify_step(R, ctx, mode, accepted[-1] if accepted else None))
    require(not (RECEIPTS / 'STOPPED.json').exists(), 'Stopped attempt retained. No replay in this stage.')
    require(OBJECT.exists() == bool(accepted), 'Unreceipted or missing object')
    require((RECEIPTS / 'owned-declarations.json').exists() == (len(accepted) == 3), 'Orphan/missing full owned audit')
    if ((RECEIPTS / 'SUCCESS.json').exists() or (STAGE / 'COMBINED_INDEX.json').exists() or
            bool(R.tree_files(STAGE / 'exports'))):
        require(len(accepted) == 3, 'Completion index with missing successful evidence')
    return accepted


def run_process(R, argv, cwd, env, log):
    proc, rc, reason, peak = None, None, None, 0
    start = time.monotonic()
    with log.open('x') as output:
        try:
            proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            while proc.poll() is None:
                peak = max(peak, R.tree_rss(proc.pid))
                if peak > LIMIT or time.monotonic() - start >= WALL:
                    reason = 'rss_limit' if peak > LIMIT else 'timeout'
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            rc = proc.wait()
        except (Exception, KeyboardInterrupt) as exc:
            reason = 'launch_or_wait_error'
            if proc is not None:
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGKILL)
                rc = proc.wait()
            output.write(repr(exc) + '\n')
    elapsed = time.monotonic() - start
    if elapsed > WALL and reason is None:
        reason = 'timeout'
    return rc, reason, peak, elapsed


def execute(R, V, ctx, mode, previous, check):
    check()
    cmd_path, log_path, result_path, seal_path = step_paths(mode)
    require(not any(p.exists() for p in step_paths(mode)), 'Refusing to repeat a command')
    history = prior_steps(R, ctx)
    require(len(history) == MODES.index(mode) and (history[-1] if history else None) == previous, 'Prior acceptance changed')
    require(OBJECT.exists() == (previous is not None), 'Unexpected object before launch')
    if previous:
        require(R.checked(previous, step_paths(MODES[MODES.index(mode) - 1])[-1])['object'] == R.fp(OBJECT),
                'Accepted object changed before next command')
    cmd = command_fields(R, ctx, mode, previous)
    cmd['started_unix'] = time.time()
    R.dump_new(cmd_path, cmd)
    cmd_pin = R.fp(cmd_path)
    witness = publish_witness(R, mode, cmd_pin)
    env = {k: v for k, v in cmd['environment'].items() if v is not None}
    print(json.dumps({'mode': mode, 'status': 'started'}), flush=True)
    rc, reason, peak, elapsed = run_process(V, cmd['argv'], cmd['cwd'], env, log_path)
    result = {k: cmd[k] for k in ('run', 'module', 'mode', 'source', 'audit_source', 'dependencies')}
    result.update(schema='cell05_single_shape_result_v1', launch_witness=witness, command=cmd_pin, termination_reason=reason, exit_code=rc,
                  started_unix=cmd['started_unix'], finished_unix=time.time(), elapsed_seconds=elapsed,
                  peak_rss_bytes=peak, log=R.fp(log_path), object=R.fp(OBJECT) if OBJECT.exists() else None, status='failed')
    try:
        check()
        for i, accepted in enumerate(history):
            require(verify_step(R, ctx, MODES[i], history[i - 1] if i else None) == accepted, 'Prior step changed')
        require(verify_witness(R, mode, cmd_pin) == witness and R.fp(cmd_path) == cmd_pin and R.read(cmd_path) == cmd, 'Command changed during execution')
        require(rc == 0 and reason is None and metrics_ok(result, cmd['started_unix']), 'Command failed or exceeded limits')
        require(result['object'] and result['object']['bytes'] > 0 and (mode == 'normal' or result['object'] == cmd['object_before']),
                'Missing or mutated verified object')
        facts = log_facts(R, ctx, mode, log_path.read_text())
        if mode == 'owned':
            owned = facts.pop('owned')
            owned_path = RECEIPTS / 'owned-declarations.json'
            R.dump_new(owned_path, owned)
            result.update(owned_declarations=R.fp(owned_path), owned_declaration_count=owned['owned_declaration_count'])
        result.update(facts, status='succeeded')
    except Exception as exc:
        result['validation_error'] = repr(exc)
    R.dump_new(result_path, result)
    if result['status'] != 'succeeded':
        R.dump_new(RECEIPTS / 'STOPPED.json', {'schema': 'cell05_single_shape_stopped_v1', 'status': 'stopped',
                   'run': R.fp(RUN), 'failed_result': R.fp(result_path), 'preceding_acceptances': MODES.index(mode),
                   'P2_6_complete': False})
        raise RuntimeError('Failed step retained: ' + str(result_path) + ' ' + result['validation_error'])
    R.dump_new(seal_path, {'schema': 'cell05_single_shape_accepted_v1', 'status': 'accepted', 'run': cmd['run'],
               'module': MODULE, 'mode': mode, 'launch_witness': witness, 'command': cmd_pin,
               'result': R.fp(result_path), 'object': result['object']})
    seal = verify_step(R, ctx, mode, previous)
    print(json.dumps({'mode': mode, 'status': 'accepted', 'elapsed_seconds': elapsed, 'peak_rss_bytes': peak}), flush=True)
    return seal


def require_published():
    for path in (RECEIPTS / 'SUCCESS.json', STAGE / 'COMBINED_INDEX.json', STAGE / 'exports/shape-evidence.tar.xz'):
        require(path.is_file() and strict_path(path) == path, f'Missing retained final evidence: {path}')


def finish(R, E, ctx, accepted, check, verify_only=False):
    def summary(path, expected):
        if verify_only:
            require(R.read(path) == expected, f'Retained final summary differs: {path}')
        else:
            recorded(R, path, expected)

    if verify_only:
        require_published()
    require(accepted == prior_steps(R, ctx) and len(accepted) == 3, 'Incomplete single-owner acceptance')
    success_path = RECEIPTS / 'SUCCESS.json'
    records = [{'module': MODULE, 'mode': mode, 'accepted': seal} for mode, seal in zip(MODES, accepted)]
    summary(success_path, {'schema': 'cell05_single_shape_success_v1', 'status': 'succeeded', 'run': R.fp(RUN),
             'accepted_targets': 1, 'accepted_steps': 3, 'records': records, 'object': R.fp(OBJECT),
             'old_proof_commands': 0, 'scope': SCOPE, 'P2_6_complete': False})
    index = STAGE / 'COMBINED_INDEX.json'
    summary(index, {'schema': 'cell05_two_context_index_v1', 'prefix8': R.fp(PREFIX),
             'prefix8_accepted_targets': 8, 'prefix8_accepted_steps': 24, 'shape_success': R.fp(success_path),
             'shape_accepted_targets': 1, 'shape_accepted_steps': 3, 'distinct_owners': 9, 'distinct_step_acceptances': 27,
             'scope': SCOPE, 'P2_6_complete': False})
    paths = [PREFIX, index, SOURCE, AUDIT, OBJECT, TOOL / 'complete_shape.py', TOOL / 'PINS.json', *R.tree_files(RECEIPTS),
             *(witness_path(m) for m in MODES)]
    entries = {str(path.relative_to(STAGE)): path for path in paths}
    manifest = {'schema': 'cell05_single_shape_export_v1', 'accepted_targets': 1, 'accepted_steps': 3,
                'old_supplier_object_bodies': 0, 'runtime_guard': ctx['runtime_guard'], 'scope': SCOPE,
                'P2_6_complete': False, 'members': [{'member': member, **E.data_pin(path.read_bytes())}
                         for member, path in sorted(entries.items())]}
    output = R.canonical(STAGE / 'exports/shape-evidence.tar.xz')
    if verify_only or output.exists():
        E.recheck_archive(output, manifest)
    else:
        E.write_verified_archive(output, entries, manifest)
    check()
    require(prior_steps(R, ctx) == accepted, 'Step receipts changed during export')
    status = 'RETAINED_EVIDENCE_VERIFIED' if verify_only else 'SINGLE_SHAPE_SUCCESS'
    print(json.dumps({'status': status, 'success': R.fp(success_path), 'combined_index': R.fp(index),
                      'archive': R.fp(output), 'accepted_targets': 1, 'accepted_steps': 3, 'P2_6_complete': False}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('preflight', 'run', *MODES, 'verify'))
    action = parser.parse_args().action
    require(sys.flags.isolated and sys.flags.dont_write_bytecode and not sys.flags.optimize,
            'Launch a fresh python3 -I -B interpreter with assertions enabled')
    require(strict_path(__file__) == TOOL / 'complete_shape.py', 'Wrong deployed driver path')
    pins = json.loads(verified_bytes(TOOL / 'PINS.json', {'bytes': 25524, 'sha256': PINS_SHA}))
    strict_path(OLD / 'EXECUTION.lock')
    require(STAGE.parent == OLD.parent and STAGE != OLD, 'Stages must be disjoint')
    if action == 'verify':
        require_published()
        for path in (RUN, PREFIX, STAGE / 'EXECUTION.lock'):
            strict_path(path)
    new_lock_path = STAGE / 'EXECUTION.lock'
    if os.path.lexists(new_lock_path):
        strict_path(new_lock_path)
    lock_mode = 'rb' if action == 'verify' else 'a'
    with (OLD / 'EXECUTION.lock').open('rb') as historical_lock, new_lock_path.open(lock_mode) as stage_lock:
        fcntl.flock(historical_lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        fcntl.flock(stage_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with child_import_boundary(OLD_TOOL, pins):
            R, V, E = bootstrap(OLD, OLD_TOOL, pins)
            original, target, dependencies, prefix = validate_original(R, V, pins)
        for path in (STAGE / 'objects' / 'ImbalancedChen', RECEIPTS):
            if action == 'verify':
                require(R.canonical(path, True).is_dir(), f'Missing established verification directory: {path}')
            else:
                R.canonical(path).mkdir(parents=True, exist_ok=True)
        require(RUN.exists() or not (R.tree_files(RECEIPTS) or R.tree_files(STAGE / 'launch-witnesses')), 'Run missing from existing receipt tree')
        require(RUN.exists() or not OBJECT.exists(), 'Unreceipted object in uninitialized stage')
        require(PREFIX.exists() or not RUN.exists(), 'Missing original prefix evidence')
        install_selected(R, dependencies)
        validate_namespaces(R, original, dependencies)
        recorded(R, PREFIX, prefix)
        ctx = make_context(R, original, target, dependencies, prefix, pins)
        # RUN is stable across mode invocations; resume compares it with a freshly derived context.
        recorded(R, RUN, ctx)

        def check():
            check_inputs(R, V, ctx, original, prefix, pins)

        check()
        accepted = prior_steps(R, ctx)
        if action == 'preflight':
            print(json.dumps({'status': 'PASS_PREFLIGHT', 'accepted_existing_steps': len(accepted), 'dependencies': 125,
                              'prefix8': R.fp(PREFIX), 'proof_commands_executed': 0}), flush=True)
            return
        if action == 'verify':
            require(len(accepted) == 3, 'Three accepted seals required for final verification')
        if action == 'run':
            modes = MODES[len(accepted):]
        elif action in MODES:
            index = MODES.index(action)
            require(index <= len(accepted), 'Requested stage lacks its accepted prerequisite')
            modes = [action] if index == len(accepted) else []
        else:
            modes = []
        for mode in modes:
            accepted.append(execute(R, V, ctx, mode, accepted[-1] if accepted else None, check))
        if len(accepted) == 3:
            finish(R, E, ctx, accepted, check, verify_only=(action == 'verify'))
        else:
            print(json.dumps({'status': 'ACCEPTED_PREFIX', 'accepted_steps': len(accepted), 'new_commands': len(modes)}))


if __name__ == '__main__':
    main()
