#!/usr/bin/env python3
"""Explicit v1 recovery: capture once; verify frozen bytes/current guard without proofs."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import stat
import subprocess
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
# Only these authenticated source bytes can supply the local helper. Python's
# ordinary import machinery is never asked to select a local module or a pyc.
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
    body = (HERE / row['relative_path']).read_bytes()
    if len(body) != row['bytes'] or hashlib.sha256(body).hexdigest() != row['sha256']:
        raise ValueError('Recovery source changed: ' + row['relative_path'])
    authenticated[row['relative_path']] = body
core = types.ModuleType('p26_recovery_core')
core.__file__ = str(HERE / 'protocol_core.py')
exec(compile(authenticated['protocol_core.py'], core.__file__, 'exec'), core.__dict__)
require, fp, checked = core.require, core.fp, core.checked
PROTOCOL_FILES = core.protocol_files(HERE)
require(PROTOCOL_FILES == sorted([{'path': str(HERE / 'WORKFLOW_MANIFEST.json'), **core.pin(manifest_bytes)},
        *[{'path': str(HERE / name), **core.pin(body)} for name, body in authenticated.items()]], key=lambda r: r['path']),
        'Recovery bootstrap inputs changed after authentication')
A = json.loads(authenticated['ANCHORS.json'])
STAGE = Path(A['recovery_stage'])
OUTPUTS = {name: STAGE / name for name in ('CURRENT_RUNTIME_GUARD.json', 'HISTORICAL_VALIDATION.json', 'CERTIFICATE.json')}
WORKER = HERE / 'recovery_worker.py'
KINDS = ('runtime', 'prefix13', 'shape1', 'remaining8', 'verify')


def action_audit(action):
    """The only processes are our fixed Python workers; only capture can write."""
    writable = set(map(str, OUTPUTS.values())) if action == 'capture' else set()
    def audit(event, args):
        if event == 'subprocess.Popen':
            executable, argv, cwd, env = args
            require(executable == sys.executable and isinstance(argv, list) and len(argv) == 6 and
                    argv[:5] == [sys.executable, '-I', '-S', '-B', str(WORKER)] and argv[5] in KINDS and
                    (action == 'capture' or argv[5] == 'verify') and cwd is None and env is None,
                    'Recovery attempted an unauthorized process')
            return
        if event == 'open':
            path, mode, flags = args
            writing = (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
                isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND))
            if writing:
                if type(path) is int:
                    require(stat.S_ISFIFO(os.fstat(path).st_mode) and
                            os.readlink('/proc/self/fd/' + str(path)).startswith('pipe:['),
                            'Only anonymous worker pipe descriptors may be opened for writing')
                    return
                require(str(path) in writable and flags & os.O_EXCL and flags & os.O_CREAT,
                        'Only exclusive new recovery output writes are allowed')
            return
        core.deny_worker_mutation(event, args)
    return audit


def run_worker(kind, payload=None):
    require(kind in KINDS, 'Unknown recovery worker')
    require(core.protocol_files(HERE) == PROTOCOL_FILES, 'Recovery source changed during this invocation')
    result = subprocess.run([sys.executable, '-I', '-S', '-B', str(WORKER), kind],
        input=json.dumps(payload or {}, separators=(',', ':')).encode(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900, check=False)
    require(result.returncode == 0 and not result.stderr, 'Read-only recovery worker failed (' + kind + '): ' +
            result.stderr.decode(errors='replace')[-24000:])
    require(len(result.stdout) <= 96*1024**2, 'Unexpected worker result size')
    return json.loads(result.stdout)


def validate_history(history):
    """Check the new protocol's small fixed scope before using a pinned cache."""
    require(history['schema'] == 'p26_runtime_recovery_history_v1' and
            history['status'] == 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY' and
            history['old_Lean_commands'] == 0 and history['original_evidence_rewritten'] is False and
            history['original_live_guard_validator_passed'] is False and history['P2_6_complete'] is False,
            'Wrong historical recovery scope')
    families = history['families']
    require(set(families) == {'prefix13', 'shape1', 'remaining8'}, 'Incomplete historical families')
    for kind, (owners, steps, owned) in {'prefix13': (13, 39, 112), 'shape1': (1, 3, 28), 'remaining8': (8, 24, 116)}.items():
        value = families[kind]
        require(value['schema'] == 'p26_preserved_family_recovery_v1' and value['kind'] == kind and
                value['status'] == 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY' and
                value['original_live_guard_validator_passed'] is False and value['old_Lean_commands'] == 0 and
                value['original_evidence_rewritten'] is False and value['P2_6_complete'] is False,
                'Wrong original family recovery status')
        state, context = value['state'], value['original_context']
        require(state['accepted_targets'] == owners and state['accepted_steps'] == len(state['records']) == steps and
                len(state['objects']) == owners and value['owned_declaration_count'] == owned and
                context['runtime_guard'] == A['original_guard'], 'Incomplete original family evidence')
        require([(r['module'], r['mode']) for r in state['records']] ==
                [(r['module'], mode) for r in context['targets'][:owners] for mode in ('normal', 'kernel', 'owned')],
                'Historical step order differs')
        if kind != 'shape1':
            require(len(context['targets']) == owners+1 and state['failure']['module'] == context['targets'][-1]['module'] and
                    state['failure']['accepted'] is False and state['failure']['object'] is None and
                    state['failure']['status'] == 'failed' and state['failure']['exit_code'] == 1,
                    'Original failed chain is missing or relabelled')
    final = families['remaining8']
    target, dependencies = final['target'], final['suppliers']
    require(final['original_context']['stage'] == A['remaining9']['stage'] and
            target == final['original_context']['targets'][-1] and target['module'] == A['target'] and
            len(dependencies) == len({r['module'] for r in dependencies}) == 125 and
            set(target['transitive_dependencies']) == {r['module'] for r in dependencies}, 'Exact125 dependency scope differs')
    original_rows = {r['module']: r for r in final['original_context']['suppliers']}
    original_rows.update({r['module']: {**r, 'object': final['state']['objects'][r['module']]}
                          for r in final['original_context']['targets'][:8]})
    for row in dependencies:
        old = original_rows[row['module']]
        require(row['source'] == old['source'] and core.same(row['object'], old['object']) and
                row['project_imports'] == old['project_imports'], 'Dependency contract changed')
        rel = row['module'].replace('.', '/')
        require(row['source_path'] == str(Path(A['remaining9']['stage']) / 'project' / (rel + '.lean')) and
                row['object_path'] == str(Path(A['remaining9']['stage']) / 'objects' / (rel + '.olean')),
                'Original dependency evidence relocated')
    expected_inputs = [*history['protocol_files'], A['original_guard'], A['original_snapshot'], history['python_executable']]
    expected_inputs += [row for value in families.values() for row in value['frozen_inputs']]
    require(history['frozen_inputs'] == core.refs(expected_inputs), 'Cached historical input inventory differs')
    expected_namespaces = {}
    for value in families.values():
        for row in value['namespaces']:
            require(expected_namespaces.setdefault(row['root'], row) == row, 'Historical namespace snapshots disagree')
    require(history['namespaces'] == [expected_namespaces[p] for p in sorted(expected_namespaces)],
            'Cached historical namespace coverage differs')
    require(history['runtime_capture']['status'] == 'COMPLETE_TEN_ROOT_CONTENT_EQUALITY' and
            history['runtime_capture']['original_guard_current_lstat_passed'] is False and
            history['runtime_capture']['original_guard'] == A['original_guard'] and
            history['runtime_capture']['original_snapshot'] == A['original_snapshot'] and
            history['runtime_capture']['Lean_commands'] == 0 and len(history['runtime_capture']['roots']) == 10,
            'Full byte recovery evidence is absent')


def verify(expected):
    require(expected['path'] == str(OUTPUTS['CERTIFICATE.json']), 'Certificate path is not the fixed recovery output')
    certificate = checked(expected)
    require(certificate['schema'] == 'p26_runtime_recovery_certificate_v1' and
            certificate['status'] == 'PASS_EXPLICIT_RUNTIME_RECOVERY' and certificate['stage'] == str(STAGE) and
            certificate['original_runtime_guard'] == A['original_guard'] and
            certificate['original_snapshot'] == A['original_snapshot'] and
            certificate['protocol_manifest'] == fp(HERE / 'WORKFLOW_MANIFEST.json') and
            certificate['protocol_files'] == PROTOCOL_FILES and certificate['old_Lean_commands'] == 0 and
            certificate['original_live_guard_validator_passed'] is False and
            certificate['original_evidence_rewritten'] is False and
            certificate['historical_loaded_runtime_inventory_claimed'] is False and certificate['P2_6_complete'] is False,
            'Certificate protocol, source, or scope binding differs')
    guard = checked(certificate['current_runtime_guard'], OUTPUTS['CURRENT_RUNTIME_GUARD.json'])
    history = checked(certificate['history'], OUTPUTS['HISTORICAL_VALIDATION.json'])
    require(history['protocol_files'] == PROTOCOL_FILES and
            history['python_executable'] == fp(Path(sys.executable).resolve()) and
            certificate['runtime_identity'] == history['families']['remaining8']['original_context']['runtime'] and
            certificate['historical_counts'] == {'prefix13': [13, 39, 112], 'shape1': [1, 3, 28], 'remaining8': [8, 24, 116]} and
            certificate['supplier_count'] == 125 and certificate['owned_project_closure_count'] == 126,
            'Certificate history/runtime binding differs')
    validate_history(history)
    current = run_worker('verify', {'current_guard': guard, 'history': history})
    require(current == {'schema': 'p26_runtime_recovery_current_check_v1', 'status': 'PASS_CURRENT_BINDINGS',
                        'original_live_guard_validator_passed': False, 'old_Lean_commands': 0}, 'Current evidence verification failed')
    require(fp(expected['path']) == expected and fp(certificate['history']['path']) == certificate['history'] and
            fp(certificate['current_runtime_guard']['path']) == certificate['current_runtime_guard'],
            'Recovery outputs changed during verification')
    final = history['families']['remaining8']
    return {'schema': 'p26_runtime_recovery_verified_v1', 'status': 'PASS_EXPLICIT_RUNTIME_RECOVERY',
            'certificate': expected, 'current_runtime_guard': certificate['current_runtime_guard'],
            'history': certificate['history'], 'protocol_manifest': certificate['protocol_manifest'],
            'original_runtime_guard': A['original_guard'], 'original_snapshot': A['original_snapshot'],
            'original': final['original_context'], 'target': final['target'], 'dependencies': final['suppliers'],
            'prefix8': final['state'],
            'frozen_inputs': core.refs([*history['frozen_inputs'], expected, certificate['current_runtime_guard'], certificate['history']]),
            'original_live_guard_validator_passed': False, 'old_Lean_commands': 0,
            'original_evidence_rewritten': False, 'P2_6_complete': False}


def capture():
    require(not any(p.exists() or p.is_symlink() for p in OUTPUTS.values()),
            'A recovery output already exists; preserve it and investigate, never overwrite')
    runtime = run_worker('runtime')
    require(runtime['schema'] == 'p26_runtime_recovery_capture_result_v1' and
            runtime['status'] == 'COMPLETE_TEN_ROOT_CONTENT_EQUALITY', 'Full runtime capture failed')
    guard = runtime['current_guard']
    prefix = run_worker('prefix13', {'current_guard': guard})
    shape = run_worker('shape1', {'current_guard': guard})
    remaining = run_worker('remaining8', {'current_guard': guard, 'prefix13': prefix, 'shape1': shape})
    families = {'prefix13': prefix, 'shape1': shape, 'remaining8': remaining}
    python_pin = fp(Path(sys.executable).resolve())
    frozen = core.refs([*PROTOCOL_FILES, A['original_guard'], A['original_snapshot'], python_pin,
                        *[row for value in families.values() for row in value['frozen_inputs']]])
    namespaces = {}
    for value in families.values():
        for row in value['namespaces']:
            require(namespaces.setdefault(row['root'], row) == row, 'Original namespaces changed between workers')
    history = {'schema': 'p26_runtime_recovery_history_v1', 'status': 'PASS_PRESERVED_CHAINS_UNDER_EXPLICIT_RECOVERY',
               'runtime_capture': {k: v for k, v in runtime.items() if k != 'current_guard'},
               'families': families, 'protocol_files': PROTOCOL_FILES, 'python_executable': python_pin,
               'frozen_inputs': frozen, 'namespaces': [namespaces[p] for p in sorted(namespaces)],
               'old_Lean_commands': 0, 'original_live_guard_validator_passed': False,
               'original_evidence_rewritten': False, 'P2_6_complete': False}
    validate_history(history)
    current = run_worker('verify', {'current_guard': guard, 'history': history})
    require(current['status'] == 'PASS_CURRENT_BINDINGS', 'Capture inputs changed before sealing')
    guard_pin = core.write_new(OUTPUTS['CURRENT_RUNTIME_GUARD.json'], guard)
    history_pin = core.write_new(OUTPUTS['HISTORICAL_VALIDATION.json'], history)
    certificate = {'schema': 'p26_runtime_recovery_certificate_v1', 'status': 'PASS_EXPLICIT_RUNTIME_RECOVERY',
        'stage': str(STAGE), 'protocol_manifest': fp(HERE / 'WORKFLOW_MANIFEST.json'), 'protocol_files': PROTOCOL_FILES,
        'original_runtime_guard': A['original_guard'], 'original_snapshot': A['original_snapshot'],
        'current_runtime_guard': guard_pin, 'history': history_pin,
        'runtime_identity': remaining['original_context']['runtime'],
        'historical_counts': {'prefix13': [13, 39, 112], 'shape1': [1, 3, 28], 'remaining8': [8, 24, 116]},
        'supplier_count': 125, 'owned_project_closure_count': 126,
        'original_live_guard_validator_passed': False, 'original_evidence_rewritten': False,
        'historical_loaded_runtime_inventory_claimed': False, 'old_Lean_commands': 0, 'P2_6_complete': False}
    certificate_pin = core.write_new(OUTPUTS['CERTIFICATE.json'], certificate)
    return verify(certificate_pin)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('capture', 'verify'))
    parser.add_argument('--certificate-sha256')
    parser.add_argument('--certificate-bytes', type=int)
    args = parser.parse_args()
    require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,
            'Invoke with -I -S -B and without optimization')
    require(HERE == STAGE / 'tools/p26/cell05-runtime-recovery-20261127', 'Use the explicitly versioned recovery stage')
    core.canonical(str(STAGE))
    sys.addaudithook(action_audit(args.action))
    if args.action == 'capture':
        require(args.certificate_sha256 is None and args.certificate_bytes is None, 'Capture accepts no existing certificate')
        result = capture()
    else:
        require(isinstance(args.certificate_sha256, str) and len(args.certificate_sha256) == 64 and
                all(c in '0123456789abcdef' for c in args.certificate_sha256) and
                isinstance(args.certificate_bytes, int) and args.certificate_bytes > 0,
                'Verify requires the caller-frozen certificate SHA256 and byte length')
        result = verify({'path': str(OUTPUTS['CERTIFICATE.json']), 'bytes': args.certificate_bytes,
                         'sha256': args.certificate_sha256})
    print(json.dumps(result, separators=(',', ':')))


if __name__ == '__main__':
    main()
