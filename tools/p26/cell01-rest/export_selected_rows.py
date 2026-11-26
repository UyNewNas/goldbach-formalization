#!/usr/bin/env python3
"""Audit only the two explicitly permitted Cell01 row selections; retain tar on cloud.

No compiler, Git command, network call, or Lean-source generation is performed.
Only selected accepted target object bodies are exported. Old supplier objects
are rehashed in place and remain in their already accepted caches.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import importlib.util
import io
import json
import math
import os
import re
import shlex
import sys
import tarfile

sys.dont_write_bytecode = True
MODES = ('normal', 'kernel', 'owned')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
TOOL = Path('tools/p26/cell01-rest')
PINNED = {
    'driver': 'ca58f8d847826d7d5db8d22637e3264a930defd6b3c63870595fdfe4b60ac27b',
    'mature_helper': '7f45487deec037f499f85fc904eb310350d883d08685a36be8ce4b8234f2ceb6',
    'verifier_manifest': '3a3a39ac807a91aa7b2cdf0e752c6021662a72f1bcbc9d0cdb9dbdb1eaf441d1',
    'supplier_manifest': 'a9d21432e21ac9e6083d900f48c2d33fadc75609924d6e50166ea53f28fa2769',
}
PACKAGES = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']
RECURRENCE = 'ImbalancedChen.P2Winner9HomogeneousRecurrence'
BOUNDED = 'ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess'
V1_EXPORTER_SHA256 = '6d60a4360f8c3f364a0e8b183831d8d50ba09c00db5a75f34fef94e56dde42f0'
SCENARIOS = ('c-tail-success', 'c-prefix-budget-pause')
C_ROWS = tuple(range(98, 144))
PREFIX_ROWS = tuple(range(98, 107))
TAIL_ROWS = tuple(range(107, 144))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(path, exists=True):
    path = Path(path).absolute()
    need('..' not in path.parts and not path.is_symlink() and path.resolve() == path,
         f'Noncanonical path: {path}')
    if exists:
        need(path.exists(), f'Missing file/directory: {path}')
    need(not ('row001' in path.name and 'completed' in path.name and path.name.endswith('.tar.xz')),
         'The blocked row001 completed archive is outside this audit')
    return path


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def fp(path):
    path = canonical(path)
    need(path.is_file(), f'Expected regular file: {path}')
    digest, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(data)
            size += len(data)
    return {'path': str(path), 'bytes': size, 'sha256': digest.hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(a.get(k) == b.get(k) for k in ('bytes', 'sha256'))


def read(path):
    return json.loads(canonical(path).read_text())


def body(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def imports(path):
    return re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', canonical(path).read_text())


class Audit:
    def __init__(self, stage):
        self.stage = stage
        self.watched, self.members = {}, {}

    def watch(self, path, expected=None, exact_path=False):
        actual = fp(path)
        if expected is not None:
            need(same(actual, expected), f'Changed bytes: {path}')
            if exact_path:
                need(actual == expected, f'Changed exact file identity: {path}')
        previous = self.watched.setdefault(actual['path'], actual)
        need(previous == actual, f'Input changed during review: {path}')
        return actual

    def add(self, path, role, expected=None, member=None):
        path = canonical(path)
        if member is None:
            need(path.is_relative_to(self.stage), f'Export escapes stage: {path}')
            member = path.relative_to(self.stage).as_posix()
        rel = PurePosixPath(member)
        need(member and not rel.is_absolute() and '..' not in rel.parts, 'Invalid member')
        actual = self.watch(path, expected)
        row = {'member': member, **actual, 'roles': [role]}
        if member in self.members:
            previous = self.members[member]
            need(previous['path'] == str(path) and same(previous, actual), 'Conflicting archive member')
            if role not in previous['roles']:
                previous['roles'].append(role)
        else:
            self.members[member] = row
        return actual

    def unchanged(self):
        for path, identity in self.watched.items():
            need(fp(path) == identity, f'Frozen review input changed: {path}')


def load_reviewed_driver(stage, run, audit):
    paths = {'driver': stage / TOOL / 'Cell01Batch_verify.py',
             'mature_helper': stage / TOOL / 'Geometry01Decoding_verify.py',
             'verifier_manifest': stage / TOOL / 'Cell01Batch_VERIFIER.json',
             'supplier_manifest': stage / 'Cell01Batch_SUPPLIERS.json'}
    for key, path in paths.items():
        actual = audit.add(path, key, run[key])
        need(actual == run[key] and actual['sha256'] == PINNED[key], f'Unreviewed {key}')
    sys.path.insert(0, str(stage / TOOL))
    spec = importlib.util.spec_from_file_location('reviewed_batch_driver', paths['driver'])
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    return driver


def historical_boundary(stage, registry, audit, driver, current_runtime):
    old = read(stage / 'evidence/row000/Cell01Row000_SUPPLIERS.json')
    old_run = read(stage / 'evidence/row000/RUN.json')
    old_success = read(stage / 'evidence/row000/SUCCESS.json')
    old_rows = {row['module']: row for row in old['suppliers']}
    need(len(old_rows) == len(old['suppliers']) == 398, 'Old 398-supplier boundary differs')
    need(set(registry) == set(old_rows) | {BOUNDED}, '399 suppliers are not old 398 plus bounded access')
    for module, row in old_rows.items():
        need(all(same(row[k], registry[module][k]) for k in ('source', 'object')), 'Old supplier identity differs')
    need(old['normal_only_suppliers'] == old_run['pending_supplier_kernel'] == [RECURRENCE], 'Historical pending boundary differs')
    need(old_run['full_supplier_kernel_closed'] is False and old_success['full_supplier_kernel_closed'] is False,
         'Historical P3 pending status was overwritten')
    need(all(old_success.get(k) == v for k, v in old_run.items()), 'Old RUN/SUCCESS differ')
    bounded_count = None
    for mode in MODES:
        base = stage / 'evidence/shared-bounded'
        result, command = read(base / (mode + '-result.json')), read(base / (mode + '-command.json'))
        need(all(result.get(k) == v for k, v in old_run.items()), 'Bounded access runtime differs')
        need(all(result.get(k) == v for k, v in command.items()), 'Bounded command/result differ')
        need(result['module'] == BOUNDED and result['mode'] == mode and result['status'] == 'succeeded'
             and result['exit_code'] == 0, 'Bounded access step failed')
        need(all(same(result[k], registry[BOUNDED][k]) for k in ('source', 'object')), 'Bounded source/object differ')
        audit.watch(base / (mode + '.log'), result['log'])
        flags = ['-j1', f'-M{old_run["rss_limit_bytes"] // 1024**2}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
        if mode == 'normal':
            expected = ['/toolchains/bin/lean', *flags, '-o', result['object']['path'], BOUNDED.replace('.', '/') + '.lean']
            need(result['object_before'] is None, 'Bounded normal overwrote an object')
        elif mode == 'kernel':
            expected = ['/toolchains/bin/leanchecker', '--verbose', BOUNDED]
            need(result['object_before'] == result['object'], 'Bounded kernel object differs')
            need((base / 'kernel.log').read_text().strip() == 'replaying ' + BOUNDED, 'Bounded kernel target differs')
        else:
            expected = ['/toolchains/bin/lean', *flags, result['audit_source']['path']]
            need(result['object_before'] == result['object'], 'Bounded owned object differs')
            audit.add(result['audit_source']['path'], 'accepted_shared_bounded_audit', result['audit_source'],
                      'prior-evidence/shared-bounded-owned-audit.lean')
            parsed = driver.parse_owned((base / 'owned.log').read_text(), BOUNDED)
            need(parsed == read(base / 'owned-declarations.json'), 'Bounded owned inventory differs')
            need(parsed['owned_declaration_count'] == result['owned_declaration_count'], 'Bounded owned count differs')
            bounded_count = parsed['owned_declaration_count']
        need(result['argv'] == expected, 'Bounded exact argv differs')
    base = stage / 'evidence/p1-recurrence'
    completion, accepted, result, command, prior_run, inputs = [read(base / name) for name in
        ('SUPPLIER_KERNEL_COMPLETION.json', 'ACCEPTED_STEP.json', 'result.json', 'command.json', 'RUN.json', 'INPUT_FINGERPRINTS.json')]
    need(completion['status'] == 'COMPLETE_BY_EXACT_SAME_SOURCE_AND_OBJECT_P1_KERNEL_RECEIPT'
         and completion['full_supplier_kernel_closed_at_original_P3_run'] is False
         and completion['original_P3_records_unchanged'] is True
         and completion['historical_pending_supplier_modules'] == [RECURRENCE]
         and completion['remaining_pending_supplier_kernel_modules'] == []
         and completion['supplier_kernel_closed_in_combined_evidence'] is True, 'Invalid recurrence historical join')
    for value in (accepted, result):
        need(value['module'] == RECURRENCE and value['mode'] == 'kernel' and value['status'] == 'succeeded', 'Recurrence receipt failed')
        need(same(value['source'], registry[RECURRENCE]['source']), 'Recurrence source join differs')
    need(result['exit_code'] == 0 and result['timed_out'] is False and result['error'] is None, 'Recurrence kernel did not finish')
    need(accepted['all_frozen_inputs_unchanged'] is True and accepted['object_sidecars'] == [], 'Recurrence frozen inputs differ')
    for identity in (accepted['object'], result['object_before'], completion['object']):
        need(same(identity, registry[RECURRENCE]['object']), 'Recurrence object join differs')
    need(same(completion['source'], registry[RECURRENCE]['source']), 'Recurrence completion source differs')
    for identity, name in [(accepted['command_result'], 'result.json'), (accepted['log'], 'output.log'),
                           (result['command'], 'command.json'), (result['log'], 'output.log'),
                           (result['input_fingerprints'], 'INPUT_FINGERPRINTS.json'),
                           (prior_run['input_fingerprints'], 'INPUT_FINGERPRINTS.json'),
                           (completion['P1_kernel_receipt'], 'ACCEPTED_STEP.json'),
                           (completion['P1_kernel_result'], 'result.json'), (completion['P1_kernel_log'], 'output.log')]:
        audit.watch(base / name, identity)
    need(all(result.get(k) == v for k, v in command.items()), 'Recurrence command/result differ')
    need(result['cwd'] == prior_run['project'] and result['LEAN_PATH'] == prior_run['LEAN_PATH'], 'Recurrence RUN context differs')
    need(result['argv'] == [prior_run['leanchecker_binary']['path'], '--verbose', RECURRENCE], 'Recurrence exact kernel argv differs')
    need((base / 'output.log').read_text().strip() == 'replaying ' + RECURRENCE, 'Recurrence log target differs')
    need(prior_run['mathlib_commit'] == MATHLIB_COMMIT and LEAN_COMMIT in prior_run['lean_version'], 'Recurrence runtime version differs')
    pins = {row['path']: row for row in inputs['files']}
    for identity in (accepted['source'], accepted['object']):
        need(pins.get(identity['path']) == identity, 'Recurrence source/object not frozen in historical inputs')
    for key in ('lean_binary', 'leanchecker_binary'):
        need(same(prior_run[key], audit.watch(current_runtime[key]['path'], current_runtime[key], exact_path=True)),
             'Recurrence compiler byte identity differs')
    return {'old_supplier_count': 398, 'shared_bounded_added': True, 'shared_bounded_owned_declarations': bounded_count,
            'historical_P3_pending_preserved': True, 'same_SHA_P1_recurrence_kernel_join_checked': True,
            'historical_P1_external_package_context_retained': True,
            'old_supplier_proof_commands_executed_by_export': 0}


class CommandParser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError('Invalid recorded verifier argv: ' + message)


def recorded_command(proof_mcp, stage, attempt, scenario):
    """Parse the actual direct MCP invocation, with no shell expansion or aliases."""
    need(scenario in SCENARIOS, 'Unsupported selection scenario')
    need(proof_mcp['status'] == 'succeeded' and proof_mcp['exit_code'] == 0
         and proof_mcp['output_truncated'] is False, 'MCP proof task did not exit successfully')
    argv = shlex.split(proof_mcp['command'])
    need(len(argv) >= 3 and Path(argv[0]).name in ('python', 'python3') and argv[1] == '-B'
         and argv[2] == str(stage / TOOL / 'Cell01Batch_verify.py'),
         'MCP command must directly invoke the exact frozen verifier with Python -B')
    options = [item for item in argv[3:] if item.startswith('--')]
    need(len(options) == len(set(options)) and all('=' not in item for item in options),
         'Duplicate or noncanonical recorded options')
    parser = CommandParser(add_help=False, allow_abbrev=False)
    parser.add_argument('--stage', required=True)
    parser.add_argument('--cache-root', required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--toolchain-bin', default='/toolchains/bin')
    parser.add_argument('--mathlib', default='/mathlib')
    parser.add_argument('--mathlib-packages')
    parser.add_argument('--wall-seconds', type=int, default=900)
    parser.add_argument('--rss-gib', type=int, default=6)
    parser.add_argument('--task-budget-seconds', type=int, default=3300)
    parser.add_argument('--row-start-reserve-seconds', type=int, default=180)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--batch', choices=['A', 'B', 'C'])
    group.add_argument('--rows', type=int, nargs='+')
    command = parser.parse_args(argv[3:])
    need(command.stage == str(stage) and command.attempt == attempt, 'MCP stage/attempt differs')
    need(120 <= command.task_budget_seconds <= 3300 and command.wall_seconds > 0
         and command.rss_gib > 0 and command.row_start_reserve_seconds >= 30,
         'Recorded resource limits are not legal verifier arguments')
    if scenario == 'c-tail-success':
        need(command.batch is None and command.rows == list(TAIL_ROWS),
             'Tail scenario requires exactly explicit --rows 107 through 143')
    else:
        need(command.batch == 'C' and command.rows is None,
             'Prefix scenario requires the original full --batch C invocation')
    return command


def select_acceptance(run, terminal, verifier, scenario, markers):
    """Accept no arbitrary subset, failed run, incomplete row or partial triple."""
    need(scenario in SCENARIOS, 'Unsupported selection scenario')
    need(verifier['batches']['C'] == list(C_ROWS), 'Frozen C partition differs')
    targets = {row['original_ordinal']: row for row in verifier['targets']}
    need(len(targets) == len(verifier['targets']) == 142 and set(targets) == set(range(2, 144)),
         'Frozen target series differs')
    for n, row in targets.items():
        need(row['module'] == f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite',
             'Frozen ordinal/module relation differs')
    need(all(terminal.get(k) == v for k, v in run.items()), 'Terminal/RUN context differs')
    need(terminal.get('frozen_inputs_unchanged') is True, 'Terminal inputs are not frozen')
    if scenario == 'c-tail-success':
        ordinals, marker = list(TAIL_ROWS), 'SUCCESS.json'
        need(set(markers) == {marker}, 'Tail requires SUCCESS without contradictory markers')
        need(run['batch_label'] is None and run['selected_ordinals'] == ordinals,
             'Tail RUN must retain the exact explicit row selection')
        need(terminal.get('status') == 'succeeded' and terminal.get('batch_complete') is True
             and terminal.get('accepted_targets') == len(ordinals), 'Tail selected run is not complete')
        need(terminal.get('remaining_ordinals', []) == [], 'Successful tail has remaining rows')
        status = 'PASS_EXACT_SELECTED_ROWS_EVIDENCE_AUDIT'
        remaining = []
    else:
        ordinals, marker = list(PREFIX_ROWS), 'PARTIAL.json'
        need(set(markers) == {marker}, 'Prefix requires PARTIAL without SUCCESS or STOPPED')
        need(run['batch_label'] == 'C' and run['selected_ordinals'] == list(C_ROWS),
             'Prefix RUN must select the original complete C partition')
        need(terminal.get('status') == 'BUDGET_PAUSE' and terminal.get('batch_complete') is False,
             'Only a genuine incomplete BUDGET_PAUSE can supply this prefix')
        need(terminal.get('where') == 'before_row' and terminal.get('module') is None
             and terminal.get('mode') is None, 'Prefix pause must occur before starting another row')
        need(terminal.get('remaining_ordinals') == list(TAIL_ROWS), 'Prefix remaining range differs')
        need('accepted_targets' not in terminal or terminal['accepted_targets'] == len(ordinals),
             'Partial marker overstates accepted target count')
        status = 'PASS_EXACT_ACCEPTED_PREFIX_EVIDENCE_AUDIT'
        remaining = list(TAIL_ROWS)
    need(terminal.get('completed_rows') == ordinals, 'Completed ordinals differ from the exact permitted selection')
    expected = [(targets[n]['module'], mode) for n in ordinals for mode in MODES]
    records = terminal['records']
    need([(row.get('module'), row.get('mode')) for row in records] == expected,
         'Exact row-major normal/kernel/owned record order or coverage differs')
    for record in records:
        refs = [key for key in ('receipt', 'reused_successful_receipt') if key in record]
        need(len(refs) == 1, 'Missing or ambiguous accepted step reference')
        expected_keys = {'module', 'mode', refs[0]} | ({'status'} if refs[0] == 'receipt' else set())
        need(set(record) == expected_keys, 'Record schema differs from the exact frozen verifier')
        reference = record[refs[0]]
        need(isinstance(reference, dict) and set(reference) == {'path', 'bytes', 'sha256'}
             and isinstance(reference['path'], str) and Path(reference['path']).is_absolute()
             and isinstance(reference['bytes'], int) and not isinstance(reference['bytes'], bool)
             and reference['bytes'] >= 0 and isinstance(reference['sha256'], str)
             and re.fullmatch(r'[0-9a-f]{64}', reference['sha256']),
             'Malformed accepted step fingerprint')
        if refs[0] == 'receipt':
            need(record.get('status') == 'succeeded', 'A failed or unfinished record is not accepted')
    return {'scenario': scenario, 'status': status, 'terminal_marker': marker,
            'source_terminal_status': terminal['status'], 'batch': run['batch_label'],
            'parent_batch': 'C', 'ordinals': ordinals, 'run_selected_ordinals': run['selected_ordinals'],
            'completed_rows': ordinals, 'remaining_ordinals': remaining,
            'batch_complete': terminal['batch_complete'],
            'full_C_batch_claimed': False, 'cross_context_aggregation_performed': False}


def bind_recorded_runtime(command, run):
    need(command.cache_root == run['cache_root'], 'MCP supplier cache differs')
    need(command.wall_seconds == run['wall_limit_seconds']
         and command.rss_gib * 1024**3 == run['rss_limit_bytes']
         and command.task_budget_seconds == run['task_budget_seconds'], 'MCP/RUN resource limits differ')
    toolchain = canonical(command.toolchain_bin)
    need(run['lean_binary']['path'] == str(toolchain / 'lean')
         and run['leanchecker_binary']['path'] == str(toolchain / 'leanchecker'),
         'MCP toolchain is not the recorded compiler/checker provider')
    mathlib = canonical(command.mathlib)
    packages = canonical(command.mathlib_packages or str(mathlib / '.lake/packages'))
    need(run['mathlib_packages_root'] == str(packages), 'MCP Mathlib package parent differs')
    return mathlib


def read_git_commit(mathlib, audit):
    """Resolve actual Git metadata by reading files only; never invoke Git."""
    metadata = []
    def contents(path):
        path = canonical(path)
        metadata.append(audit.watch(path))
        return path.read_text().strip()
    dotgit = canonical(mathlib / '.git')
    if dotgit.is_dir():
        gitdir = dotgit
    else:
        pointer = contents(dotgit)
        need(pointer.startswith('gitdir: ') and '\n' not in pointer, 'Invalid Mathlib gitdir pointer')
        value = Path(pointer[len('gitdir: '):])
        gitdir = canonical((mathlib / value).resolve() if not value.is_absolute() else value)
    head = contents(gitdir / 'HEAD')
    if re.fullmatch(r'[0-9a-f]{40}', head):
        return {'commit': head, 'mathlib': str(mathlib), 'metadata': metadata}
    need(head.startswith('ref: refs/'), 'Unrecognized Mathlib HEAD')
    ref = head[len('ref: '):]
    need('..' not in PurePosixPath(ref).parts and not PurePosixPath(ref).is_absolute(), 'Unsafe Git reference')
    common = gitdir
    if (gitdir / 'commondir').is_file():
        value = Path(contents(gitdir / 'commondir'))
        common = canonical((gitdir / value).resolve() if not value.is_absolute() else value)
    for directory in dict.fromkeys([gitdir, common]):
        if (directory / ref).is_file():
            commit = contents(directory / ref)
            need(re.fullmatch(r'[0-9a-f]{40}', commit), 'Invalid loose Git reference')
            return {'commit': commit, 'mathlib': str(mathlib), 'metadata': metadata}
    packed = contents(common / 'packed-refs')
    matches = [line.split()[0] for line in packed.splitlines()
               if not line.startswith(('#', '^')) and len(line.split()) == 2 and line.split()[1] == ref]
    need(len(matches) == 1 and re.fullmatch(r'[0-9a-f]{40}', matches[0]), 'Missing/ambiguous packed Git reference')
    return {'commit': matches[0], 'mathlib': str(mathlib), 'metadata': metadata}


def exact_attempt_inventory(root, audit):
    """Do not hide a failed/uncompleted row behind a valid shorter records list."""
    expected = {row['path'] for row in audit.members.values() if Path(row['path']).is_relative_to(root)}
    actual = set()
    for path in root.rglob('*'):
        path = canonical(path)
        if path.is_file():
            actual.add(str(path))
    need(actual == expected, 'Attempt has unselected, failed, incomplete or unaccounted evidence files')


def mcp_measurements(proof_mcp):
    fields = [key for key in ('peak_memory_bytes', 'memory_peak_bytes') if key in proof_mcp]
    need(len(fields) == 1, 'Missing or ambiguous MCP peak-memory field')
    value = proof_mcp[fields[0]]
    runtime = proof_mcp['runtime_seconds']
    need(isinstance(value, int) and not isinstance(value, bool) and value >= 0
         and isinstance(runtime, (int, float)) and not isinstance(runtime, bool)
         and math.isfinite(runtime) and runtime >= 0, 'Invalid MCP measurements')
    return {'proof_MCP_task_id': proof_mcp['task_id'], 'proof_MCP_runtime_seconds': runtime,
            'proof_MCP_peak_memory_bytes': value, 'proof_MCP_peak_memory_field': fields[0],
            'proof_MCP_memory_peak_source': proof_mcp.get('memory_peak_source')}


def review(stage, attempt, scenario, mcp_path):
    audit = Audit(stage)
    root = canonical(stage / 'verification' / attempt)
    run = read(root / 'RUN.json')
    need(run['attempt'] == attempt and run['stage'] == str(stage), 'Wrong selected RUN')
    audit.watch(mcp_path)
    proof_mcp = read(mcp_path)
    command = recorded_command(proof_mcp, stage, attempt, scenario)
    marker = 'SUCCESS.json' if scenario == 'c-tail-success' else 'PARTIAL.json'
    audit.watch(root / marker)
    success = read(root / marker)
    markers = {name for name in ('SUCCESS.json', 'PARTIAL.json', 'STOPPED.json') if (root / name).exists()}
    driver = load_reviewed_driver(stage, run, audit)
    verifier = read(stage / TOOL / 'Cell01Batch_VERIFIER.json')
    supplier = read(stage / 'Cell01Batch_SUPPLIERS.json')
    selection = select_acceptance(run, success, verifier, scenario, markers)
    ordinals = selection['ordinals']
    mathlib = bind_recorded_runtime(command, run)
    git_state = read_git_commit(mathlib, audit)
    targets = {row['original_ordinal']: row for row in verifier['targets']}
    need(len(targets) == len(verifier['targets']) == 142 and set(targets) == set(range(2, 144)), 'Frozen target series differs')
    registry = {row['module']: row for row in supplier['suppliers']}
    need(len(registry) == len(supplier['suppliers']) == supplier['existing_supplier_count'] == 399, 'Supplier inventory differs')
    need(supplier['normal_only_suppliers'] == [] and supplier['full_supplier_kernel_closed'] is True, 'Supplier kernel join not complete')
    need(run['cloud_source_generation'] is False and run['suppliers_recompiled'] is False
         and run['full_supplier_kernel_closed'] is True and run['accepted_supplier_count'] == 399, 'Unexpected acceptance scope')
    need(run['integral_claimed'] is False and run['P2_6_complete_claimed'] is False, 'Scope expanded')
    need(run['mathlib_commit'] == MATHLIB_COMMIT and LEAN_COMMIT in run['lean_version'], 'Wrong runtime version')
    need(git_state['commit'] == MATHLIB_COMMIT, 'Current Mathlib HEAD changed')
    for key in ('lean_binary', 'leanchecker_binary'):
        audit.watch(run[key]['path'], run[key], exact_path=True)
    need(run['required_mathlib_packages'] == PACKAGES and run['cwd'] == str(stage / 'project'), 'Runtime paths differ')
    package_parent = canonical(run['mathlib_packages_root'])
    expected_packages = [str(package_parent / name / '.lake/build/lib/lean') for name in PACKAGES]
    if (package_parent / 'Cli/.lake/build/lib/lean').is_dir():
        expected_packages.append(str(package_parent / 'Cli/.lake/build/lib/lean'))
    need(run['mathlib_package_object_roots'] == expected_packages, 'Package path inventory differs')
    lean_paths = [str(stage / 'objects'), *expected_packages, str(mathlib / '.lake/build/lib/lean')]
    need(run['LEAN_PATH'].split(os.pathsep) == lean_paths, 'LEAN_PATH differs')
    for path in lean_paths[1:]:
        need(canonical(path).is_dir() and not (Path(path) / 'ImbalancedChen').exists(), 'Missing package or project fallback')
    stable_keys = ['lean_version', 'mathlib_commit', 'lean_binary', 'leanchecker_binary', 'supplier_manifest',
                   'mathlib_package_object_roots', 'LEAN_PATH', 'cwd']
    digest = hashlib.sha256(json.dumps({k: run[k] for k in stable_keys}, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    need(digest == run['runtime_context_sha256'], 'Runtime context digest differs')
    for name in ('RUN.json', marker, 'INPUT_FINGERPRINTS.json', 'SUPPLIER_INSTALLATION.json'):
        audit.add(root / name, 'batch_context')
    for row in verifier['frozen_evidence']:
        audit.add(stage / row['archive_member'], row.get('role', 'frozen_control'), row)
    inputs = read(root / 'INPUT_FINGERPRINTS.json')
    installation = read(root / 'SUPPLIER_INSTALLATION.json')
    need(audit.watch(root / 'INPUT_FINGERPRINTS.json') == run['input_fingerprints'], 'Input snapshot RUN pin differs')
    need(audit.watch(root / 'SUPPLIER_INSTALLATION.json') == run['supplier_installation'], 'Installation RUN pin differs')
    need(inputs['cloud_source_generation'] is False and installation['suppliers_recompiled'] is False, 'Supplier generation/replay recorded')
    need(installation['single_project_object_root'] == str(stage / 'objects') and installation['supplier_modules'] == 399, 'Wrong installation namespace')
    cache = canonical(run['cache_root'])
    need(not stage.is_relative_to(cache) and not cache.is_relative_to(stage), 'Cache/stage overlap')
    entries = {(row['module'], row['kind']): row for row in installation['entries']}
    need(len(entries) == len(installation['entries']) == 798, 'Incomplete/duplicate installation inventory')
    frozen_expected = {str(stage / TOOL / name) for name in ['Cell01Batch_verify.py', 'Geometry01Decoding_verify.py', 'Cell01Batch_VERIFIER.json']}
    frozen_expected.add(str(stage / 'Cell01Batch_SUPPLIERS.json'))
    frozen_expected.update(str(stage / row['archive_member']) for row in verifier['frozen_evidence'])
    supplier_sequence, graph = [], {}
    for module, row in registry.items():
        relative = Path(module.replace('.', '/'))
        for kind, directory, suffix in [('source', 'project', '.lean'), ('object', 'objects', '.olean')]:
            provider, installed = cache / directory / relative.with_suffix(suffix), stage / directory / relative.with_suffix(suffix)
            entry = entries[module, kind]
            need(entry['method'] in {'hardlink', 'cross_filesystem_copy', 'existing_identical'}, 'Unexpected installation method')
            for key, path in [('source', provider), ('installed', installed)]:
                actual = audit.watch(path, row[kind])
                need(actual == entry[key], 'Supplier exact path/pin mismatch')
                frozen_expected.add(str(path))
            supplier_sequence.append([module, kind, row[kind]['bytes'], row[kind]['sha256']])
        graph[module] = imports(stage / 'project' / relative.with_suffix('.lean'))
        need(graph[module] == row['project_imports'], 'Actual supplier import graph differs')
    for target in targets.values():
        module = target['module']
        need(module == f'ImbalancedChen.P2OriginalSaving19Cell01Row{target["original_ordinal"]:03d}Finite', 'Wrong ordinal/module')
        for path, identity in [(stage / 'project' / (module.replace('.', '/') + '.lean'), target['source']),
                               (stage / target['audit_relative_path'], target['audit'])]:
            audit.watch(path, identity)
            frozen_expected.add(str(path))
    input_map = {row['path']: row for row in inputs['files']}
    need(len(input_map) == len(inputs['files']) and set(input_map) == frozen_expected, 'Incomplete frozen-input inventory')
    for path, identity in input_map.items():
        audit.watch(path, identity, exact_path=True)
    history = historical_boundary(stage, registry, audit, driver, run)
    ordered = [(targets[n]['module'], mode) for n in ordinals for mode in MODES]
    need([(row['module'], row['mode']) for row in success['records']] == ordered, 'Selected three-step order/coverage mismatch')
    selected_modules = {targets[n]['module'] for n in ordinals}
    all_modules = set(registry) | {row['module'] for row in targets.values()}
    object_names = set()
    for path in (stage / 'objects').rglob('*'):
        canonical(path)
        if path.is_file():
            need(path.suffix == '.olean', 'Unexpected object sidecar')
            module = str(path.relative_to(stage / 'objects').with_suffix('')).replace('/', '.')
            need(module in all_modules, 'Unregistered project object')
            object_names.add(module)
    need(set(registry) | selected_modules <= object_names, 'Missing checked project object')
    selected_objects, rows, steps, union = {}, [], [], set()
    for n in ordinals:
        target = targets[n]
        module = target['module']
        source_path = stage / 'project' / (module.replace('.', '/') + '.lean')
        object_path = stage / 'objects' / (module.replace('.', '/') + '.olean')
        audit_path = stage / target['audit_relative_path']
        source = audit.add(source_path, 'accepted_target_source', target['source'])
        obj = audit.add(object_path, 'new_accepted_target_object')
        audit_source = audit.add(audit_path, 'complete_owned_audit_source', target['audit'])
        selected_objects[module] = obj
        graph[module] = imports(source_path)
        closure, active = set(), set()

        def visit(name):
            need(name in graph and name not in active, 'Missing/cyclic project dependency')
            if name in closure:
                return
            active.add(name)
            for parent in graph[name]:
                visit(parent)
            active.remove(name)
            closure.add(name)

        visit(module)
        need(closure == set(registry) | {module} and len(closure) == 400, 'Per-owner project closure differs')
        chain, owned = [], None
        for mode in MODES:
            record = success['records'][len(steps)]
            reference = record.get('receipt') or record.get('reused_successful_receipt')
            need(isinstance(reference, dict), 'Missing step reference')
            receipt_path = canonical(reference['path'])
            relative = receipt_path.relative_to(stage / 'verification').parts
            need(len(relative) == 3 and relative[1:] == (module.split('.')[-1], mode + '-result.json'), 'Receipt module/mode path differs')
            need(audit.watch(receipt_path, reference, exact_path=True) == reference, 'Result reference differs')
            result = driver.validated_receipt(receipt_path, module, mode, source, obj, audit_source, run)
            need(result is not None and result['original_ordinal'] == n, 'Strict reviewed validator rejected step')
            need(result['source'] == source and result['object'] == obj, 'Three-step current source/object identity differs')
            need(result['status'] == 'succeeded' and result['exit_code'] == 0, 'Unsuccessful step')
            for field, expected_path in [('command', receipt_path.with_name(mode + '-command.json')),
                                         ('log', receipt_path.with_name(mode + '.log'))]:
                need(result[field] == audit.add(expected_path, 'accepted_step_' + field, result[field]), 'Step evidence exact path differs')
            old_run_path = receipt_path.parent.parent / 'RUN.json'
            audit.add(old_run_path, 'accepted_step_RUN')
            audit.add(receipt_path, 'accepted_step_result', reference)
            for key, name in [('input_fingerprints', 'INPUT_FINGERPRINTS.json'), ('supplier_installation', 'SUPPLIER_INSTALLATION.json')]:
                path = old_run_path.with_name(name)
                need(result[key] == audit.add(path, 'accepted_step_' + key, result[key]), 'Step frozen context reference differs')
            log = Path(result['log']['path']).read_text()
            if mode == 'kernel':
                need(log.strip() == 'replaying ' + module, 'Kernel log does not identify exact target')
            elif mode == 'owned':
                owned_path = receipt_path.with_name('owned-declarations.json')
                need(result['owned_declarations'] == audit.add(owned_path, 'complete_owned_inventory_types_axioms', result['owned_declarations']), 'Owned exact path differs')
                owned = driver.parse_owned(log, module)
                need(owned == read(owned_path), 'Owned log/file differs')
                markers = [line[len('P26_GEOMETRY01_AUDIT_IMPORTS '):] for line in log.splitlines()
                           if line.startswith('P26_GEOMETRY01_AUDIT_IMPORTS ')]
                need(len(markers) == 1, 'Missing/duplicate import inventory')
                imported = json.loads(markers[0])
                need(len(imported) == len(set(imported)), 'Duplicate imported module names')
                need({name for name in imported if name.startswith('ImbalancedChen.')} == closure, 'Actual owned import closure differs')
                need(set(owned['axioms_union']) <= ALLOWED, 'Forbidden transitive axiom')
                union.update(owned['axioms_union'])
            need(math.isfinite(result['elapsed_seconds']) and result['elapsed_seconds'] >= 0
                 and isinstance(result['peak_rss_bytes'], int) and result['peak_rss_bytes'] >= 0, 'Invalid measurements')
            chain.append(reference)
            steps.append({'module': module, 'ordinal': n, 'mode': mode, 'receipt': reference,
                          'disposition': 'executed' if 'receipt' in record else 'reused',
                          'elapsed_seconds': result['elapsed_seconds'], 'peak_rss_bytes': result['peak_rss_bytes'],
                          'owned_declaration_count': result.get('owned_declaration_count')})
        row_path = root / module.split('.')[-1] / 'ROW_ACCEPTED.json'
        audit.add(row_path, 'three_step_row_acceptance')
        row = read(row_path)
        need(row['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED' and row['module'] == module and row['original_ordinal'] == n,
             'Row acceptance labels differ')
        need(row['source'] == source and row['object'] == obj and row['audit'] == audit_source and row['chain'] == chain,
             'Row acceptance chain differs')
        need(row['runtime_context_sha256'] == digest and row['owned_declaration_count'] == owned['owned_declaration_count'], 'Row acceptance inventory/context differs')
        rows.append({'ordinal': n, 'module': module, 'source': source, 'object': obj, 'audit': audit_source,
                     'owned_declaration_count': owned['owned_declaration_count'], 'project_closure': 400,
                     'serialized_environment_and_printed_names_equal': True, 'complete_types_checked': True,
                     'transitive_axioms': owned['axioms_union'], 'chain': chain})
    exact_attempt_inventory(root, audit)
    measurements = mcp_measurements(proof_mcp)
    audit.add(mcp_path, 'independent_MCP_proof_task_receipt', member='exporter/PROOF_MCP_TASK.json')
    audit.add(Path(__file__).absolute(), 'independent_exporter_reviewer_source', member='exporter/export_selected_rows.py')
    audit.unchanged()
    report = {'schema': 'p26_cell01_selected_rows_independent_review_v1', **selection,
        'attempt': attempt, 'stage': str(stage),
        'mathlib_checkout_check': git_state, 'MCP_measurements': measurements,
        'base_exporter_sha256': V1_EXPORTER_SHA256,
        'accepted_targets': len(rows), 'accepted_steps': len(steps),
        'step_counts': {mode: sum(item['mode'] == mode for item in steps) for mode in MODES},
        'newly_executed_steps': sum(item['disposition'] == 'executed' for item in steps),
        'reused_steps': sum(item['disposition'] == 'reused' for item in steps),
        'owned_declarations': sum(row['owned_declaration_count'] for row in rows), 'axioms_union': sorted(union),
        'complete_owned_inventory_types_transitive_axioms_checked': True,
        'old_suppliers': 399, 'supplier_source_object_entries': 798, 'supplier_files_rehashed_in_cache_and_stage': 1596,
        'supplier_inventory_sha256': hashlib.sha256(json.dumps(sorted(supplier_sequence), separators=(',', ':')).encode()).hexdigest(),
        'input_fingerprint_files_checked': len(input_map), 'actual_project_objects_at_review': len(object_names),
        'per_owner_project_closure': 400, 'selected_batch_project_closure': 399 + len(rows),
        'runtime_context_sha256': digest, 'runtime_context_checked': True, 'supplier_history': history,
        'step_elapsed_sum_seconds': sum(row['elapsed_seconds'] for row in steps),
        'sampled_Lean_process_tree_peak_bytes': max(row['peak_rss_bytes'] for row in steps),
        'proof_MCP_task': proof_mcp, 'rows': rows, 'steps': steps,
        'old_supplier_object_bodies_included': False, 'new_target_object_bodies': len(rows),
        'scope': 'Original cell01 finite arithmetic and five prefix-floor conditions only for the listed rows; no OriginalFloorTransport/analytic/integral bridge acceptance.',
        'other_batches_claimed': False, 'P2_6_complete': False, 'Lean_executed_by_reviewer': False,
        'Git_executed_by_reviewer': False, 'blocked_row001_completed_archive_read': False,
        'full_archive_automatically_transferred': False}
    return audit, report


def export(audit, report, output):
    output = canonical(output, exists=False)
    need(not output.exists(), 'Refusing to replace an existing export directory')
    need(not output.is_relative_to(audit.stage) and not audit.stage.is_relative_to(output), 'Export directory overlaps proof stage')
    need({row['member'] for row in audit.members.values() if row['member'].startswith('objects/')} ==
         {'objects/' + row['module'].replace('.', '/') + '.olean' for row in report['rows']}, 'Export object selection differs')
    report_data = body(report)
    members = [dict(row) for _, row in sorted(audit.members.items())]
    members.append({'member': 'INDEPENDENT_REVIEW.json', **pin(report_data), 'roles': ['independent_review_report']})
    selection_fields = ['scenario', 'status', 'terminal_marker', 'source_terminal_status', 'batch',
                        'parent_batch', 'ordinals', 'run_selected_ordinals', 'completed_rows',
                        'remaining_ordinals', 'batch_complete', 'full_C_batch_claimed',
                        'cross_context_aggregation_performed']
    manifest = {'schema': 'p26_cell01_selected_rows_cloud_export_v1',
                **{key: report[key] for key in selection_fields},
                'attempt': report['attempt'], 'members': members,
                'accepted_targets': report['accepted_targets'], 'accepted_steps': report['accepted_steps'],
                'owned_declarations': report['owned_declarations'], 'new_target_objects': report['new_target_object_bodies'],
                'old_supplier_object_bodies_included': False, 'archive_retained_on_cloud': True,
                'Lean_executed_for_export': False, 'P2_6_complete': False}
    manifest_data = body(manifest)
    output.mkdir(parents=True, exist_ok=False)
    tar_path = output / 'evidence.tar.xz'
    partial = output / 'evidence.tar.xz.partial'
    with partial.open('xb') as stream:
        with tarfile.open(fileobj=stream, mode='w:xz', preset=6) as archive:
            for row in members:
                data = report_data if row['member'] == 'INDEPENDENT_REVIEW.json' else canonical(row['path']).read_bytes()
                need(same(pin(data), row), 'Member changed before packing')
                info = tarfile.TarInfo(row['member'])
                info.type, info.size, info.mode, info.mtime = tarfile.REGTYPE, len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
            info = tarfile.TarInfo('EXPORT_MANIFEST.json')
            info.size, info.mode, info.mtime = len(manifest_data), 0o644, 0
            archive.addfile(info, io.BytesIO(manifest_data))
    expected, seen = {row['member']: row for row in members}, set()
    with tarfile.open(partial, 'r:xz') as archive:
        for item in archive:
            name = PurePosixPath(item.name)
            need(item.isfile() and not name.is_absolute() and '..' not in name.parts and item.name not in seen, 'Unsafe/duplicate tar member')
            seen.add(item.name)
            data = archive.extractfile(item).read()
            if item.name == 'EXPORT_MANIFEST.json':
                need(data == manifest_data, 'Embedded export manifest changed')
            else:
                need(item.name in expected and same(pin(data), expected[item.name]), 'Tar member does not match frozen manifest')
    need(seen == set(expected) | {'EXPORT_MANIFEST.json'}, 'Incomplete archive')
    audit.unchanged()
    os.link(partial, tar_path)
    partial.unlink()
    for name, data in [('EXPORT_MANIFEST.json', manifest_data), ('INDEPENDENT_REVIEW.json', report_data)]:
        with (output / name).open('xb') as stream:
            stream.write(data)
    summary = {k: report[k] for k in ['status', 'batch', 'attempt', 'accepted_targets', 'accepted_steps', 'step_counts',
        'newly_executed_steps', 'reused_steps', 'owned_declarations', 'axioms_union', 'old_suppliers',
        'supplier_files_rehashed_in_cache_and_stage', 'input_fingerprint_files_checked', 'runtime_context_sha256',
        'step_elapsed_sum_seconds', 'sampled_Lean_process_tree_peak_bytes', 'old_supplier_object_bodies_included',
        'new_target_object_bodies', 'P2_6_complete']}
    summary.update({key: report[key] for key in selection_fields})
    summary.update({'archive': fp(tar_path), 'manifest': fp(output / 'EXPORT_MANIFEST.json'),
        'review_report': fp(output / 'INDEPENDENT_REVIEW.json'), 'listed_members': len(members), 'archive_members': len(seen),
        'archive_readback_all_members_passed': True, 'watched_input_files_unchanged_after_export': len(audit.watched),
        'full_archive_retained_on_cloud': True, 'archive_locally_recovered': False,
        'blocked_row001_completed_archive_read_or_transferred': False,
        'recurrence_same_SHA_join_checked_historical_pending_preserved': True,
        **report['MCP_measurements'],
        'Lean_invoked': False, 'Git_invoked': False})
    with (output / 'SUMMARY.json').open('xb') as stream:
        stream.write(body(summary))
    return summary


def main():
    need(sys.flags.optimize == 0, 'Run without Python optimization')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--scenario', choices=SCENARIOS, required=True)
    parser.add_argument('--proof-mcp-receipt', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    need(re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt), 'Invalid attempt name')
    stage = canonical(args.stage)
    audit, report = review(stage, args.attempt, args.scenario, canonical(args.proof_mcp_receipt))
    print(json.dumps({'event': 'STRICT_SELECTED_ROWS_AUDIT_PASSED', 'scenario': args.scenario,
                      'batch_complete': report['batch_complete'], 'full_C_batch_claimed': False,
                      'targets': report['accepted_targets'], 'steps': report['accepted_steps'],
                      'owned_declarations': report['owned_declarations']}), flush=True)
    if args.check_only:
        return
    need(args.output is not None, 'An explicit fresh cloud output directory is required')
    print(json.dumps(export(audit, report, args.output)), flush=True)


if __name__ == '__main__':
    main()
