#!/usr/bin/env python3
"""Package original P1.5 owner evidence; never execute a checker, Git, or Lean.

This is a local export-integrity and publication assembler. The mathematical
acceptance authority remains the immutable original adapters and their actual
independent --check receipts. No synthetic receipt or replacement validator is
created here. Both owners must have complete real exports before any final
publication directory or PASS summary is written.
"""

from pathlib import Path, PurePosixPath
import argparse
import ast
import base64
import hashlib
import json
import re
import sys
import zlib


HERE = Path(__file__).resolve().parent
PACKET = 'docs/p1/20261127/p15-partition-group-log-acceptance'
PARENT = 'ce08ba304bafb7732c8fd9f27553822f87cfb7d0'
REMOTE_ROOT = '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1'
RUNTIME_SHA = '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
STANDARD_AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}
OWNERS = {
    'partition': {
        'module': 'ImbalancedChen.P1SignedExitPartition',
        'commit': '7296a9659fbf34773ec03f437860c14073b3a638',
        'source': {'bytes': 15972, 'sha256': '19f59a09107d934a8230d58a11afd256dd6134d7e2bba958a4144331f191249c'},
        'original': {'bytes': 15982, 'sha256': 'cb4d4bb096d7de762cb23925af58624736bcfd753251f348b352acc67bdd2ad9'},
        'adapter': {'bytes': 31065, 'sha256': '208fca4558eca8021837b3a2ca992eb6c071a4c9c33893f98a9f93a183582c57'},
        'adapter_name': 'run_partition.py',
        'source_packet': 'docs/p1/20261127/p15-signed-exit-partition',
        'formal_task': 'job_5fbfb818f8f24d439f519edc1d22176b',
        'readonly_task': 'job_d2a04ab9365246faa0b39e61f510694b',
        'operation': 'signed-exit-partition-operation',
        'outer_command': 'serialized-partition',
        'stage_receipt': 'PARTITION_STAGE_RECEIPT.json',
        'stage_schema': 'p15_partition_stage_v1',
        'export_schema': 'p15_partition_exact_acceptance_export_v1',
        'envelope_schema': 'p15_compressed_partition_acceptance_export_v1',
        'readonly_root': '/workspace/p1-complete-proof/20261127-p15-partition-readonly-v1',
        'source_identity_key': 'new_source_sha256',
        'stage_script': 'transport/partition/stage_run_partition.py',
        'export_script': 'transport/partition/export_partition_acceptance.py',
    },
    'group-log': {
        'module': 'ImbalancedChen.P5OriginalGroupLogAbelVariation',
        'commit': 'ce08ba304bafb7732c8fd9f27553822f87cfb7d0',
        'source': {'bytes': 10005, 'sha256': 'dc2870dd9a94a2f6f1dfe3e8872e8c4ba3c541cb58ec3595fd406f1910db7f73'},
        'original': {'bytes': 9607, 'sha256': '0cd74710f8ec890412e35e28e3985e9eceff6d52157b12a24c0873d9c50fe3d2'},
        'adapter': {'bytes': 21852, 'sha256': '9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057'},
        'adapter_name': 'run_group_log.py',
        'source_packet': 'docs/p1/20261127/p15-group-log-abel',
        'formal_task': 'job_67db0441349a4ad58ecacd1480001ceb',
        'readonly_task': 'job_9d92c26f45804a4a954b05bf94ad82f5',
        'operation': 'group-log-operation',
        'outer_command': 'serialized-group-log',
        'stage_receipt': 'GROUPLOG_STAGE_RECEIPT.json',
        'stage_schema': 'p15_group_log_stage_v1',
        'export_schema': 'p15_group_log_exact_acceptance_export_v1',
        'envelope_schema': 'p15_compressed_group_log_acceptance_export_v1',
        'readonly_root': '/workspace/p1-complete-proof/20261127-p15-group-log-readonly-v1',
        'source_identity_key': 'new_sha256',
        'stage_script': 'transport/group-log/stage_run_group_log.py',
        'export_script': 'transport/group-log/export_group_log_acceptance.py',
    },
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def document(raw):
    return json.loads(raw, object_pairs_hook=unique_pairs)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n').encode()


def relative(value):
    need(isinstance(value, str) and value and '\\' not in value, 'invalid relative path')
    path = PurePosixPath(value)
    need(not path.is_absolute() and path.as_posix() == value and
         all(part not in ('', '.', '..') for part in path.parts), 'unsafe relative path: ' + value)
    return value


def regular(path):
    path = Path(path)
    need(path.is_absolute() and path.resolve() == path and path.is_file() and
         not path.is_symlink(), 'expected existing absolute regular file: ' + str(path))
    return path.read_bytes()


def pinned(row):
    need(isinstance(row, dict) and set(row) == {'local', 'bytes', 'sha256'}, 'missing exact local file pin')
    need(type(row['bytes']) is int and row['bytes'] >= 0 and
         re.fullmatch('[0-9a-f]{64}', row['sha256'] or ''), 'invalid bytes/SHA256 pin')
    raw = regular(row['local'])
    need(fingerprint(raw) == {k: row[k] for k in ('bytes', 'sha256')}, 'file pin differs: ' + row['local'])
    return raw


def requirements():
    return {
        'schema': 'p15_dual_owner_publication_requirements_v1',
        'status': 'UNBOUND_REQUIRES_BOTH_REAL_INDEPENDENT_READONLY_EXPORTS',
        'packet': PACKET,
        'parent_source_commit': PARENT,
        'owners': {name: {
            'module': spec['module'], 'source_acceptance_commit': spec['commit'],
            'formal_task': spec['formal_task'], 'readonly_task_if_already_known': spec['readonly_task'],
            'required_pinned_local_files': ['formal_provider', 'formal_stdout', 'readonly_provider', 'export_stdout'],
            'required_raw_root': 'Absolute root containing all four original exported group directories.',
            'required_export_groups': [name + '-' + role for role in ('operation', 'owner', 'readonly', 'stage')],
            'completion': 'Both provider tasks succeeded with exit 0; distinct later readonly task; exact original --check returns REVALIDATED.',
        } for name, spec in OWNERS.items()},
        'assembly_does_not_execute_git_lean_or_original_checkers': True,
        'final_PASS_or_owner_counts_generated_before_all_inputs_ready': False,
        'original_registry': {'registered': 21, 'accepted': 18, 'unchanged': True},
        'new_owners_listed_separately': list(OWNERS),
        'whole_P1_5_complete': False,
    }


def load_support():
    raw = regular(HERE / 'SUPPORT_BINDINGS.json')
    bindings = document(raw)
    need(isinstance(bindings, list) and bindings, 'missing frozen support list')
    result = {}
    for row in bindings:
        need(set(row) == {'local', 'path', 'bytes', 'sha256'}, 'invalid support row')
        rel = relative(row['path'])
        need(rel not in result and not rel.startswith(('raw/', 'owners/')), 'duplicate or reserved support path')
        result[rel] = pinned({k: row[k] for k in ('local', 'bytes', 'sha256')})
    required = {
        'metadata/SOURCE_PUBLICATION_VERIFICATION.json',
        'metadata/PARTITION_NOT_STARTED_PROVIDER_TASK.json',
        'metadata/GROUP_LOG_V5_PROBE_PROVIDER_TASK.json',
        'reviews/PARTITION_INPUTS_BINDING_REVIEW_208F.json',
        'reviews/GROUPLOG_INPUTS_BINDING_REVIEW_9F618.json',
        'reviews/PARTITION_ADAPTER_REVIEW_451A.json',
        'reviews/GROUPLOG_ADAPTER_REVIEW_2D284.json',
        'reviews/MEDIUM_SOURCE_REVIEW.md', 'reviews/GROUPLOG_SOURCE_REVIEW.json',
        'next-policy/probe_policy_template.py', 'next-policy/NEXT_POLICY_READINESS.json',
        'next-policy/STATIC_REVIEW.json', 'next-policy/LOCAL_TEMPLATE_CHECK.json',
    } | {spec[key] for spec in OWNERS.values() for key in ('stage_script', 'export_script')}
    need(required <= result.keys(), 'required review, transport, or next Policy support missing')
    # A reusable next step remains unbound even after the parent evidence is available.
    tree = ast.parse(result['next-policy/probe_policy_template.py'])
    values = [node.value for node in tree.body if isinstance(node, ast.Assign) and
              any(isinstance(t, ast.Name) and t.id == 'PARTITION_BINDING' for t in node.targets)]
    need(len(values) == 1 and isinstance(values[0], ast.Constant) and values[0].value is None,
         'next Policy template must remain UNBOUND in this packet')
    policy = document(result['next-policy/NEXT_POLICY_READINESS.json'])
    need(policy['dependencies']['partition_acceptance_binding'] is None and
         policy['template']['partition_binding_is_none'] is True and
         policy['template']['pre_filled_owned_or_public_counts'] is False,
         'next Policy preparation acquired an acceptance or prefills counts')
    failed = document(result['metadata/PARTITION_NOT_STARTED_PROVIDER_TASK.json'])
    need(failed['task_id'] == 'job_9db0b07f37bf40caa314b1c6637647d7' and
         failed['status'] == 'resource_unavailable' and failed['started_at'] is None and
         failed['exit_code'] is None and failed['output_bytes'] == 0,
         'superseded provider event is not established as pre-execution only')
    published = document(result['metadata/SOURCE_PUBLICATION_VERIFICATION.json'])
    for name, key in [('partition', 'partition_source_publication'), ('group-log', 'group_log_source_publication')]:
        spec = OWNERS[name]
        entry = published[key]
        need(entry['commit'] == spec['commit'] and entry['exact_blob_sha_and_size_verified'] is True,
             'original source publication verification differs: ' + name)
        bypath = {row['path']: row for row in entry['files']}
        source_path = spec['module'].replace('.', '/') + '.lean'
        for path, pin in [(source_path, spec['source']),
                          (spec['source_packet'] + '/' + spec['adapter_name'], spec['adapter'])]:
            row = bypath[path]
            need({k: row[k] for k in ('bytes', 'sha256')} == pin, 'published source/adapter identity differs')
    return raw, result


def script_in_task(task, script):
    # Preserve and compare the exact submitted heredoc body, including final LF.
    command = task['command']
    need(isinstance(command, str) and '\n' in command, 'missing provider command text')
    first, rest = command.split('\n', 1)
    match = re.fullmatch(r"python3 - <<'([A-Za-z0-9_]+)'", first)
    need(match is not None, 'unexpected transport wrapper; inspect original provider metadata')
    ending = '\n' + match.group(1)
    need(rest.endswith(ending) or rest.endswith(ending + '\n'), 'unterminated transport heredoc')
    body = rest[:-(len(ending) + (1 if rest.endswith(ending + '\n') else 0))]
    need(body.encode() == script, 'submitted provider script differs from preserved transport script')


def successful_provider(raw, expected_task, script):
    task = document(raw)
    need(re.fullmatch('job_[0-9a-f]+', task['task_id']) and task.get('job_id') == task['task_id'],
         'provider task identity missing')
    if expected_task is not None:
        need(task['task_id'] == expected_task, 'unexpected provider task identity')
    need(task['status'] == 'succeeded' and type(task['exit_code']) is int and task['exit_code'] == 0 and
         isinstance(task['started_at'], (int, float)) and isinstance(task['finished_at'], (int, float)) and
         task['finished_at'] >= task['started_at'] and task['output_truncated'] is False and
         task['cancel_requested'] is False, 'provider task has not completed successfully')
    script_in_task(task, script)
    return task


def load_export(raw, spec, name, raw_root):
    envelope = document(raw)
    need(envelope['schema'] == spec['envelope_schema'] and envelope['encoding'] == 'zlib+base64' and
         envelope['status'] == 'REVALIDATED', 'missing original successful readonly export envelope')
    compressed = base64.b64decode(envelope['data_base64'], validate=True)
    need(len(compressed) == envelope['compressed_bytes'], 'compressed export size differs')
    decoder = zlib.decompressobj()
    decoded = decoder.decompress(compressed, 128 * 1024 * 1024)
    need(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail,
         'incomplete, oversized, or concatenated compressed export')
    need(fingerprint(decoded) == {k: envelope[k] for k in ('bytes', 'sha256')}, 'export payload SHA/size differs')
    export = document(decoded)
    groups = export['groups']
    need(export['schema'] == spec['export_schema'] and export['read_only'] is True and
         set(groups) == {name + '-' + role for role in ('operation', 'owner', 'readonly', 'stage')},
         'wrong or incomplete original exported groups')
    base = REMOTE_ROOT + '/' + spec['commit']
    roots = {
        name + '-operation': base + '/' + spec['operation'],
        name + '-owner': base + '/' + spec['module'],
        name + '-readonly': spec['readonly_root'] + '/' + spec['commit'] + '/attempt-00000',
        name + '-stage': base + '/published-entrypoints',
    }
    root = Path(raw_root)
    need(root.is_absolute() and root.is_dir() and root.resolve() == root, 'missing original downloaded raw root')
    payload, remote, index = {}, {}, []
    for group in sorted(groups):
        entries = groups[group]
        need(isinstance(entries, dict) and entries, 'empty original export group: ' + group)
        for rel, pin in sorted(entries.items()):
            relative(rel)
            need(set(pin) == {'remote_path', 'bytes', 'sha256', 'base64'}, 'unexpected original export file row')
            need(pin['remote_path'] == roots[group] + '/' + rel, 'original remote path differs')
            data = base64.b64decode(pin['base64'], validate=True)
            data.decode('utf-8')
            need(len(data) < 8 * 1024 * 1024 and fingerprint(data) == {k: pin[k] for k in ('bytes', 'sha256')},
                 'raw export content differs: ' + rel)
            local = root / group / rel
            need(regular(local) == data, 'downloaded original raw file differs: ' + str(local))
            key = group + '/' + rel
            need(key not in payload and pin['remote_path'] not in remote, 'duplicate original raw path')
            payload[key] = data
            remote[pin['remote_path']] = data
            index.append({'group': group, 'relative': rel, 'remote_path': pin['remote_path'],
                          'local': str(local), **fingerprint(data)})
    need(envelope['files'] == len(index), 'original export file count differs')
    return envelope, payload, remote, index


def original_command(command, remote, allowed, exact_build=False):
    """Check retained command/log transport completeness, not execute/revalidate it."""
    need(type(command['exit_code']) is int and command['exit_code'] == 0, 'original command did not finish successfully')
    if 'actual_built_modules' in command:
        built = set(command['actual_built_modules'])
        need(not command['actual_failed_modules'] and built <= allowed and
             (not exact_build or built == allowed), 'original build scope differs')
    log = command['log']
    need(log in remote, 'original command log not exported: ' + log)
    need(hashlib.sha256(remote[log]).hexdigest() == command['log_sha256'], 'original log SHA differs')
    if 'log_bytes' in command:
        need(len(remote[log]) == command['log_bytes'], 'original log bytes differ')


def verify_owner(name, inputs, support):
    spec = OWNERS[name]
    need(isinstance(inputs, dict) and set(inputs) == {
        'formal_provider', 'formal_stdout', 'readonly_provider', 'export_stdout', 'raw_root'},
        'UNBOUND or incomplete owner inputs: ' + name)
    originals = {key: pinned(inputs[key]) for key in ('formal_provider', 'formal_stdout', 'readonly_provider', 'export_stdout')}
    formal = successful_provider(originals['formal_provider'], spec['formal_task'], support[spec['stage_script']])
    readonly = successful_provider(originals['readonly_provider'], spec['readonly_task'], support[spec['export_script']])
    need(formal['task_id'] != readonly['task_id'] and readonly['started_at'] >= formal['finished_at'],
         'readonly task is not independent and later than actual formal completion')
    need(formal['output_bytes'] == len(originals['formal_stdout']) and
         readonly['output_bytes'] == len(originals['export_stdout']), 'provider stdout not complete byte-for-byte')
    envelope, payload, remote, raw_index = load_export(originals['export_stdout'], spec, name, inputs['raw_root'])
    base = REMOTE_ROOT + '/' + spec['commit']
    op = base + '/' + spec['operation']
    owner_root = base + '/' + spec['module']
    ro = spec['readonly_root'] + '/' + spec['commit'] + '/attempt-00000'
    def get(path):
        need(path in remote, 'required original raw evidence missing: ' + path)
        return remote[path]
    def read(path):
        return document(get(path))
    def bind(pin):
        data = get(pin['path'])
        need(fingerprint(data) == {k: pin[k] for k in ('bytes', 'sha256')}, 'original receipt binding differs')
        return document(data)

    receipt = read(ro + '/READONLY_RESULT.json')
    ro_command = read(ro + '/READONLY_COMMAND.json')
    ro_stderr = get(ro + '/readonly.stderr.log')
    need(receipt['status'] == 'REVALIDATED', 'FRESH or partial state is not original acceptance')
    identity = receipt['identity']
    need(identity['commit'] == spec['commit'] and identity['module'] == spec['module'] and
         identity['adapter_sha256'] == spec['adapter']['sha256'] and
         identity[spec['source_identity_key']] == spec['source']['sha256'] and
         identity['whole_P1_5_complete'] is False, 'readonly source/adapter identity differs')
    expected_ro = ['python3', '-B', base + '/published-entrypoints/' + spec['adapter_name'],
                   '--source-commit', spec['commit'], '--check']
    need(ro_command['argv'] == expected_ro and ro_command['cwd'] == '/workspace' and
         ro_command['exit_code'] == 0 and ro_command['normal_or_kernel_commands_executed'] == 0 and
         ro_command['stdout_sha256'] == fingerprint(get(ro + '/READONLY_RESULT.json'))['sha256'] and
         ro_command['stderr_sha256'] == fingerprint(ro_stderr)['sha256'], 'independent original --check binding differs')
    need(not ro_stderr.strip(), 'independent readonly reported stderr; inspect it before publication')
    # The same-task final check is preserved but cannot replace the later check above.
    formal_lines = originals['formal_stdout'].decode().splitlines()
    need(formal_lines and document(formal_lines[-1]) == receipt, 'formal task final original check differs from independent readonly')
    stage_line = document(formal_lines[0])
    stage_path = base + '/published-entrypoints/' + spec['stage_receipt']
    stage_raw = get(stage_path)
    stage = document(stage_raw)
    need(stage_line['stage_receipt'] == stage_path and stage_line['stage_receipt_binding'] == fingerprint(stage_raw),
         'formal stdout stage binding differs')
    need(stage['schema'] == spec['stage_schema'] and stage['source_commit'] == spec['commit'] and
         stage['adapter'] == spec['adapter'] and stage['adapter_path'] == expected_ro[2] and
         stage['original_git_state_unchanged'] is True and stage['git_before'] == stage['git_after'] and
         stage['normal_or_kernel_commands_executed'] == 0 and stage['new_owner_accepted'] is False and
         stage['whole_P1_5_complete'] is False, 'original staging receipt differs')

    passed = read(op + '/PASS.json')
    worker = read(op + '/WORKER_PASS.json')
    install = read(op + '/INSTALL.json')
    need(passed['identity'] == identity == worker['identity'] == install['identity'], 'operation identities differ')
    need(fingerprint(get(op + '/executed.py')) == spec['adapter'] and
         fingerprint(get(op + '/original-published.lean')) == spec['original'], 'executed adapter or original source differs')
    need(type(install['original_present']) is bool, 'missing original install state')
    backup = op + '/original-installed.lean'
    need((fingerprint(get(backup)) == spec['original']) if install['original_present'] else backup not in remote,
         'installed original source backup differs')
    need(passed['worker'] == fingerprint(get(op + '/WORKER_PASS.json')) and
         passed['preserved'] == fingerprint(get(op + '/PRESERVED_BEFORE.json')) ==
         fingerprint(get(op + '/PRESERVED_AFTER.json')) and
         read(op + '/GIT_BEFORE.json') == read(op + '/GIT_AFTER.json'), 'operation before/after export is incomplete')
    outer = read(op + '/' + spec['outer_command'] + '-command.json')
    need(outer == passed['command'], 'outer operation command receipt differs')
    original_command(outer, remote, {spec['module']})
    lane = read(op + '/LANE.json')
    worker_argv = ['python3', '-B', op + '/executed.py', '--source-commit', spec['commit'], '--worker']
    need(lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 0 and
         lane['argv'] == worker_argv and lane['state_sha256'] == RUNTIME_SHA and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True, 'outer formal lane did not complete')
    direct = read(op + '/' + spec['module'] + '/direct-import-stock-readiness-command.json')
    need(direct == worker['native_stock'], 'original no-build readiness receipt differs')
    original_command(direct, remote, set())

    owned = worker['owner']
    binding = owned['binding']
    need(binding['module'] == spec['module'] and len(binding['audits']) == 1, 'owner binding is partial or ambiguous')
    normal_path = owner_root + '/normal/' + spec['module'] + '/NORMAL_PASS.json'
    need(binding['normal_receipt']['path'] == normal_path, 'normal receipt ownership differs')
    normal = bind(binding['normal_receipt'])
    need(normal['status'] == 'NORMAL_PASS_AUDIT_PENDING' and normal['source_commit'] == spec['commit'] and
         normal['module'] == spec['module'], 'missing original successful normal receipt')
    normal_command = normal['normal_command']
    normal_command_raw = get(normal_command['command_receipt'])
    need(fingerprint(normal_command_raw)['sha256'] == normal_command['command_sha256'], 'normal command pin differs')
    original_command(document(normal_command_raw), remote, {spec['module']}, exact_build=True)
    normal_attempt = normal_command['command_receipt'].rsplit('/', 1)[0]
    for filename in ('CONTEXT_BEFORE.json', 'normal-started.json', 'directdeps-command.json',
                     'directdeps-started.json', 'directdeps.log', 'target-ready-command.json',
                     'target-ready-started.json', 'target-ready.log'):
        get(normal_attempt + '/' + filename)
    audit = binding['audits'][0]
    plan = bind(audit['plan'])
    result = bind(audit['result'])
    audit_root = audit['plan']['path'].rsplit('/', 1)[0]
    need(audit_root.startswith(owner_root + '/audits/') and
         audit['result']['path'] == audit_root + '/lane-0/VALIDATION_RESULTS.json', 'audit ownership differs')
    lane_root = audit_root + '/lane-0'
    for filename in ('BEFORE_KERNEL.json', 'MODULES.json', 'PROJECT_SOURCE_BINDING.json',
                     'REUSED_NORMAL_EVIDENCE.json', 'PublicAudit.lean'):
        get(lane_root + '/' + filename)
    for filename in ('PLAN_BINDING.json', 'TARGETS.json'):
        get(audit_root + '/' + filename)
    get(owner_root + '/plans/' + audit_root.rsplit('/', 1)[1] + '.json')
    records = read(lane_root + '/OWNED_EXPORTS.json')
    need(isinstance(records, list) and records and all(type(row['is_private']) is bool for row in records),
         'original full-owned export records missing')
    observed = {'owned': len(records), 'public': sum(not row['is_private'] for row in records),
                'axioms': sorted({axiom for row in records for axiom in row['axioms']})}
    need(set(observed['axioms']) <= STANDARD_AXIOMS and
         observed == {k: owned[k] for k in ('owned', 'public', 'axioms')} == receipt['owner'] == envelope['owner'],
         'original ownership or axioms disagree across real receipts')
    need(result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS' and
         result['modules'] == {spec['module']: spec['source']['sha256']} and result['total_owned_exports'] == observed['owned'] and
         result['total_public_exports'] == observed['public'] and
         all(result[key] is True for key in ('full_owned_including_private_generated', 'only_standard_axioms',
             'pp_all_true_no_elisions', 'source_plus_five_outputs_unchanged_across_kernel_and_audit',
             'successful_normal_not_repeated')) and result['whole_P1_complete'] is False,
         'original audit completion flags differ')
    need(result['plan_sha256'] == fingerprint(get(audit['plan']['path']))['sha256'] and
         set(plan['modules']) == {spec['module']}, 'original audit plan differs')
    source_path = spec['module'].replace('.', '/') + '.lean'
    need(binding['source_plus_five_outputs'][source_path] == spec['source'] ==
         normal['source_plus_five_outputs'][source_path] == result['source_plus_five_outputs'][spec['module']][source_path],
         'accepted source bytes differ from original published candidate')
    # Original audit's own relative log names are preserved and checked locally.
    commands = list(result['kernel_commands'].values()) + [result[key] for key in
        ('audit_command', 'stock_readiness_before', 'stock_readiness_after')]
    for command in commands:
        exported = dict(command)
        exported['log'] = lane_root + '/' + relative(command['log'])
        original_command(exported, remote, set())
        get(exported['log'][:-4] + '-command.json')

    summary = {
        'module': spec['module'], 'source_acceptance_commit': spec['commit'], 'source': spec['source'],
        'adapter': spec['adapter'], 'formal_task': formal['task_id'], 'independent_readonly_task': readonly['task_id'],
        'original_readonly_status': receipt['status'], 'owner': observed,
        'original_acceptance_binding': binding,
        'readonly_receipt': {'remote_path': ro + '/READONLY_RESULT.json', **fingerprint(get(ro + '/READONLY_RESULT.json'))},
        'readonly_command': {'remote_path': ro + '/READONLY_COMMAND.json', **fingerprint(get(ro + '/READONLY_COMMAND.json'))},
        'formal_pass': {'remote_path': op + '/PASS.json', **fingerprint(get(op + '/PASS.json'))},
        'export_payload': {k: envelope[k] for k in ('bytes', 'sha256', 'files')},
        'source_package_with_original_failed_probes': {'commit': spec['commit'], 'path': spec['source_packet']},
        'full_owned_and_private_generated_records_preserved': True,
        'owned_counts_derived_from_original_exports': True,
        'new_checker_or_Lean_commands_executed_by_assembler': 0,
        'whole_P1_5_complete': False,
    }
    return summary, payload, originals, raw_index


def assemble(bindings_path, output):
    bindings_raw = regular(bindings_path)
    inputs = document(bindings_raw)
    need(isinstance(inputs, dict) and inputs.get('schema') == 'p15_dual_owner_publication_inputs_v1' and
         inputs.get('parent_source_commit') == PARENT and isinstance(inputs.get('owners'), dict) and
         set(inputs['owners']) == set(OWNERS) and all(isinstance(v, dict) for v in inputs['owners'].values()),
         'UNBOUND: both real owner exports and provider task pins are required before assembly')
    support_raw, files = load_support()
    summaries, manifests = {}, {}
    # Complete validation of BOTH owners precedes all publication writes.
    for name in OWNERS:
        summary, payload, originals, manifest = verify_owner(name, inputs['owners'][name], files)
        summaries[name], manifests[name] = summary, manifest
        for rel, data in payload.items():
            files['raw/' + rel] = data
        for key, data in originals.items():
            extension = '.log' if key == 'formal_stdout' else '.json'
            files['transport/' + name + '/' + key + extension] = data
        files['owners/' + name + '.json'] = encoded(summary)
    final = {
        'schema': 'p15_partition_group_log_acceptance_publication_v1',
        'status': 'PASS_COMPLETE_ORIGINAL_EVIDENCE_ASSEMBLED',
        'packet': PACKET, 'parent_source_commit': PARENT,
        'acceptance_authority': 'Original frozen adapters, original g.run_owner audit, and actual later independent original --check receipts.',
        'publication_assembler_is_not_a_replacement_acceptance_validator': True,
        'original_registry': {'registered': 21, 'accepted': 18, 'unchanged': True},
        'new_owners_separate_from_original_registry': summaries,
        'source_only_continuations': {
            'ImbalancedChen.Part3ShiftedTauFiniteInterval': {
                'sha256': 'd006abee2c8dd632d9fd9712b29030dbff0a70f6c95ade6ffec92955a37444c2',
                'new_formal_credit': 0, 'status': 'SOURCE_ONLY_EXACT_REPAIR_RESTORED'},
            'ImbalancedChen.P1OriginalHistoricalFirstDisagreement': {
                'sha256': 'edb45d7c44440fdb68937fc0931c95c7a7ab0532ec26b1f20002b8669c8700a2',
                'new_formal_credit': 0, 'status': 'SOURCE_ONLY_STATIC_REVIEW'},
        },
        'next_policy': {'template': 'next-policy/probe_policy_template.py', 'binding': None,
                        'status': 'UNBOUND_PREPARATION_ONLY', 'new_formal_credit': 0},
        'old_owners_recompiled_by_assembler': False,
        'remote_commands': 0, 'git_commands': 0, 'Lean_or_kernel_commands': 0,
        'canonical_source_paths_changed': [],
        'whole_P1_5_status': 'OPEN', 'whole_P1_5_complete': False,
    }
    files['ACCEPTANCE_SUMMARY.json'] = encoded(final)
    files['RAW_EXPORT_MANIFEST.json'] = encoded(manifests)
    files['INPUT_BINDINGS.json'] = bindings_raw
    files['SUPPORT_BINDINGS.json'] = support_raw
    files['assemble_acceptance.py'] = regular(Path(__file__).resolve())
    files['ASSEMBLER_README.md'] = regular(HERE / 'README.md')
    files['REQUIRED_EVIDENCE.json'] = encoded(requirements())
    rows = ['# Partition and GroupLog original acceptance evidence', '',
            'Both owners have complete original formal evidence and a later independent original `--check` receipt.',
            'This packet preserves those receipts. The local assembler did not execute Lean, a kernel checker, Git, or remote tasks.', '',
            '| Additional owner | Original source acceptance commit | Owned | Public | Independent readonly task |',
            '| --- | --- | ---: | ---: | --- |']
    for summary in summaries.values():
        rows.append('| ' + ' | '.join([summary['module'], summary['source_acceptance_commit'],
                    str(summary['owner']['owned']), str(summary['owner']['public']), summary['independent_readonly_task']]) + ' |')
    rows += ['', 'Counts come from the original full-owned exports, including private and generated declarations.',
             'Original raw files are under `raw/`; the operation/owner/readonly/stage remote paths and every byte/SHA256 pin are in `RAW_EXPORT_MANIFEST.json`.',
             'Transport scripts and provider metadata are under `transport/`. Source publication and binding reviews are under `reviews/` and `metadata/`.', '',
             'The fixed original registry remains **18 accepted of 21 registered**. These two new owners are listed separately.',
             'ShiftedTau repair `d006abee…` and the medium first-disagreement bridge `edb45d7c…` remain source-only.',
             'The next PolicyComparison template remains UNBOUND preparation. It grants no probe or formal acceptance.',
             '**The complete P1.5 task remains OPEN.**', '',
             'Failed probe originals remain in each immutable source package referenced by `ACCEPTANCE_SUMMARY.json`; they are not duplicated here.',
             'The superseded Partition resource-unavailable provider event is retained separately; it never started and is not a failed normal attempt.', '']
    files['README.md'] = '\n'.join(rows).encode()
    need(output.is_absolute() and output.parent == HERE and output.resolve() == output and not output.exists(),
         'output must be a fresh direct child of this assembler directory')
    need(not (HERE / 'FILE_INDEX.json').exists(), 'prior publication index exists; preserve it instead of overwriting')
    output.mkdir()
    index = []
    # Final PASS summary is the last packet file written; an I/O failure while
    # copying raw evidence must not leave an apparently finished summary.
    for rel, data in sorted(files.items(), key=lambda item: (item[0] == 'ACCEPTANCE_SUMMARY.json', item[0])):
        relative(rel)
        dest = output / PACKET / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        with dest.open('xb') as stream:
            stream.write(data)
        need(regular(dest) == data, 'written publication bytes differ')
        index.append({'local': str(dest), 'path': PACKET + '/' + rel, **fingerprint(data)})
    with (HERE / 'FILE_INDEX.json').open('xb') as stream:
        stream.write(encoded(index))
    print(json.dumps({'status': final['status'], 'files': len(index), 'bytes': sum(row['bytes'] for row in index),
                      'file_index': str(HERE / 'FILE_INDEX.json'), 'whole_P1_5_complete': False}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--requirements', action='store_true')
    group.add_argument('--bindings', type=Path)
    parser.add_argument('--output-dir', type=Path, default=HERE / 'publication')
    args = parser.parse_args()
    if args.requirements:
        print(encoded(requirements()).decode(), end='')
        return 0
    assemble(args.bindings, args.output_dir)
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print(json.dumps({'status': 'NOT_READY_NO_FINAL_ACCEPTANCE_SUMMARY', 'reason': str(error),
                          'whole_P1_5_complete': False}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(2)
