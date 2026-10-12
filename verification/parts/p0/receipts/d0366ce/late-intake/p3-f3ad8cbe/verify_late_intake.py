#!/usr/bin/env python3
"""Offline P0 evidence intake. This program never executes a producer runner or Lean.

Only read-only git show/ls-tree/diff-tree commands are permitted below. All writes
are restricted to this directory. PASS below means evidence-consistency checks,
never a Lean proof gate. Static inventory fields describe the producer's recorded
filesystem, not this consumer's environment and not an imported Lean environment.
"""
from __future__ import annotations

import base64
from collections import Counter, defaultdict
import datetime as dt
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2] / 'goldbach-formalization'
SOURCE = 'f3ad8cbe43c61c903857c7411626ee8c56f4f2f9'
PARENT = 'f37f341412eb239f7e7e8937921ee8d01c9c2922'
INTEGRATION = 'd0366ce64272e81faf6166a8a90050f56b328d38'
PREVIOUS = '28fd630ef7cc38eba86beb6c0ba123336b5d05f2'
UPSTREAM = '09b97db5764ade1246bfb77206baa1b124760958'
TARGET = 'ImbalancedChen.Part3PrimeAPDistribution'
SOURCE_PATH = TARGET.replace('.', '/') + '.lean'
SOURCE_SHA256 = '55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc'
HANDOFF_PATH = 'verification/parts/p3/prime-ap-distribution'
HANDOFF = HERE / 'fixed-source' / HANDOFF_PATH
LEDGER_PATH = 'verification/parts/p0/round4/ledger/MODULE_LEDGER_CANDIDATE.json'
CHECKS: list[dict] = []


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def write_json(name: str, value) -> None:
    (HERE / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def check(name: str, condition: bool, details=None) -> None:
    CHECKS.append({'check': name, 'status': 'PASS' if condition else 'FAIL',
                   'details': details})
    if not condition:
        write_json('CHECKS.json', {'scope': 'OFFLINE_EVIDENCE_CONSISTENCY_ONLY',
                   'status': 'CONSUMER_CHECK_FAILED_NOT_LEAN_DIAGNOSTIC',
                   'checks': CHECKS})
        raise AssertionError(name)


@lru_cache(maxsize=None)
def git(*args: str) -> bytes:
    if not args or args[0] not in {'show', 'ls-tree', 'diff-tree'}:
        raise ValueError('This intake permits only read-only git commands')
    return subprocess.check_output(['git', *args], cwd=REPO)


def fixed_file(commit: str, path: str) -> bytes:
    return git('show', f'{commit}:{path}')


def fixed_tree(commit: str) -> dict[str, dict]:
    rows = {}
    for row in git('ls-tree', '-r', '-t', '-z', commit).split(b'\0'):
        if not row:
            continue
        meta, name = row.split(b'\t', 1)
        mode, kind, object_sha = meta.decode().split()
        rows[name.decode()] = {'mode': mode, 'type': kind, 'sha': object_sha}
    return rows


def ref_file(path: Path) -> dict:
    data = path.read_bytes()
    return {'path': str(path.relative_to(HERE)), 'bytes': len(data), 'sha256': sha(data)}


def main() -> None:
    source_tree = fixed_tree(SOURCE)
    parent_tree = fixed_tree(PARENT)
    integration_tree = fixed_tree(INTEGRATION)
    source_tree_sha = git('show', '-s', '--format=%T', SOURCE).decode().strip()
    parent_tree_sha = git('show', '-s', '--format=%T', PARENT).decode().strip()
    check('fixed source parent', git('show', '-s', '--format=%P', SOURCE).decode().strip() == PARENT)
    check('fixed parent tree', parent_tree_sha == 'b6bcbedaf527e8894fd4d05a1df1d68463b47ac5')
    check('fixed integration tree', git('show', '-s', '--format=%T', INTEGRATION).decode().strip()
          == 'e2ab22b96f76c8969386296558c626c62a581700')
    changes = [line.split('\t') for line in git('diff-tree', '--no-commit-id', '--name-status', '-r', PARENT, SOURCE).decode().splitlines()]
    check('19 tracked evidence/documentation changes', len(changes) == 19, changes)
    check('no production Lean change', not any(row[-1].endswith('.lean') for row in changes))
    check('only expected documentation and evidence prefix changed', all(
        row == ['M', 'docs/part3-distribution/README.md'] or
        (row[0] == 'A' and row[1].startswith(HANDOFF_PATH + '/')) for row in changes))
    check('no applicable AGENTS file in fixed P3 tree', not any(PurePosixPath(p).name == 'AGENTS.md' for p in source_tree))

    original_files = read_json(HERE / 'FIXED_FILES.json')
    check('extraction source identity', original_files['source_commit'] == SOURCE)
    for row in original_files['files']:
        data = (HERE / 'fixed-source' / row['path']).read_bytes()
        check('fixed extraction ' + row['path'], data == fixed_file(SOURCE, row['path'])
              and sha(data) == row['sha256'] and len(data) == row['bytes'])

    manifest = read_json(HANDOFF / 'evidence-manifest.json')
    check('17 manifested evidence files', len(manifest['files']) == 17)
    check('manifest is diagnostic at parent source', manifest['base_commit'] == PARENT
          and manifest['status'] == 'DIAGNOSTIC_CHECKPOINT_NOT_PROOF_ACCEPTANCE')
    for row in manifest['files']:
        data = (HANDOFF / row['path']).read_bytes()
        check('original handoff manifest ' + row['path'], len(data) == row['bytes'] and sha(data) == row['sha256'])
    check('manifest covers all other handoff files', set(r['path'] for r in manifest['files']) ==
          {p.name for p in HANDOFF.iterdir() if p.is_file()} - {'evidence-manifest.json'})

    archive_manifest = read_json(HANDOFF / 'inventory-evidence-manifest.json')
    encoded = (HANDOFF / archive_manifest['archive']).read_bytes()
    archive = base64.b64decode(encoded)
    check('encoded archive identity', sha(encoded) == archive_manifest['encoded_sha256'])
    check('decoded archive identity', sha(archive) == archive_manifest['decoded_sha256']
          and len(archive) == archive_manifest['decoded_bytes']
          and archive == (HERE / 'inventory-evidence.tar.xz').read_bytes())
    members = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode='r:xz') as tar:
        for member in tar.getmembers():
            check('safe regular archive member ' + member.name, member.isfile()
                  and not PurePosixPath(member.name).is_absolute()
                  and '..' not in PurePosixPath(member.name).parts
                  and member.name not in members)
            members[member.name] = tar.extractfile(member).read()
    check('six manifested archive members', len(members) == 6 and
          set(members) == {row['path'] for row in archive_manifest['members']})
    for row in archive_manifest['members']:
        data = members[row['path']]
        check('archive member identity ' + row['path'], sha(data) == row['sha256']
              and len(data) == row['bytes'] and data == (HERE / 'archive-evidence' / row['path']).read_bytes())
    check('archive contains no produced object', not any(n.endswith(('.olean', '.ir')) for n in members))

    base_commit = json.loads(members['base-commit.json'])
    base_tree = json.loads(members['base-tree.json'])
    check('archived base commit identity', base_commit['sha'] == PARENT
          and base_commit['tree']['sha'] == parent_tree_sha
          and [x['sha'] for x in base_commit['parents']] == git('show', '-s', '--format=%P', PARENT).decode().split())
    check('archived recursive base tree complete', base_tree['sha'] == parent_tree_sha and base_tree['truncated'] is False)
    archived_tree = {row['path']: {k: row[k] for k in ('mode', 'type', 'sha')} for row in base_tree['tree']}
    check('all archived tree entries agree with fixed git object', archived_tree == parent_tree)
    restoration = json.loads(members['source-restoration.json'])
    restored_rows = restoration['restored'] + restoration['restored_from_github_blob']
    parent_blobs = {path: row for path, row in parent_tree.items() if row['type'] == 'blob'}
    check('348 restored starting blobs exact set', len(restored_rows) == 348
          and {row['path'] for row in restored_rows} == set(parent_blobs))
    for row in restoration['restored']:
        data = fixed_file(PARENT, row['path'])
        check('restored fixed parent source ' + row['path'], blob_sha(data) == row['blob']
              == parent_blobs[row['path']]['sha'] and sha(data) == row['sha256'])
    for row in restoration['restored_from_github_blob']:
        data = fixed_file(PARENT, row['path'])
        check('restored fixed parent API blob ' + row['path'], blob_sha(data) == row['sha']
              == parent_blobs[row['path']]['sha'] and len(data) == row['size'])
    unchanged = [p for p, row in parent_blobs.items() if source_tree.get(p) == row]
    check('347 starting blobs unchanged in late handoff', len(unchanged) == 347)
    guard = read_json(HANDOFF / 'source-and-scope-guard.json')
    for path, expected in guard['frozen_files_sha256'].items():
        check('preserved P3 gate/pin source ' + path, sha(fixed_file(PARENT, path)) == expected
              and fixed_file(PARENT, path) == fixed_file(SOURCE, path))

    target_source = fixed_file(SOURCE, SOURCE_PATH)
    check('target fixed source hash and blob', sha(target_source) == SOURCE_SHA256
          and blob_sha(target_source) == '2d761133b313302ab3a89ae906eb6944037a093d')
    check('archive and parent target source identity', members['Part3PrimeAPDistribution.lean'] ==
          target_source == fixed_file(PARENT, SOURCE_PATH))
    check('target absent from d036 production tree', SOURCE_PATH not in integration_tree)
    check('d036 archived candidate target matches', fixed_file(INTEGRATION,
          'verification/parts/p0/round4/ledger/snapshot-sources/' + SOURCE_PATH) == target_source)

    inventory = json.loads(members['source-import-inventory.json'])
    rows = inventory['inventory']
    by_module = {row['module']: row for row in rows}
    check('6472 unique static inventory modules', len(rows) == len(by_module) == inventory['total_modules_including_target'] == 6472)
    check('inventory target source identity', inventory['target'] == TARGET
          and inventory['target_source_sha256'] == SOURCE_SHA256
          and by_module[TARGET]['source_sha256'] == SOURCE_SHA256)
    group_counts = defaultdict(lambda: {'modules': 0, 'missing_objects': 0, 'missing_sources': 0})
    for row in rows:
        group = group_counts[row['root']]
        group['modules'] += 1
        group['missing_objects'] += not row['object_exists']
        group['missing_sources'] += not row['source_exists']
    check('static group counts independently recomputed', dict(group_counts) == inventory['groups'])
    check('all static direct graph references inventoried', all(dep in by_module for row in rows for dep in row['imports']))
    reached = set()
    todo = [TARGET]
    while todo:
        current = todo.pop()
        if current in reached:
            continue
        reached.add(current)
        todo.extend(by_module[current]['imports'])
    check('all 6472 listed modules reachable in archived source graph', reached == set(by_module))
    missing = [row['module'] for row in rows if not row['object_exists'] and row['module'] != TARGET]
    check('185 missing import objects excludes target', missing == inventory['missing_import_modules']
          and len(missing) == inventory['missing_import_objects_count'] == 185)
    check('186 missing including unproduced target', sum(not row['object_exists'] for row in rows) == 186
          and by_module[TARGET]['object_exists'] is False)
    check('no missing source recorded by producer inventory', not inventory['source_missing']
          and all(row['source_exists'] for row in rows))
    missing_summary = read_json(HANDOFF / 'missing-imports.json')
    for key in ('status', 'recorded_utc', 'target', 'target_source_sha256', 'groups',
                'total_modules_including_target', 'missing_import_objects_count',
                'source_missing', 'direct_imports', 'missing_import_modules', 'first_missing_frontier'):
        check('original missing-import summary ' + key, missing_summary[key] == inventory[key])
    source_imports = re.findall(r'^import\s+(\S+)', target_source.decode(), re.M)
    check('two actual target imports match full archived rows', source_imports == by_module[TARGET]['imports']
          == [row['module'] for row in inventory['direct_imports']]
          and inventory['direct_imports'] == [by_module[name] for name in source_imports])
    check('two direct objects absent in producer snapshot', all(not row['object_exists'] for row in inventory['direct_imports']))

    branch_match = read_json(HANDOFF / 'branch-source-match.json')
    check('25 project rows in branch matching inventory', len(branch_match['modules']) == 25)
    project_bindings = []
    for row in branch_match['modules']:
        name = row['module']
        path = name.replace('.', '/') + '.lean'
        data = fixed_file(PARENT, path)
        check('project source binding ' + name, sha(data) == row['branch_source_sha256']
              == row['inventory_source_sha256'] == by_module[name]['source_sha256']
              and data == fixed_file(SOURCE, path) and row['matches'] is True)
        d036_path = path if name != TARGET else 'verification/parts/p0/round4/ledger/snapshot-sources/' + path
        check('d036 same project source ' + name, data == fixed_file(INTEGRATION, d036_path))
        project_bindings.append({'module': name, 'source_sha256': sha(data), 'd036_path': d036_path,
                                 'd036_identity': 'PRODUCTION' if name != TARGET else 'ARCHIVED_CANDIDATE_ONLY'})

    pins = read_json(HANDOFF / 'fixed-source-pins.json')
    lake_manifest = json.loads(fixed_file(SOURCE, 'lake-manifest.json'))
    packages = {row['name']: row for row in lake_manifest['packages']}
    check('11 exact dependency pin records', len(pins['dependencies']) == 11
          and {r['name'] for r in pins['dependencies']} == set(packages))
    for row in pins['dependencies']:
        name = row['name']
        count = sum(r['root'].endswith('/.lake/packages/' + name) for r in rows)
        check('recorded frozen dependency ' + name, row['expected_rev'] == row['head'] == packages[name]['rev']
              and row['head_matches'] is True and row['returncode'] == 0
              and row['closure_source_count'] == count)
        if count:
            check('recorded nonempty frozen dependency source closure ' + name,
                  row['tree_read_returncode'] == 0 and not row['closure_source_mismatches'])
    upstream_files = read_json(HERE / 'UPSTREAM_FIXED_FILES.json') + read_json(HERE / 'UPSTREAM_SUPPLEMENTAL_FIXED_FILES.json')
    for row in upstream_files:
        data = (HERE / 'upstream-fixed-source' / row['source_file']).read_bytes()
        name = row['source_file'].removesuffix('.lean').replace('/', '.')
        check('independently retrieved fixed supplier source ' + name, row['ref'] == UPSTREAM
              and sha(data) == row['sha256'] == by_module[name]['source_sha256']
              and blob_sha(data) == row['git_blob_sha1'] == row['api_metadata']['sha']
              and len(data) == row['bytes'])

    config = read_json(HANDOFF / 'runtime-config.json')
    attempt = read_json(HANDOFF / 'strict-compile-receipt.json')
    receipt = read_json(HANDOFF / 'receipt.json')
    raw_log = (HANDOFF / 'strict-compile.log').read_bytes()
    driver = members['frontend-driver/lakefile.lean']
    check('attempt source/config/runner/log bindings', attempt['source_sha256_before'] == attempt['source_sha256_after']
          == config['source_sha256'] == SOURCE_SHA256
          and attempt['config_sha256'] == sha((HANDOFF / 'runtime-config.json').read_bytes())
          and attempt['runner_sha256'] == sha((HANDOFF / 'diagnose_imports.py').read_bytes())
          and attempt['log_sha256'] == sha(raw_log))
    check('producer recorded runtime identities unchanged', attempt['tool_and_driver_sha256_after'] == config['tool_and_driver_sha256']
          and attempt['tools_and_driver_unchanged'] is True)
    check('archived driver matches producer record', config['tool_and_driver_sha256'][config['driver'] + '/lakefile.lean'] == sha(driver))
    check('actual driver source requests strict trust zero', b'(trustLevel := 0)' in driver
          and b'setBool `warningAsError (strictName == "strict")' in driver)
    expected_command = [config['toolroot'] + '/bin/lake', '-d', config['driver'], '-f', 'lakefile.lean',
                        'script', 'run', 'compileOne', config['source'], TARGET, config['output_object'], 'strict']
    check('actual diagnostic command and cwd bound to config', attempt['command'] == expected_command
          and attempt['cwd'] == config['repo'] and attempt['environment'] == config['environment'])
    check('actual bounded frontend failed after starting', attempt['returncode'] == 1
          and attempt['timed_out'] is False and attempt['elapsed_seconds'] == 3.326
          and attempt['frontend_started'] is True and attempt['frontend_success_marker'] is False
          and attempt['trustLevel_requested'] == 0 and attempt['warningAsError_requested'] is True)
    check('target objects absent before and after', attempt['target_parts_before'] == attempt['target_parts_after'] == {})
    check('direct import objects absent before and after', attempt['direct_import_parts_before'] ==
          attempt['direct_import_parts_after'] == {name: {} for name in source_imports})
    check('target kernel replay and axiom audit not executed', attempt['kernel_replay'] ==
          attempt['transitive_axiom_audit'] == {'executed': False, 'accepted': False}
          and attempt['strict_compile_accepted'] is False)
    check('no follow-on build recorded', attempt['prerequisite_builds_started'] == 0
          and attempt['full_repository_build_started'] is False and attempt['metadata_adapter'] is False)
    log_lines = raw_log.decode().splitlines()
    diagnostics = [(i + 1, line) for i, line in enumerate(log_lines) if ': error:' in line]
    check('one real Lean import diagnostic in original raw log', len(diagnostics) == 1
          and diagnostics[0][0] == 5 and config['source'] + ':1:0: error: object file ' in diagnostics[0][1]
          and inventory['direct_imports'][0]['object'] in diagnostics[0][1]
          and diagnostics[0][1].endswith('of module ImbalancedChen.ChenQuotientSieveRemainders does not exist'))
    check('runtime githash marker recorded', any('FRONTEND_START module=' + TARGET +
          ' trustLevel=0 strict=strict Lean.githash=62eed1db4d67327ec8120be05f1a1b0847d74561' == line for line in log_lines))
    check('main receipt admits no new proof or compiler types', receipt['base_commit'] == PARENT
          and receipt['verified_new_theorem_count'] == 0 and receipt['compiler_confirmed_types'] == []
          and receipt['owned_declaration_count_from_lean'] is None
          and receipt['actual_import_inventory_from_lean'] is None
          and receipt['target_object_sha256'] is None and receipt['target_object_produced'] is False)
    first_diagnostic = {'scope': 'ACTUAL_PRODUCER_LEAN_FRONTEND_IMPORT_FAILURE',
        'source_handoff_sha': SOURCE, 'attempt_base_sha': PARENT,
        'raw_log': ref_file(HANDOFF / 'strict-compile.log'), 'raw_log_line': diagnostics[0][0],
        'diagnostic': diagnostics[0][1], 'target_source_line': 1, 'target_source_column': 0,
        'elapsed_seconds': attempt['elapsed_seconds'], 'returncode': attempt['returncode'],
        'target_declarations_reached': False,
        'raw_marker_order_note': 'Combined buffered stdout/stderr records FRONTEND_FAILED before FRONTEND_START; raw order is preserved, not reinterpreted as execution chronology.'}
    write_json('FIRST_REAL_LEAN_DIAGNOSTIC.json', first_diagnostic)
    (HERE / 'FIRST_REAL_LEAN_DIAGNOSTIC.txt').write_text(diagnostics[0][1] + '\n')

    source_declarations = read_json(HANDOFF / 'source-declarations.json')
    text = target_source.decode()
    declarations = []
    for match in re.finditer(r'^(theorem|def)\s+(\S+)', text, re.M):
        end = text.index(':=', match.start())
        declarations.append({'kind': match.group(1), 'name': 'ImbalancedChen.' + match.group(2),
            'source_line': text[:match.start()].count('\n') + 1,
            'source_header': text[match.start():end].rstrip(), 'compiler_confirmed': False})
    check('all 15 complete source declaration headers exact', declarations == source_declarations['declarations'])
    check('13 source theorems and two source definitions', Counter(d['kind'] for d in declarations) == {'theorem': 13, 'def': 2})
    check('original complete source headers appear verbatim in SOURCE_TYPES', all(
          d['source_header'] in (HANDOFF / 'SOURCE_TYPES.md').read_text() for d in declarations))
    context = ['namespace ImbalancedChen', 'noncomputable section', 'open Filter',
        'open scoped BigOperators', 'open MathlibNt.SieveTheory.BombieriVinogradov',
        'open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)']
    types = {'scope': 'SOURCE_HEADERS_ONLY_NOT_COMPILER_TYPES', 'source_handoff_sha': SOURCE,
        'original_candidate_source_sha': '7d70a2545fd819706e473eb41e4d430ad19119d8',
        'source_file': SOURCE_PATH, 'source_sha256': SOURCE_SHA256,
        'context': context, 'complete_source_header_count': 15,
        'compiler_confirmed_type_count': 0, 'owned_private_generated_inventory': None,
        'declarations': declarations}
    write_json('SOURCE_TYPES_15_SOURCE_ONLY.json', types)
    (HERE / 'SOURCE_TYPES_15_SOURCE_ONLY.md').write_text(
        '# P3 固定候选的 15 个完整源码声明头\n\n'
        '**SOURCE_HEADERS_ONLY_NOT_COMPILER_TYPES。** 13 个 theorem、2 个 def；编译器确认类型 0。'
        '没有私有/自动生成声明审计，因此 15 不是完整所属声明数的上限。\n\n'
        f'交接 `{SOURCE}`；源码 `{SOURCE_PATH}`；SHA256 `{SOURCE_SHA256}`。\n\n'
        '原源码名称解析上下文：\n\n```lean\n' + '\n'.join(context) + '\n```\n\n' +
        '\n\n'.join(f"## {d['name']}\n\n源码第 {d['source_line']} 行，源码提取。\n\n```lean\n{d['source_header']}\n```" for d in declarations) + '\n')

    ledger_data = fixed_file(INTEGRATION, LEDGER_PATH)
    ledger = json.loads(ledger_data)
    p3_rows = [row for row in ledger['modules'] if row['part_owner'] == 'P3']
    check('seven existing P3 ledger modules', len(p3_rows) == 7)
    alignment_rows = []
    for row in p3_rows:
        data = fixed_file(SOURCE, row['repository_path'])
        check('unchanged P3 module at latest handoff ' + row['module'], sha(data) == row['source']['sha256']
              and data == fixed_file(PARENT, row['repository_path']))
        alignment_rows.append({'module': row['module'], 'source_sha256': sha(data),
            'latest_source_handoff': SOURCE, 'd036_latest_handoff_field': row['source']['latest_fixed_handoff'],
            'source_unchanged': True, 'd036_component_evidence_accepted': row['component_evidence_accepted'],
            'd036_validation_status': row['validation_status'],
            'd036_complete_received_production_types': row['declarations']['complete_received_production_types'],
            'new_proof_from_late_update': False})
    target_row = next(row for row in p3_rows if row['module'] == TARGET)
    check('target remains unaccepted candidate in frozen integration', target_row['component_evidence_accepted'] is False
          and target_row['compiled_object_sha256'] is None and target_row['declarations']['complete_received_production_types'] == 0)
    check('late handoff not present in fixed integration evidence', not any(
          path.startswith(HANDOFF_PATH + '/') for path in integration_tree))
    alignment = {'scope': 'LATE_HANDOFF_OVERLAY_ONLY_NO_REPOSITORY_MUTATION',
        'integration_sha': INTEGRATION, 'ledger_path': LEDGER_PATH, 'ledger_sha256': sha(ledger_data),
        'late_handoff_sha': SOURCE, 'late_handoff_parent': PARENT, 'included_in_integration': False,
        'unchanged_existing_counts': ledger['counts'], 'new_accepted_modules': 0,
        'new_compiler_confirmed_types': 0, 'p3_modules': alignment_rows,
        'target_update': {'module': TARGET, 'source_sha256': SOURCE_SHA256,
            'previous_compile_status': target_row['validation']['compile']['status'],
            'new_attempt_status': 'FAILED_MISSING_IMPORT_OBJECTS',
            'new_attempt_is_proof_acceptance': False, 'compile_exit_code': 1, 'compile_elapsed_seconds': 3.326,
            'stock_kernel_replay': 'NOT_EXECUTED_NO_TARGET_OBJECT',
            'all_owned_transitive_axioms': 'NOT_EXECUTED_NO_TARGET_OBJECT',
            'candidate_status_retained': True, 'first_real_diagnostic': 'FIRST_REAL_LEAN_DIAGNOSTIC.json'}}
    write_json('D036_LEDGER_ALIGNMENT.json', alignment)

    old_zip_path = HERE.parents[1] / 'previous-28fd630/core-artifact.zip'
    old_bytes = old_zip_path.read_bytes()
    fixed_old_zip = 'verification/parts/p0/round4/ledger/previous-ci/core-artifact.zip'
    check('old core artifact exact published byte identity', old_bytes == fixed_file(INTEGRATION, fixed_old_zip))
    with zipfile.ZipFile(io.BytesIO(old_bytes)) as old_zip:
        receipt_name = next(n for n in old_zip.namelist() if n.endswith('/receipt.json'))
        old_receipt_data = old_zip.read(receipt_name)
        old = json.loads(old_receipt_data)
        dep = 'ImbalancedChen.ChenQuotientSieveRemainders'
        dep_path = dep.replace('.', '/') + '.lean'
        check('old fixed receipt source identity for missing direct project import', old['source_commit'] == PREVIOUS
              and old['status'] == 'PASS' and old['inputs_before']['source_sha256'][dep_path] ==
              old['inputs_after']['source_sha256'][dep_path] == by_module[dep]['source_sha256'])
        parts = old['inputs_before']['production_olean_parts'][dep]
        check('old direct project object identity stable in prior receipt', parts == old['inputs_after']['production_olean_parts'][dep])
        replay_name = '_temp/lean-verification-logs/leanchecker.log'
        replay_data = old_zip.read(replay_name)
        replay_lines = [line for line in replay_data.decode().splitlines() if dep in line]
        check('prior root replay log actually names direct project module', bool(replay_lines))
        check('old artifact does not transport that direct object binary', not any(n.endswith('/' + dep.replace('.', '/') + '.olean') for n in old_zip.namelist()))
    old_reuse = {'scope': 'REUSED_PREVIOUS_FIXED_CORE_RECORD_NOT_NEW_TARGET_VALIDATION',
        'previous_integration_sha': PREVIOUS, 'artifact_current_fixed_repository_path': fixed_old_zip,
        'artifact_container_commit': INTEGRATION, 'artifact_sha256': sha(old_bytes),
        'original_receipt_member': receipt_name, 'original_receipt_sha256': sha(old_receipt_data),
        'module': dep, 'source_sha256': by_module[dep]['source_sha256'],
        'production_object_parts_recorded': parts, 'replay_log_member': replay_name,
        'replay_log_sha256': sha(replay_data), 'matching_replay_lines': replay_lines,
        'binary_present_in_artifact': False, 'new_target_compilation_inferred': False,
        'limitation': 'This confirms an earlier same-source project prerequisite receipt; it does not make its object available in the P3 producer runtime or supply the missing goldbach BV closure.'}
    write_json('PRIOR_DIRECT_IMPORT_EVIDENCE_REUSE.json', old_reuse)

    write_json('PROJECT_SOURCE_BINDINGS.json', {'source_handoff_sha': SOURCE,
        'parent_sha': PARENT, 'comparison_integration_sha': INTEGRATION, 'bindings': project_bindings})
    receipt_out = {'schema': 'p0.late-p3-diagnostic-intake.v1',
        'status': 'RECEIVED_DIAGNOSTIC_UPDATE_NO_NEW_PROOF',
        'checked_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'source_handoff_sha': SOURCE, 'source_tree': source_tree_sha,
        'parent_sha': PARENT, 'parent_tree': parent_tree_sha,
        'proof_baseline': '1a80c1bcce67886f699d097fc37fd245cd3620bf',
        'manuscript_baseline': 'ba6ec11d800eccc54406490631895e174de85766',
        'integration_sha': INTEGRATION, 'included_in_integration': False,
        'changed_files': [{'status': row[0], 'path': row[1]} for row in changes],
        'production_lean_files_changed': [], 'new_accepted_modules': 0,
        'new_compiler_confirmed_types': 0, 'source_declaration_headers': {'theorems': 13, 'definitions': 2},
        'target_module': TARGET, 'target_source_sha256': SOURCE_SHA256,
        'target_source_git_blob': blob_sha(target_source),
        'attempt': {'kind': 'ACTUAL_PRODUCER_STRICT_FRONTEND_IMPORT_FAILURE',
            'base_sha': PARENT, 'command': expected_command,
            'trust_level_requested': 0, 'strict_warning_as_error_requested': True,
            'returncode': 1, 'elapsed_seconds': 3.326, 'target_object_before': {},
            'target_object_after': {}, 'target_declarations_reached': False,
            'kernel_replay_executed': False, 'all_owned_axiom_audit_executed': False,
            'first_real_lean_diagnostic': first_diagnostic},
        'static_inventory': {'record_kind': 'PRODUCER_RECORDED_STATIC_SOURCE_GRAPH',
            'modules_including_target': 6472, 'missing_import_objects': 185,
            'missing_objects_including_target': 186, 'missing_goldbach_import_objects': 184,
            'missing_project_import_objects': 1, 'actual_imported_lean_environment': False,
            'full_source_object_provenance_established': False, 'groups': dict(group_counts)},
        'source_identity_checks': {'restored_fixed_parent_blobs': 348,
            'unchanged_parent_blobs': 347, 'project_modules_cross_checked': 25,
            'independent_fixed_upstream_files_cross_checked': len(upstream_files),
            'dependency_pin_records_cross_checked': 11,
            'all_upstream_source_blobs_independently_read': False,
            'runtime_binaries_available_or_rehashed_by_consumer': False},
        'evidence_archive': {'encoded': ref_file(HANDOFF / 'inventory-evidence.tar.xz.b64'),
            'decoded': ref_file(HERE / 'inventory-evidence.tar.xz'),
            'member_manifest': ref_file(HANDOFF / 'inventory-evidence-manifest.json'),
            'six_regular_members_verified': True},
        'receiving_parts': ['P0: diagnostic ledger only', 'P3: candidate validation prerequisites',
                            'P4-B and P5: future ordinary-BV candidate interface, not yet accepted proof'],
        'unclosed_validation_inputs': ['Source/toolchain/import-bound goldbach BV prerequisite object closure (184 recorded missing import modules)',
            'Same-source ChenQuotientSieveRemainders object (one recorded missing project import)',
            'Explicit target strict compile, original stock kernel replay, all-owned private/generated transitive-axiom audit and complete compiler types'],
        'unclosed_mathematical_inputs': ['Actual-policy modulus cap, coefficients and source/factorization identities from P1',
            'Full physical high-modulus/medium/two-long distribution and uniform rough/Mobius SW beyond ordinary square-root BV',
            'Same actual rho K density bound; real Chen mean c/hLower and hUpper analytic suppliers'],
        'dependency_rule_preserved': 'P5 waits for P4-A, not for P4-B',
        'consumer_actions': {'lean_lake_elan_or_leanchecker_executed': False,
            'ci_polled_dispatched_or_retried': False, 'producer_scripts_executed': False,
            'runtime_or_environment_built': False, 'repository_mutated': False,
            'git_read_operations_only': ['show', 'ls-tree', 'diff-tree'],
            'offline_hash_and_json_checks_only': True},
        'limitations': ['A passing evidence-consistency check is not a Lean gate.',
            'The new integration d036 core run is owned and monitored by root; this intake contains no new result for that run.',
            'Producer tool binary before/after hashes are recorded and consistent, not independently rehashed here.',
            'The archived frontend driver includes an existing runtime initializer API invocation using unsafe; no production Lean source changed and no proof-bypass conclusion is asserted.']}
    write_json('INTAKE_RECEIPT.json', receipt_out)
    write_json('CHECKS.json', {'schema': 'p0.offline-evidence-checks.v1',
        'status': 'PASS_OFFLINE_EVIDENCE_CONSISTENCY_ONLY',
        'source_handoff_sha': SOURCE, 'script_sha256': sha(Path(__file__).read_bytes()),
        'assertion_count': len(CHECKS), 'lean_proof_gate_executed': False,
        'producer_runtime_provenance_claimed': False, 'checks': CHECKS})
    print(json.dumps({'status': receipt_out['status'], 'offline_checks_passed': len(CHECKS),
        'new_accepted_modules': 0, 'compiler_confirmed_target_types': 0,
        'actual_producer_failure': {'exit_code': 1, 'elapsed_seconds': 3.326}}, ensure_ascii=False))


if __name__ == '__main__':
    main()
