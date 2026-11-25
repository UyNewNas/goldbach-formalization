#!/usr/bin/env python3
"""Offline consistency check of the three fixed P1.4 checkpoints; never rebuild.

Checks the fixed archive, reported cloud commands, complete owned inventory,
cross-receipt source/object fingerprints and current target source bytes. The
archive does not contain compiled objects: this is not a local kernel replay.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tarfile

ARCHIVE_SHA = '61a6c9eb309baea57a2ef5e7fda4d2473131552e432e1f1601f0982eb38c8c9e'
AUDIT_TEMPLATE_SHA = '535d5e697ff5c719dbbd90ff04e358be7071cdc9a0b145cf4d3edf2fff002248'
AUDIT_BODY_SHA = 'dcc7d001d2e82fd9a4ff9fd2d0ad2b1fb8b7223bc1f3e8cf8aa0505644017d92'
AUDIT_RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
GROUPS = {
    'p14_new': ['P1FifthGrid400UnitBoxPartition', 'P1OriginalFifthRawBoxGateSoundness',
                'P1OriginalFifthCorrelatedRawBoxGates', 'P1OriginalFifthCorrelatedDecodedGates'],
    'p15_shared_repairs_reused': ['P1ActualVariableFifthGlobalPositiveLimit',
        'P1OriginalFifthMiddleShellFiniteBudget', 'P1OriginalFifthMovingScaleLimit',
        'P1OriginalVariableFourthActiveMeshCover', 'P1OriginalVariableFourthFullActivePositiveLimit',
        'P1OriginalVariableFourthUntruncatedDomination'],
    'prior_fourth_integral_reused': ['P1OriginalFourthUntruncatedIntegral'],
}
EXPECTED = {'ImbalancedChen.' + m: group for group, modules in GROUPS.items() for m in modules}
CHECKPOINTS = {
    '01': {'sha256': ARCHIVE_SHA, 'bytes': 266688, 'files': 502, 'groups': GROUPS,
           'shared_root': 'p15_shared', 'shared_exit_code': 0, 'shared_failures': [],
           'owned': 312, 'public': 301},
    '02': {'sha256': 'fb92a04371670d9f04b35420c0cfa7ac6afefd039eae1bca2f9ae0e584924ef5',
           'bytes': 196276, 'files': 309,
           'groups': {
               'p14_new': ['P1FifthRawKeyThirdOwnerPersistence',
                   'P1OriginalFifthFiniteTableRefinementConstructor', 'P1OriginalFifthPositiveBufferSchedule'],
               'p15_shared_repairs_reused': ['P1FifthMiddleNormalizedPointwise',
                   'P1OriginalVariableFourthFullActiveIntegral', 'P1OriginalVariableFourthFullSmallSource']},
           'shared_root': 'p15_shared_round02', 'shared_exit_code': 1,
           'shared_failures': ['ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit'],
           'owned': 113, 'public': 112},
    '03': {'sha256': 'b538605b5dfad63279f9a59a2e771afcf0c1cc658b63578115e8dce0c5e09bbe',
     'bytes': 325052,
     'files': 725,
     'groups': {'p14_new': ['P5OriginalCommonRefinedSeedHull'],
                'p15_shared_repairs_reused': ['P1ActualVariableFifthSmallLastGeometry',
                                              'P1ActualVariableFifthTailPointwise',
                                              'P1ActualVariableFifthUniformTail',
                                              'P1ActualVariableFifthUntruncatedDomination',
                                              'P1OriginalFifthMiddleShellMovingLimit',
                                              'P1OriginalFifthMiddleShellRemainderSplit',
                                              'P1OriginalFifthUniformSmallRemainder',
                                              'P1OriginalFifthUntruncatedIntegral',
                                              'P1OriginalFifthZeroCutoffLimit',
                                              'P1OriginalVariableFourthFullSmallRemainder',
                                              'P1OriginalVariableFourthFullSourceAssembly',
                                              'P1OriginalVariableFourthFullSourceMean']},
     'shared_runs': [{'path': 'p15_shared_round03/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceAssembly'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthSmallLastGeometry',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round03/runs/attempt-00001',
                      'accepted': ['ImbalancedChen.P1OriginalFifthMiddleShellRemainderSplit'],
                      'failures': [],
                      'exit_code': 0},
                     {'path': 'p15_shared_round04/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1ActualVariableFifthSmallLastGeometry'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthTailPointwise',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination',
                                   'ImbalancedChen.P1OriginalFifthUniformSmallRemainder',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceMean'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round05/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder',
                                   'ImbalancedChen.P1ActualVariableFifthTailPointwise',
                                   'ImbalancedChen.P1OriginalFifthUniformSmallRemainder'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalVariableFourthFullSourceMean'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round06/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1OriginalVariableFourthFullSourceMean',
                                   'ImbalancedChen.P1ActualVariableFifthUniformTail',
                                   'ImbalancedChen.P1OriginalFifthZeroCutoffLimit',
                                   'ImbalancedChen.P1OriginalFifthUntruncatedIntegral'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean',
                                   'ImbalancedChen.P1ActualVariableFifthUntruncatedDomination'],
                      'exit_code': 1},
                     {'path': 'p15_shared_round07/runs/attempt-00000',
                      'accepted': ['ImbalancedChen.P1ActualVariableFifthUntruncatedDomination'],
                      'failures': ['ImbalancedChen.P1ActualVariableFifthFullMean'],
                      'exit_code': 1}],
     'shared_failures': ['ImbalancedChen.P1ActualVariableFifthFullMean'],
     'excluded_failed_owners': ['ImbalancedChen.P1HistoricalFifthNpyFrame',
                                'ImbalancedChen.P1HistoricalFifthOriginalByteLiteral',
                                'ImbalancedChen.P1ActualVariableFifthFullMean'],
     'owned': 197,
     'public': 176},
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT = re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+'
                   r'(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)', re.M)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(archive, repo, checkpoint='01'):
    config = CHECKPOINTS[checkpoint]
    groups = config['groups']
    expected = {'ImbalancedChen.' + m: group for group, modules in groups.items() for m in modules}
    raw = archive.read_bytes()
    need(len(raw) == config['bytes'] and sha(raw) == config['sha256'], 'checkpoint ' + checkpoint + ' archive differs')
    files = {}
    with tarfile.open(archive, 'r:xz') as tar:
        for member in tar.getmembers():
            path = PurePosixPath(member.name)
            need(not path.is_absolute() and '..' not in path.parts, 'unsafe archive path')
            need(member.isfile() or member.isdir(), 'archive contains a nonregular entry')
            if member.isfile():
                need(member.name not in files, 'duplicate archive file')
                files[member.name] = tar.extractfile(member).read()
    get = lambda path: json.loads(files[str(path)])
    manifest = get('EXPORT_MANIFEST.json')
    need(manifest['schema'] == 'p14_receipt_export_v1' and not manifest['whole_P1_4_complete'], 'export scope')
    need(len(manifest['files']) == config['files'], 'export file count')
    if checkpoint in ('02', '03'):
        predecessor = '01' if checkpoint == '02' else '02'
        need(manifest['checkpoint'] == checkpoint and
             manifest['prior_checkpoint_sha256'] == CHECKPOINTS[predecessor]['sha256'], 'checkpoint predecessor binding')
    originals = {}
    for row in manifest['files']:
        data = files[row['path']]
        need(len(data) == row['bytes'] and sha(data) == row['sha256'], 'export hash: ' + row['path'])
        need(row['original_path'] not in originals, 'duplicate original receipt path')
        originals[row['original_path']] = row['path']
    need(set(files) == {r['path'] for r in manifest['files']} | {'EXPORT_MANIFEST.json'}, 'unlisted archive file')
    git_pairs = [p for p in files if p.endswith('/GIT_BEFORE.json')]
    for path in git_pairs:
        need(get(path) == get(path.replace('/GIT_BEFORE.json', '/GIT_AFTER.json')), 'original Git checkout changed')
    shared_expected = {m for m, g in expected.items() if g == 'p15_shared_repairs_reused'}
    shared_specs = config['shared_runs'] if 'shared_runs' in config else [{
        'path': config['shared_root'] + '/runs/attempt-00000', 'accepted': sorted(shared_expected),
        'failures': config['shared_failures'], 'exit_code': config['shared_exit_code']}]
    shared_by_owner, shared_protected = {}, None
    for spec in shared_specs:
        shared_run = PurePosixPath(spec['path'])
        shared_result = get(shared_run / 'RESULT.json')
        shared_context = get(shared_run / 'CONTEXT_BEFORE.json')
        need(shared_context == get(shared_run / 'CONTEXT_AFTER.json'), 'shared source/runtime context changed')
        need(shared_result['all_selected_owners_accepted'] is (not spec['failures']) and
             set(shared_result['failures']) == set(spec['failures']) and
             shared_result['worker_exit_code'] == spec['exit_code'] and
             not shared_result['whole_P1_complete'], 'shared outer result')
        need(set(shared_result['accepted_owners']) == set(spec['accepted']) and
             set(shared_result['targets']) == set(spec['accepted']) | set(spec['failures']), 'shared outer owner set')
        if shared_protected is None:
            shared_protected = shared_context['protected_roots']
        need(shared_context['protected_roots'] == shared_protected, 'shared protected roots differ')
        for module in spec['accepted']:
            need(module not in shared_by_owner, 'duplicate shared acceptance')
            shared_by_owner[module] = (shared_result, shared_context)
    need(set(shared_by_owner) == shared_expected, 'shared accepted owner union differs')
    deployments = [get(p) for p in files if '/source-materialization/' in p and p.endswith('/RESULT.json')]
    need(all(d['status'] == 'SOURCE_DEPLOYMENT_ONLY_NOT_ACCEPTANCE' and d['acceptance_claimed'] is False
             and 'accepted_owners' not in d for d in deployments), 'source deployment misstates acceptance')

    def location(path, base=''):
        return originals[path] if PurePosixPath(path).is_absolute() else str(PurePosixPath(base) / path)

    def command(record, base, expected_argv=None):
        need(record['exit_code'] == 0 and record['cwd'] == '/workspace/blue-member-build', 'command failed or cwd differs')
        if expected_argv is not None:
            need(record['argv'][4:] == expected_argv, 'command arguments differ')
        need(record['argv'][:3] == ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state'], 'unguarded command')
        log = location(record['log'], base)
        need(sha(files[log]) == record['log_sha256'], 'command log hash: ' + log)
        if 'log_bytes' in record:
            need(len(files[log]) == record['log_bytes'], 'command log size')
        return ANSI.sub('', files[log].decode())

    normals = {}
    for path in files:
        if path.endswith('/NORMAL_PASS.json'):
            item = get(path)
            need(item['module'] not in normals, 'duplicate successful normal receipt')
            normals[item['module']] = (path, item)
    need(set(normals) == set(expected), 'successful normal owner set differs')
    successes = collections.Counter()
    for path in files:
        if path.endswith('/normal-command.json'):
            record = get(path)
            if record['exit_code'] == 0:
                built = BUILT.findall(command(record, ''))
                need(built == record['actual_built_modules'] and len(built) == 1, 'normal rebuilt extra modules')
                successes.update(built)
    need(successes == collections.Counter({m: 1 for m in expected}), 'successful normal was duplicated or omitted')

    reports = []
    seen = set()
    for path in sorted(p for p in files if p.endswith('/VALIDATION_RESULTS.json')):
        v = get(path)
        lane = PurePosixPath(path).parent
        audit_root = lane.parent
        need(v['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS', 'audit status')
        need(len(v['modules']) == 1, 'checkpoint lane scope')
        module, digest = next(iter(v['modules'].items()))
        need(module in expected and module not in seen, 'duplicate or unexpected audited owner')
        seen.add(module)
        need(all(v[k] is True for k in ['full_owned_including_private_generated', 'only_standard_axioms',
            'pp_all_true_no_elisions', 'source_plus_five_outputs_unchanged_across_kernel_and_audit',
            'successful_normal_not_repeated']) and v['whole_P1_complete'] is False, 'audit flags')
        normal_path, normal = normals[module]
        nc = normal['normal_command']
        normal_log = command(nc, '', ['lake', 'build', '+' + module + ':olean'])
        need(BUILT.findall(normal_log) == [module] and nc['actual_built_modules'] == [module], 'normal build markers')
        need(nc['actual_failed_modules'] == [] and nc['project_error_count'] == 0 and nc['project_error_sections'] == [], 'normal errors')
        command_path = location(nc['command_receipt'])
        need(sha(files[command_path]) == nc['command_sha256'], 'normal command receipt hash')
        need(get(command_path) == {k: x for k, x in nc.items() if k not in ['command_receipt', 'command_sha256']}, 'normal receipt contents')
        attempt = PurePosixPath(command_path).parent
        context = normal['dependency_context']
        need(get(attempt / 'CONTEXT_BEFORE.json') == context, 'normal dependency context changed')
        need(normal['source_commit'] == context['source_commit'], 'normal source commit differs')
        deps = get(attempt / 'directdeps-command.json')
        need('--no-build' in deps['argv'] and BUILT.findall(command(deps, str(attempt))) == [], 'direct dependencies were rebuilt')
        ready = get(attempt / 'target-ready-command.json')
        need(ready['exit_code'] == 3 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == [module], 'target was not held as missing before build')
        need('--no-build' in ready['argv'] and sha(files[location(ready['log'], str(attempt))]) == ready['log_sha256'], 'target readiness binding')

        plan = get(audit_root / 'AUDIT_PLAN.json')
        plan_binding = get(audit_root / 'PLAN_BINDING.json')
        need(sha(files[str(audit_root / 'AUDIT_PLAN.json')]) == v['plan_sha256'] == plan_binding['sha256'], 'audit plan hash')
        need(plan_binding['runner_sha256'] == AUDIT_RUNNER_SHA and plan_binding['no_compiler_invoked_by_preparation'], 'audit runner binding')
        need(v['audit_template_sha256'] == plan['audit_template']['sha256'] == AUDIT_TEMPLATE_SHA, 'audit template pin')
        need(get(lane / 'MODULES.json') == get(audit_root / 'TARGETS.json') == [module], 'module inventory scope')
        need(plan['source_review_head'] == normal['source_commit'], 'normal/audit source commits differ')
        sources = v['project_dependency_sources']
        need(sources == get(lane / 'PROJECT_SOURCE_BINDING.json') == context['project_sources'], 'normal/audit source closure differs')
        need(sources == {m: plan['expected_project_sources'][m] for m in plan['modules'][module]['project_closure']}, 'plan source closure differs')
        need(sources[module] == plan['modules'][module]['source_sha256'] == digest, 'target source binding')
        if expected[module] == 'p14_new':
            owner_root = PurePosixPath(normal_path).parents[2]
            binding = get(owner_root / 'BINDING.json')
            outer = get(owner_root / 'runs/attempt-00000/RESULT.json')
            need(binding['source_commit'] == outer['source_commit'] == normal['source_commit'], 'outer source commit differs')
            need(binding['targets'][module] == outer['targets'][module] == digest and
                 module in outer['accepted_owners'] and module in outer['normal_passed'], 'outer accepted target differs')
            need(binding['protected_roots'] == outer['protected_roots'] == shared_protected, 'protected root hashes differ')
            need(sha(files[str(owner_root / 'executed-driver.py')]) == binding['driver_sha256'], 'executed driver hash differs')
            need(sha((repo / binding['manifest_path']).read_bytes()) == binding['manifest_sha256'], 'current stage manifest differs')
            need(all(binding['project_sources'][m] == s for m, s in sources.items()), 'outer source closure differs')
        elif expected[module] == 'p15_shared_repairs_reused':
            owner_shared_result, owner_shared_context = shared_by_owner[module]
            need(normal['source_commit'] == owner_shared_result['source_commit'] and
                 all(owner_shared_context['project_sources'][m] == s for m, s in sources.items()), 'shared outer source binding differs')
        snapshot = v['source_plus_five_outputs'][module]
        need(snapshot == normal['source_plus_five_outputs'] == get(lane / 'BEFORE_KERNEL.json')[module], 'source/object fingerprints changed')
        source_path = module.replace('.', '/') + '.lean'
        current = (repo / source_path).read_bytes()
        need(sha(current) == snapshot[source_path]['sha256'] == digest and len(current) == snapshot[source_path]['bytes'], 'current target source differs: ' + module)
        reused = v['reused_normal_evidence']
        need(reused == get(lane / 'REUSED_NORMAL_EVIDENCE.json') and set(reused) == {module}, 'normal reuse record')
        record = reused[module]
        need(record['source_commit'] == normal['source_commit'] and record['sha256'] == nc['log_sha256'], 'reused normal binding')
        need(record['all_actual_built_modules'] == [module] and record['selected_sources'] == {module: digest}, 'reused normal target')
        for header in record['selected_actual_built_headers']:
            need(header['module'] == module and normal_log.splitlines()[header['line'] - 1] == header['text'], 'actual Built header differs')
        need(len(record['selected_actual_built_headers']) == 1, 'missing actual Built header')

        kernel = v['kernel_commands'][module]
        need(get(lane / (module.split('.')[-1] + '-kernel-command.json')) == kernel, 'kernel command sidecar')
        kernel_log = command(kernel, str(lane), ['lake', 'env', 'leanchecker', '--verbose', module])
        need(kernel_log.strip() == 'replaying ' + module, 'kernel replay target log')
        audit = v['audit_command']
        need(get(lane / 'all-owned-types-axioms-command.json') == audit, 'audit command sidecar')
        text = command(audit, str(lane))
        need(audit['argv'][4:7] == ['lake', 'env', 'lean'], 'full-owned audit command')
        records = [json.loads(s.removeprefix('AUDIT_RECORD ')) for s in text.splitlines() if s.startswith('AUDIT_RECORD ')]
        inventory = [json.loads(s.removeprefix('MEMBER_OWNED_NAMES '))['names'] for s in text.splitlines() if s.startswith('MEMBER_OWNED_NAMES ')]
        counts = [json.loads(s.removeprefix('MEMBER_OWNED_MODULE ')) for s in text.splitlines() if s.startswith('MEMBER_OWNED_MODULE ')]
        totals = [int(s.removeprefix('MEMBER_OWNED_COUNT ')) for s in text.splitlines() if s.startswith('MEMBER_OWNED_COUNT ')]
        names = [r['name'] for r in records]
        need(records == get(lane / 'OWNED_EXPORTS.json'), 'owned export records differ from log')
        need(len(inventory) == 1 and sorted(inventory[0]) == sorted(names) and len(set(names)) == len(names), 'owned inventory incomplete')
        need(counts == [{'count': len(records), 'module': module}] and totals == [len(records)], 'owned module count')
        need(len(records) == v['total_owned_exports'] and sum(not r['is_private'] for r in records) == v['total_public_exports'], 'owned/public count')
        need(all(r['module'] == module and r['kind'] != 'axiom' and set(r['axioms']) <= ALLOWED_AXIOMS and
                 r['type'] and r['type_expression'].startswith('Lean.Expr.') for r in records), 'type or axiom audit')
        need(not any(s in text for s in ['sorryAx', '…', '⋯', '...']), 'type dump has elisions or sorry')
        audit_source = files[str(lane / 'PublicAudit.lean')].decode()
        body = re.sub(r'^import ImbalancedChen\.[^\n]+\n', '', audit_source, flags=re.M)
        body = re.sub(r'let modules := #\[[^\n]*\]', 'let modules := #[__MODULES__]', body, count=1)
        need(sha(body.encode()) == AUDIT_BODY_SHA, 'full environment audit program differs')
        need(audit_source.startswith('import ' + module + '\n') and 'let modules := #[`' + module + ']' in audit_source, 'audit program target')
        for key in ['stock_readiness_before', 'stock_readiness_after']:
            rec = v[key]
            need(get(lane / (key.replace('_', '-') + '-command.json')) == rec, 'readiness command sidecar')
            need(BUILT.findall(command(rec, str(lane), ['lake', '--no-build', 'build', '+' + module + ':olean'])) == [], 'audit repeated a normal build')
        reports.append({'module': module, 'group': expected[module], 'source_commit': normal['source_commit'],
            'current_source_sha256': digest, 'owned_declarations': len(records), 'public_declarations': v['total_public_exports'],
            'private_declarations': len(records) - v['total_public_exports'], 'source_closure_modules': len(sources),
            'normal_seconds': nc['elapsed_seconds'], 'kernel_seconds': kernel['elapsed_seconds'],
            'normal_log_sha256': nc['log_sha256'], 'kernel_log_sha256': kernel['log_sha256'],
            'owned_log_sha256': audit['log_sha256'], 'normal_receipt': normal_path,
            'validation_receipt': path, 'validation_receipt_sha256': sha(files[path]),
            'normal_exit_code': 0, 'kernel_exit_code': 0, 'full_owned_audit_exit_code': 0,
            'normal_built_only_target_once_in_archive': True, 'current_source_matches': True})
    need(seen == set(expected), 'accepted owner set differs')
    totals = {g: {'owners': sum(r['group'] == g for r in reports),
                  'owned_declarations': sum(r['owned_declarations'] for r in reports if r['group'] == g)} for g in groups}
    need(sum(r['owned_declarations'] for r in reports) == config['owned'], 'checkpoint owned total differs')
    need(sum(r['public_declarations'] for r in reports) == config['public'], 'checkpoint public total differs')
    limits = [
        'Cloud command exits are validated as archived receipts; no compiler or kernel was rerun locally.',
        'Source and five output fingerprints agree between normal, before-kernel and final audit receipts; binary objects are not in this export.',
        'Current target source bytes match the receipts; historical Git commit/source associations are cross-checked through archived bindings, not new Git retrieval.']
    if checkpoint == '01':
        limits.extend([
            'The prior FourthUntruncatedIntegral export contains its complete owner receipts, but not its original batch-level outer RESULT.json.',
            'This checkpoint excludes later FiniteTableRefinementConstructor and subsequent stages.'])
    elif checkpoint == '02':
        limits.extend([
            'The shared B2 batch exited 1: only its three individually accepted owners are counted; failed MiddleShellMovingLimit is excluded.',
            'Source-materialization receipts describe deployment, not acceptance, and add no accepted owner.'])
    else:
        limits.extend([
            'Shared rounds 03 through 07 contain failed and held attempts; only the twelve individually accepted source-bound owners are counted.',
            'The bytes-frame-seed stage accepted only P5OriginalCommonRefinedSeedHull. ByteLiteral, NpyFrame and the round07 FullMean failure are excluded.',
            'Later retries and pipelines outside the six fixed export roots are not included in checkpoint 03.'])
    return {'schema': 'p14_checkpoint' + checkpoint + '_offline_receipt_verification_v1',
        'status': 'PASS_ARCHIVED_CLOUD_RECEIPT_CONSISTENCY_AND_CURRENT_TARGET_SOURCE_IDENTITY',
        'archive_sha256': config['sha256'], 'archive_bytes': len(raw), 'export_manifest_sha256': sha(files['EXPORT_MANIFEST.json']),
        'exported_files_verified': len(manifest['files']), 'unchanged_original_git_pairs_verified': len(git_pairs),
        'groups': totals, 'owners': reports,
        'total_owners': len(expected), 'total_owned_declarations': config['owned'], 'total_public_declarations': config['public'],
        'total_private_declarations': config['owned'] - config['public'], 'permitted_transitive_axioms': sorted(ALLOWED_AXIOMS),
        'excluded_failed_owners': config.get('excluded_failed_owners', config['shared_failures']),
        'nonaccepting_source_deployments': len(deployments),
        'normal_build_repeated_by_this_verifier': False, 'local_kernel_replay_performed': False,
        'compiled_object_binaries_exported_or_rehashed_locally': False,
        'historical_git_blobs_independently_resolved': False,
        'verification_limits': limits,
        'whole_P1_4_complete': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', choices=['01', '02', '03'], default='01')
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    archive = args.archive or args.repo / ('docs/p1/20261125/p14-continuation/evidence/checkpoint-' + args.checkpoint + '.tar.xz')
    result = verify(archive, args.repo, args.checkpoint)
    result['verifier_sha256'] = sha(Path(__file__).read_bytes())
    payload = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        args.output.write_text(payload)
    print(json.dumps({k: result[k] for k in ['status', 'groups', 'total_owners', 'total_owned_declarations',
          'local_kernel_replay_performed', 'whole_P1_4_complete']}, ensure_ascii=False))


if __name__ == '__main__':
    main()
