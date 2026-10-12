#!/usr/bin/env python3
"""Read only fixed git source and existing records; never execute Lean or CI.

Only writes this subagent's intake directory.  This is an evidence/source
cross-check, not a compiler, replay, axiom-audit, or producer-fixture rerun.
"""
from __future__ import annotations

import ast
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/workspace/scratch/535d89efd063/goldbach-formalization')
FIXED = HERE / 'fixed-source'
ROUND2 = FIXED / 'verification/parts/p4a/round2'
SOURCE = '1089a965e20664e63ffd51e0105c11befa406a1f'
PARENT = '3d5dd058cf6bef5fe90719ee277580baf8b5bf41'
BASELINE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
ORIGINAL_P4 = '262f69822a386a9d44efc059bceba11049668d68'
INTEGRATION = 'd0366ce64272e81faf6166a8a90050f56b328d38'
CHECKS: list[dict] = []


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', *args], cwd=REPO)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def require(name: str, condition: bool, **details) -> None:
    CHECKS.append({'name': name, 'status': 'PASS' if condition else 'FAIL', **details})
    if not condition:
        raise AssertionError(name)


def read_json(path: Path):
    return json.loads(path.read_text())


def signatures(text: str) -> list[dict]:
    # A proof starts at `:= by`; the type itself legitimately contains let :=.
    declarations = []
    start = re.compile(r'(?m)^(?:@\[[^\n]*?\] )?theorem ([A-Za-z_][A-Za-z0-9_]*)\b')
    proof = re.compile(r'\s:= by(?:\s|$)')
    for match in start.finditer(text):
        tail = text[match.start():]
        end = proof.search(tail)
        if end is None:
            raise ValueError(match.group(1))
        signature = tail[:end.start()].rstrip()
        assert len(list(start.finditer(signature))) == 1
        name = match.group(1)
        declarations.append({
            'name': name,
            'full_name': 'ImbalancedChen.' + name,
            'signature': signature,
            'qualified_signature': signature.replace(
                'theorem ' + name, 'theorem ImbalancedChen.' + name, 1),
        })
    return declarations


def blank_comments_and_strings(text: str) -> str:
    # Nested Lean comments and quoted strings.  This static source scan is not
    # substituted for the required compiler-owned declaration axiom inventory.
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                result.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            newline = text.find('\n', i)
            i = len(text) if newline == -1 else newline
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    assert not depth and not quoted
    return ''.join(result)


head_start = git('rev-parse', 'HEAD').decode().strip()
require('integration_head_is_d036_before_readonly_review', head_start == INTEGRATION)
require('fixed_source_parent', git('rev-parse', SOURCE + '^').decode().strip() == PARENT)
require('fixed_source_tree', git('rev-parse', SOURCE + '^{tree}').decode().strip()
        == 'ebfb0ed3ddb58504b7e33344f2d39cc960aa32d5')
subprocess.run(['git', 'merge-base', '--is-ancestor', BASELINE, SOURCE],
               cwd=REPO, check=True, capture_output=True)
require('common_baseline_is_ancestor', True)

extracted = read_json(HERE / 'FIXED_EXTRACTION_MANIFEST.json')
require('extraction_source_identity', extracted['fixed_commit'] == SOURCE
        and extracted['parent'] == PARENT)
for item in extracted['files']:
    path = item['path']
    data = (FIXED / path).read_bytes()
    original = git('show', f'{SOURCE}:{path}')
    require('fixed_source_bytes_and_manifest:' + path,
            data == original and sha(data) == item['sha256']
            and blob(data) == item['git_blob'] and len(data) == item['bytes'])

changes = []
for line in git('diff', '--name-status', PARENT, SOURCE).decode().splitlines():
    status, path = line.split('\t')
    data = git('show', f'{SOURCE}:{path}')
    changes.append({'status': status, 'path': path,
                    'git_blob': blob(data), 'sha256': sha(data), 'bytes': len(data)})
require('twenty_changed_paths', len(changes) == 20)
api_commit = read_json(HERE / 'api/commit.json')
require('github_commit_matches_git_object', api_commit['sha'] == SOURCE
        and api_commit['parents'][0]['sha'] == PARENT
        and {x['filename'] for x in api_commit['files']} == {x['path'] for x in changes})
(HERE / 'SOURCE_CHANGES.patch').write_bytes(git('diff', '--binary', PARENT, SOURCE))

saved = read_json(ROUND2 / 'SOURCE_TYPES.json')
require('source_inventory_explicitly_not_compiler',
        saved['status'] == 'SOURCE_EXTRACTED_NOT_COMPILER_INVENTORY')
module_rows = []
all_signatures = {}
observed = read_json(ROUND2 / 'OBSERVED_CHECKS.json')
observed_modules = {x['module']: x for x in observed['modules']}
for item in saved['files']:
    path = item['path']
    data = (FIXED / path).read_bytes()
    old = git('show', f'{PARENT}:{path}')
    original_p4 = git('show', f'{ORIGINAL_P4}:{path}')
    archived_path = 'verification/parts/p0/round3/ledger/snapshot-sources/' + path
    archived_d036 = git('show', f'{INTEGRATION}:{archived_path}')
    require('parent_matches_original_p4_candidate:' + path, old == original_p4)
    require('parent_matches_d036_archived_candidate:' + path, old == archived_d036)
    current_signatures = signatures(data.decode())
    previous_signatures = signatures(old.decode())
    require('all_public_headers_unchanged:' + path,
            current_signatures == previous_signatures)
    require('saved_full_headers_match_fixed_source:' + path,
            current_signatures == item['declarations'])
    require('saved_inventory_binding:' + path,
            item['sha256'] == sha(data) and item['git_blob_sha1'] == blob(data)
            and item['source_bytes'] == len(data)
            and item['public_theorem_count'] == len(current_signatures))
    transcription = observed_modules[item['module']]
    require('recovered_hashes_match_transcription:' + path,
            transcription['recovered_source_sha256'] == sha(data)
            and transcription['recovered_source_git_blob'] == blob(data))
    code = blank_comments_and_strings(data.decode())
    require('static_no_proof_escape:' + path,
            re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', code) is None
            and 'debug.skipKernelTC' not in code)
    module_rows.append({
        'module': item['module'], 'path': path,
        'public_source_theorem_count': len(current_signatures),
        'source_sha256': sha(data), 'source_git_blob': blob(data),
        'parent_sha256': sha(old), 'parent_git_blob': blob(old),
        'parent_bytes_equal_original_p4': True,
        'parent_bytes_equal_d036_archived_candidate': True,
        'd036_archived_candidate_path': archived_path,
        'source_changed': data != old,
        'public_headers_byte_identical_to_parent': True,
        'compiler_owned_declaration_count': None,
        'accepted_compiler_inventory_available': False,
        'compile_and_replay_evidence_kind': 'PRODUCER_TRANSCRIPTION_ORIGINALS_LOST',
        'strict_compile_transcribed': transcription['strict_compile_observation'],
        'individual_replay_transcribed': transcription['individual_kernel_replay_observation'],
    })
    for declaration in current_signatures:
        all_signatures[declaration['name']] = {'path': path, **declaration}
require('five_modules_fifty_three_source_theorems',
        len(module_rows) == 5
        and sum(x['public_source_theorem_count'] for x in module_rows) == 53
        and saved['public_theorem_count'] == 53)
require('exactly_three_proof_sources_changed',
        {x['path'] for x in module_rows if x['source_changed']} == {
            'ImbalancedChen/UpperCoefficientPerturbation.lean',
            'ImbalancedChen/ActualUpperDensityAssembly.lean',
            'ImbalancedChen/RealPhysicalUpperWeightBridge.lean'})
require('audit_source_unchanged',
        git('show', f'{SOURCE}:verification/Part4UpperAudit.lean')
        == git('show', f'{PARENT}:verification/Part4UpperAudit.lean'))
require('core_workflow_unchanged_from_parent',
        git('show', f'{SOURCE}:.github/workflows/lean.yml')
        == git('show', f'{PARENT}:.github/workflows/lean.yml'))

protected = []
for path in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
             'ImbalancedChen/CurrentMainTheorem.lean',
             'ImbalancedChen/CurrentNumericalTransfer.lean',
             'docs/CURRENT_MANUSCRIPT_MAP.md', 'docs/EXTERNAL_REUSE.md']:
    data = git('show', f'{SOURCE}:{path}')
    baseline = git('show', f'{BASELINE}:{path}')
    integration = git('show', f'{INTEGRATION}:{path}')
    protected.append({'path': path, 'sha256': sha(data),
                      'equals_common_baseline': data == baseline,
                      'equals_d036': data == integration})
    require('protected_bytes_unchanged:' + path, data == baseline and data == integration)

# Compute the exact repository-local import closure of the unchanged P4 root.
# External dependency sources are not re-proved by this graph calculation.
tree_files = set(git('ls-tree', '-r', '--name-only', SOURCE).decode().splitlines())
seen, external = set(), set()
pending = ['ImbalancedChen']
import_pattern = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$', re.M)
while pending:
    module = pending.pop()
    if module in seen:
        continue
    path = module.replace('.', '/') + '.lean'
    if path not in tree_files:
        external.add(module)
        continue
    seen.add(module)
    code = blank_comments_and_strings(git('show', f'{SOURCE}:{path}').decode())
    for match in import_pattern.finditer(code):
        imports = match.group(1).split()
        if imports and imports[0] == 'all':
            imports = imports[1:]
        pending.extend(imports)
targets = {x['module'] for x in module_rows}
require('no_part4_target_in_root_project_import_closure', not seen.intersection(targets))

fixture = read_json(ROUND2 / 'runner-recovery-python.json')
stdout = (ROUND2 / 'runner-recovery-fixtures.stdout.log').read_text()
stderr = (ROUND2 / 'runner-recovery-fixtures.stderr.log').read_text()
passes = re.findall(r'^PASS (.+)$', stdout, re.M)
json_line = [line for line in stdout.splitlines() if line.startswith('{')]
require('retained_python_record_matches_stdout', len(json_line) == 1
        and json.loads(json_line[0]) == fixture['fixture_results'])
require('thirty_nine_actual_python_cases_exit_zero',
        fixture['exit_code'] == 0 and fixture['status'] == 'PASSED'
        and fixture['fixture_results']['case_count'] == 39
        and passes == [x['name'] for x in fixture['fixture_results']['cases']]
        and len(passes) == 39 and not stderr
        and all(x['status'] == 'PASSED' for x in fixture['fixture_results']['cases']))
for path, digest in fixture['sha256_before'].items():
    require('retained_python_input_matches_fixed_source:' + path,
            digest == fixture['sha256_after'][path]
            and digest == sha((FIXED / path).read_bytes()))
first_fixture = read_json(ROUND2 / 'attempt1-runner-recovery-python.json')
first_stderr = (ROUND2 / 'attempt1-runner-recovery-fixtures.stderr.log').read_text()
require('first_python_failure_original_retained', first_fixture['exit_code'] == 1
        and 'AssertionError: Fixture condition failed' in first_stderr
        and 'line 161' in first_stderr)
require('python_record_does_not_claim_lean_recovery', fixture['lean_status'] == 'NOT_RERUN'
        and fixture['old_raw_logs_recovered'] is False)

# Parse, never import or execute, the fixed verifier and fixture source.
ast.parse((FIXED / 'verification/verify_part4_upper.py').read_text())
ast.parse((ROUND2 / 'verify_runner_recovery.py').read_text())
require('read_only_ast_parsing_of_fixed_python_sources', True)

run_data = read_json(HERE / 'api/runs.json')
ci = []
for run in run_data['workflow_runs']:
    require('observed_run_is_exact_p4_head:' + str(run['id']), run['head_sha'] == SOURCE)
    ci.append({key: run.get(key) for key in [
        'id', 'name', 'head_sha', 'status', 'conclusion', 'created_at', 'updated_at',
        'run_attempt', 'html_url']})
jobs = {name: read_json(HERE / 'api' / (name + '-jobs.json'))['jobs']
        for name in ['part4', 'core']}
for kind, values in jobs.items():
    for job in values:
        require('observed_job_is_exact_p4_head:' + str(job['id']), job['head_sha'] == SOURCE)

require('integration_head_unchanged_after_readonly_review',
        git('rev-parse', 'HEAD').decode().strip() == head_start)

candidate = (ROUND2 / 'COMMON_CARRIER_CANDIDATE.lean.txt').read_text()
candidate_headers = signatures(candidate)
require('common_carrier_four_source_candidate_theorems', len(candidate_headers) == 4)
require('candidate_is_not_a_compiled_production_lean_file',
        'verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt' in tree_files
        and all(x['name'] not in all_signatures for x in candidate_headers))

key_names = [
    'actualSmallRoughRho_eq_firstExitAttachment',
    'same_rho_normalized_mainTerm',
    'exists_actualSmallRoughRho_density_le_of_full_policy_limits',
    'exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits',
    'compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget',
    'actualSmallRoughRho_sieveProduct_majorant',
    'RealB_cast_le_actualSmallRoughRho_main_add_errors',
    'eventually_RealB_le_currentK_log_of_same_rho_inputs',
]
key_output = [
    '# P4 late intake: key complete source theorem signatures\n',
    f'Fixed source: `{SOURCE}`; parent: `{PARENT}`.\n',
    '**SOURCE_EXTRACTED_NOT_COMPILER_CONFIRMED.** All signatures below preserve '
    'the full written source header in its original `ImbalancedChen` namespace '
    'and imports. No implicit-argument elaboration or axiom inventory is claimed. '
    'The five production files retain all 53 public source headers byte for byte '
    'from the parent. Full original inventory is retained in '
    '`fixed-source/verification/parts/p4a/round2/SOURCE_TYPES.md` and `.json`.\n',
]
for name in key_names:
    item = all_signatures[name]
    key_output += [f'## `{name}`\n', f'Fixed path: `{item["path"]}`.\n',
                   '```lean\n' + item['signature'] + '\n```\n']
key_output += ['## Four uncompiled common-carrier candidate signatures\n',
               'Fixed path: `verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt`. '
               'These four are outside the five production modules, outside their '
               '53-source-theorem inventory, and outside the dedicated P4 audit.\n']
for item in candidate_headers:
    key_output += ['```lean\n' + item['signature'] + '\n```\n']
main_source = (FIXED / 'ImbalancedChen/CurrentMainTheorem.lean').read_text()
main = next(x for x in signatures(main_source)
            if x['name'] == 'current_theorem_1_1_of_manuscript_bounds')
key_output += ['## Unchanged final conditional entrance\n',
               'Fixed path: `ImbalancedChen/CurrentMainTheorem.lean`; byte-identical '
               'to the common baseline and d036. This transcription remains source '
               'text. The existing earlier compiler confirmation belongs to its '
               'own fixed receipt, not to this late P4 evidence.\n',
               '```lean\n' + main['signature'] + '\n```\n']
(HERE / 'KEY_TYPES.md').write_text('\n'.join(key_output))

api_records = []
for path in sorted((HERE / 'api').glob('*.json')):
    data = path.read_bytes()
    api_records.append({'path': path.relative_to(HERE).as_posix(), 'bytes': len(data),
                        'sha256': sha(data),
                        'local_saved_mtime_utc': datetime.fromtimestamp(
                            path.stat().st_mtime, timezone.utc).isoformat()})

receipt = {
    'schema': 'p0-independent-late-p4-intake-v1',
    'review_utc': datetime.now(timezone.utc).isoformat(),
    'source_commit': SOURCE, 'source_parent': PARENT,
    'original_p4_proof_source': ORIGINAL_P4,
    'source_tree': 'ebfb0ed3ddb58504b7e33344f2d39cc960aa32d5',
    'common_proof_baseline': BASELINE,
    'existing_integration_head': INTEGRATION,
    'integrated_into_d036': False,
    'acceptance': 'CANDIDATE_REGISTERED_AWAIT_COMPLETED_ORIGINAL_DEDICATED_CI_RECEIPT',
    'review_scope': 'Read-only fixed git source, retained Python records and one saved GitHub API snapshot; no Lean/Lake/replay/audit/CI execution by reviewer.',
    'review_check_count': len(CHECKS), 'checks': CHECKS,
    'changed_files': changes, 'modules': module_rows,
    'source_type_status': '53_PUBLIC_SOURCE_HEADERS_NOT_COMPILER_OWNED_INVENTORY',
    'compiler_owned_declaration_count': None,
    'compiler_confirmed_types_available_for_this_head': False,
    'protected_files': protected,
    'toolchain': (FIXED / 'lean-toolchain').read_text().strip(),
    'dependency_pins': {p['name']: p['rev'] for p in read_json(FIXED / 'lake-manifest.json')['packages']},
    'root_project_import_scope': {
        'source_commit': SOURCE,
        'project_module_count': len(seen), 'external_import_leaf_count': len(external),
        'part4_targets_in_closure': sorted(seen.intersection(targets)),
        'scope': 'Repository-local source import graph from ImbalancedChen; no proof verification or external-source audit is claimed.',
    },
    'producer_observation_status': {
        'kind': observed['record_kind'],
        'original_logs_and_generated_objects_available': False,
        'strict_compiles_transcribed_success': 5,
        'individual_stock_replays_transcribed_success': 5,
        'strict_audit_compile_transcribed': observed['audit_compile_observation'],
        'aggregate_fresh_replay': observed['aggregate_fresh_replay'],
        'finalizer': observed['finalizer'],
        'earlier_interrupted_fresh_attempt': observed['earlier_interrupted_fresh_attempt'],
        'first_original_lean_diagnostic': None,
        'first_original_lean_diagnostic_reason': 'Raw Lean diagnostics were lost before this fixed handoff; source repair descriptions are not original diagnostics.',
    },
    'retained_python_execution': {
        'record_path': 'fixed-source/verification/parts/p4a/round2/runner-recovery-python.json',
        'exit_code': 0, 'case_count': 39,
        'stdout_matches_record': True, 'inputs_match_fixed_source': True,
        'producer_fixtures_rerun_by_reviewer': False,
        'first_fixture_failure_preserved': True,
        'scope': 'Verifier Python fixtures only; not Lean proof evidence.',
    },
    'ci_snapshot_only': ci,
    'ci_jobs_snapshot': jobs,
    'api_original_records': api_records,
    'ci_scope_limit': 'The dedicated P4 run was in progress in the saved snapshot. P4-branch core and VE runs neither imply P4 audit completion nor belong to the d036 integration run. No completed dedicated artifact has been reviewed here.',
    'common_carrier_candidate': {
        'path': 'verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt',
        'sha256': sha(candidate.encode()), 'git_blob': blob(candidate.encode()),
        'public_source_theorem_count': 4,
        'compiled': False, 'in_five_module_audit': False,
        'names': [x['name'] for x in candidate_headers],
    },
    'mathematical_open_inputs': [
        'P1 complete adopted historical policy, real integral/support/majorant and compiler construction.',
        'Actual same-policy normalized full-density limit hIntegral, cap coverage hcap and strict positive gap.',
        'P2 full upper-integral certificate hCertificate for the exact same integral and precision.',
        'Compiled-versus-raw reciprocal-totient error budget on a common legal carrier, with rawBound + compilerReserve <= currentK.',
        'P4-B same Q/rho pointwise majorant, density, coprime correction and actual P3 prime-product-source distribution inputs.',
        'P5 complete Chen mean and real c/hLower suppliers; hUpper is not a prerequisite for P5.',
    ],
    'analytic_open_appendix_effect': {
        'appendix_commit_scope': INTEGRATION,
        'K_closed': False, 'hUpper_closed': False, 'c_closed': False,
        'Chen_mean_closed': False, 'hLower_closed': False,
        'p5_waits_for': 'P4-A same actual rho K density; not P4-B hUpper',
        'change': 'Update the latest P4 source/evidence identity only; previous d036 mathematical open conclusions remain unchanged.',
        'original_appendix_modified': False,
    },
    'next_acceptance_conditions': [
        'Reuse the already-running dedicated exact-head P4 run; do not duplicate or interfere.',
        'Require final successful outcome and original logs for all five strict builds, five exact stock replay markers, the complete defining-module audit, and one aggregate fresh audit-module replay.',
        'Check complete types/axiom lists for every owned private/generated/structural declaration; 53 public source signatures are not the declaration count.',
        'Bind source/dependency/three toolchain binary hashes and each present .olean/.olean.server/.olean.private output part before/after the corresponding gates; verify final head.',
        'Accept verified components into a future explicit integration batch with P0-owned root imports; keep their analytic hypotheses visible.',
        'Treat the four common-carrier .lean.txt theorems as a separate uncompiled finite candidate until explicit production/audit validation.',
    ],
}
(HERE / 'P4_LATE_INTAKE.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'status': 'PASS_READONLY_SOURCE_AND_EVIDENCE_CROSSCHECK',
                  'checks': len(CHECKS), 'source_theorems': 53,
                  'production_files_changed': 3, 'compiler_receipt_complete': False,
                  'root_project_module_count': len(seen),
                  'source_commit': SOURCE, 'integration_head_unchanged': head_start,
                  'lean_or_ci_started': False}, ensure_ascii=False))
