#!/usr/bin/env python3
"""Read-only review of already completed VE CI evidence; never invokes Lean/Lake/CI.

Inputs are immutable fixed-commit Git blobs, three saved GitHub API responses,
the downloaded ZIP, and its existing extracted originals. Writes only this
review directory. Does not extract ZIP members, modify Git refs, or run imports
of repository Python programs.
"""
from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone, timedelta
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import subprocess
import zipfile


WORK = Path('/workspace/scratch/535d89efd063')
REPO = WORK / 'goldbach-formalization'
INPUT = WORK / 'p0-round4/d0366ce-ci/ve'
ART = INPUT / 'artifact'
OUT = Path(__file__).resolve().parent
HEAD = 'd0366ce64272e81faf6166a8a90050f56b328d38'
BASELINE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
RUN_ID = 38289734726
JOB_ID = 114946657574
ARTIFACT_ID = 11765091242
ZIP_SHA = '70cb8852b79d8409d1982016ba60823982a30d7320c80195620ecf058f5d31a7'
ZIP_BYTES = 43195
TOOLCHAIN = 'leanprover/lean4:v4.33.0-rc1'
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
ALLOWED = {'Classical.choice', 'Quot.sound', 'propext'}
PRODUCTION = [
    'ImbalancedChen.VariableEnvelope',
    'ImbalancedChen.VariableEnvelopeConsequences',
    'ImbalancedChen.VariableEnvelopeRegularity',
    'ImbalancedChen.VariableEnvelopeScaled',
    'ImbalancedChen.VariableEnvelopeBoxes',
    'ImbalancedChen.VariableEnvelopeCertificates',
]
BOUNDARY = [
    'verification.VariableEnvelopeBoundary',
    'verification.VariableEnvelopeBoxesBoundary',
]
MODULES = PRODUCTION + BOUNDARY
EXPECTED_COUNTS = dict(zip(MODULES, [42, 30, 31, 31, 76, 74, 0, 74]))
checks = []


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(path: Path):
    return json.loads(path.read_text(encoding='utf-8'))


def fixed_blob(path: str, commit: str = HEAD) -> bytes:
    return subprocess.check_output(['git', '-C', str(REPO), 'show', f'{commit}:{path}'])


def check(name: str, condition: bool, evidence):
    checks.append({'name': name, 'status': 'PASS' if condition else 'FAIL', 'evidence': evidence})


def log_command(name: str):
    text = (ART / name).read_text(encoding='utf-8')
    header, body = text.split('\n', 1)
    if not header.startswith('command='):
        raise ValueError(f'{name}: missing command header')
    return json.loads(header.removeprefix('command=')), body


def utc(s: str):
    return datetime.fromisoformat(s.replace('Z', '+00:00'))


run = load(INPUT / 'run.json')
jobs = load(INPUT / 'jobs.json')['jobs']
artifact_metadata = load(INPUT / 'artifacts.json')['artifacts']
report = load(ART / 'report.json')
job = next(j for j in jobs if j['id'] == JOB_ID)
metadata = next(a for a in artifact_metadata if a['id'] == ARTIFACT_ID)

check('fixed_run_identity_and_success',
      run['id'] == RUN_ID and run['head_sha'] == HEAD
      and run['head_branch'] == 'chatgpt/chen-p0-integration'
      and run['event'] == 'push' and run['run_attempt'] == 1
      and run['status'] == 'completed' and run['conclusion'] == 'success',
      {k: run[k] for k in ['id', 'head_sha', 'head_branch', 'event', 'run_attempt', 'status', 'conclusion']})
check('actual_job_and_all_steps_success',
      len(jobs) == 1 and job['head_sha'] == HEAD and job['status'] == 'completed'
      and job['conclusion'] == 'success'
      and all(s['status'] == 'completed' and s['conclusion'] == 'success' for s in job['steps']),
      {'job_id': JOB_ID, 'actual_step_count': len(job['steps']), 'steps': job['steps']})
required_names = {
    'Explicit builds, exact regressions, bundled kernel replays and every-declaration axiom audit',
    'Record required outcome',
    'Retain actual verification logs and declaration inventory, including failures',
}
check('required_verification_outcome_and_retention_executed',
      required_names <= {s['name'] for s in job['steps']}
      and (ART / 'outcome.log').read_text() == 'verification=success\n',
      sorted(required_names))

zip_bytes = (INPUT / 'artifact.zip').read_bytes()
check('downloaded_zip_size_digest_and_api_binding',
      len(zip_bytes) == ZIP_BYTES and sha(zip_bytes) == ZIP_SHA
      and metadata['size_in_bytes'] == ZIP_BYTES and metadata['digest'] == 'sha256:' + ZIP_SHA
      and metadata['workflow_run']['id'] == RUN_ID
      and metadata['workflow_run']['head_sha'] == HEAD,
      {'id': ARTIFACT_ID, 'bytes': len(zip_bytes), 'sha256': sha(zip_bytes),
       'metadata_name': metadata['name'], 'expired_at_api_capture': metadata['expired']})
artifact_manifest = []
with zipfile.ZipFile(INPUT / 'artifact.zip') as archive:
    infos = archive.infolist()
    zip_names = [i.filename for i in infos]
    safe = all(not i.is_dir() and not PurePosixPath(i.filename).is_absolute()
               and '..' not in PurePosixPath(i.filename).parts and '\\' not in i.filename for i in infos)
    check('zip_has_27_unique_safe_regular_members',
          len(infos) == len(set(zip_names)) == 27 and safe, zip_names)
    disk_names = sorted(p.relative_to(ART).as_posix() for p in ART.rglob('*') if p.is_file())
    check('extracted_member_set_is_exact', sorted(zip_names) == disk_names, {'extracted_count': len(disk_names)})
    for info in sorted(infos, key=lambda i: i.filename):
        data = archive.read(info)
        original = (ART / info.filename).read_bytes()
        artifact_manifest.append({'path': info.filename, 'bytes': len(data), 'sha256': sha(data),
                                  'zip_to_extracted_bytes_equal': data == original})
check('all_27_original_member_bytes_equal_zip',
      all(p['zip_to_extracted_bytes_equal'] for p in artifact_manifest), {'member_count': len(artifact_manifest)})

command, body = log_command('head-commit.log')
check('compiler_runner_head_and_clean_tree_binding',
      command == ['git', 'rev-parse', 'HEAD'] and body.strip() == HEAD
      and log_command('working-tree.log') == (['git', 'status', '--porcelain'], '')
      and report['head_commit'] == HEAD and report['working_tree'] == '',
      {'head_commit': report['head_commit'], 'working_tree': report['working_tree'],
       'historical_checker_base_commit_only': report['base_commit']})
provenance = (ART / 'provenance.log').read_text()
check('workflow_provenance_matches_actual_head_toolchain_and_run',
      all(f'{key}={HEAD}\n' in provenance for key in ['head_commit', 'expected_head', 'event_commit'])
      and f'toolchain={TOOLCHAIN}\n' in provenance
      and 'lean_action_commit=f061402b660e0c34644504b324e830f2991d4865\n' in provenance
      and f'run={RUN_ID} attempt=1 event=push\n' in provenance, provenance.splitlines())

source_manifest = []
sources = {}
for path, expected_sha in report['source_sha256'].items():
    data = fixed_blob(path)
    sources[path] = data
    blob_id = subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', f'{HEAD}:{path}'], text=True).strip()
    source_manifest.append({'path': path, 'git_blob': blob_id, 'bytes': len(data), 'sha256': sha(data),
                            'reported_sha256': expected_sha, 'matches_fixed_commit': sha(data) == expected_sha})
check('all_20_reported_source_hashes_equal_fixed_commit_blobs',
      len(source_manifest) == 20 and all(p['matches_fixed_commit'] for p in source_manifest),
      {'source_commit': HEAD, 'checked_source_count': len(source_manifest)})
manifest = json.loads(sources['lake-manifest.json'])
pins = {p['name']: p['rev'] for p in manifest['packages']}
check('fixed_toolchain_and_dependency_pins',
      sources['lean-toolchain'].decode().strip() == TOOLCHAIN
      and pins['mathlib'] == 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
      and pins['goldbach'] == '09b97db5764ade1246bfb77206baa1b124760958',
      {'toolchain': TOOLCHAIN, 'dependency_pins': pins})
protected = ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']
check('toolchain_manifest_and_lakefile_unchanged_from_common_baseline',
      all(sources[p] == fixed_blob(p, BASELINE) for p in protected),
      {'baseline': BASELINE, 'paths': protected})
command, body = log_command('lean-version.log')
check('actual_pinned_lean_and_bundled_checker',
      command == ['lake', 'env', 'lean', '--version'] and body.strip() == report['lean_version']
      and 'version 4.33.0-rc1' in body and f'commit {LEAN_COMMIT}' in body
      and (ART / 'checker.log').read_text().strip().endswith('/leanprover--lean4---v4.33.0-rc1/bin/leanchecker'),
      {'lean_version': body.strip(), 'checker_log': (ART / 'checker.log').read_text().strip()})
check('reported_exact_module_scope', report['modules'] == PRODUCTION and report['boundary_modules'] == BOUNDARY,
      {'production_modules': report['modules'], 'boundary_modules': report['boundary_modules']})

runner_source = sources['verification/verify_variable_envelope_boxes.py'].decode()
audit_source = sources['verification/VariableEnvelopeBoxesAudit.lean'].decode()
workflow_source = sources['.github/workflows/variable-envelope.yml'].decode()
check('source_uses_before_after_hash_comparison_before_success',
      'report["source_sha256"] = hashes' in runner_source
      and 'for relative, expected in hashes.items():' in runner_source
      and 'Source changed during verification:' in runner_source
      and runner_source.index('for relative, expected in hashes.items():') < runner_source.index('report.update(status="PASSED"'),
      'Producer runner checks these same 20 source hashes again before PASSED; no object digest inventory is emitted by this VE runner.')
check('full_defining_module_inventory_and_kernel_axiom_safety_guards',
      all(s in audit_source for s in ['env.constants.fold', 'env.getModuleIdxFor?', 'if info.isUnsafe then',
                                      'if info.isAxiom then', 'collectAxioms name', 'unless allowed.contains ax do'])
      and all('`' + module in audit_source for module in MODULES)
      and 'sorry|admit|axiom|unsafe|native_decide' in runner_source,
      'Actual environment inventory includes private/generated declarations by defining module; successful loop rejects own axioms, unsafe declarations and forbidden transitive axioms. Records themselves have no per-declaration isUnsafe field.')
check('workflow_requires_actual_verification_success_and_keeps_logs',
      'test "$VERIFICATION_OUTCOME" = success' in workflow_source
      and 'set -euo pipefail' in workflow_source
      and 'if: ${{ always() }}' in workflow_source
      and 'path: .lake/variable-envelope-boxes-verification/' in workflow_source,
      'The required-outcome step and upload-artifact step both actually completed successfully.')

stages = report['stages']
stage_names = [s['log'] for s in stages]
check('all_16_recorded_stages_have_raw_logs_and_exit_zero',
      len(stages) == len(set(stage_names)) == 16
      and all(s['exit_code'] == 0 and (ART / s['log']).is_file() for s in stages), stages)
check('all_stage_times_fit_actual_job_interval',
      all(utc(job['started_at']) <= utc(s['started_utc'])
          and utc(s['started_utc']) + timedelta(seconds=s['elapsed_seconds']) <= utc(job['completed_at'])
          for s in stages), {'job_started_at': job['started_at'], 'job_completed_at': job['completed_at']})
runner_log = (ART / 'runner.log').read_text()
check('actual_runner_passes_all_recorded_stages',
      all(f'PASS {name}\n' in runner_log for name in stage_names)
      and 'PASS: 358 declarations, all module builds, regression checks, bundled kernel replays and full transitive axiom audit.' in runner_log
      and report['status'] == 'PASSED', {'status': report['status'], 'runner_log': 'runner.log'})

command, body = log_command('build.log')
check('six_explicit_production_builds_actually_completed',
      command == ['lake', 'build', *PRODUCTION]
      and all(re.search(r'Built ' + re.escape(m) + r' \(', body) for m in PRODUCTION)
      and 'Build completed successfully (1396 jobs).' in body,
      {'command': command, 'built_production_targets': PRODUCTION, 'lake_jobs': 1396,
       'strictness_note': 'Production targets use project lake build; explicit -DwarningAsError=true is present on the two boundary compiles and the audit.'})
boundary_commands = []
for module in BOUNDARY:
    name = module.rsplit('.', 1)[1] + '-build.log'
    command, body = log_command(name)
    relative = module.replace('.', '/')
    boundary_commands.append(command)
    check(f'strict_boundary_compile:{module}',
          command[:5] == ['lake', 'env', 'lean', '-DwarningAsError=true', '-o']
          and command[5].endswith('/.lake/build/lib/lean/' + relative + '.olean')
          and command[6:] == [relative + '.lean'] and body == '', command)
replay_commands = []
for module in MODULES:
    name = module.rsplit('.', 1)[1] + '-replay.log'
    command, body = log_command(name)
    replay_commands.append(command)
    check(f'stock_replay:{module}',
          command == ['lake', 'env', 'leanchecker', '--verbose', module]
          and body.splitlines() == ['replaying ' + module], command)

command, body = log_command('axioms.log')
check('actual_strict_axiom_inventory_command',
      command == ['lake', 'env', 'lean', '-DwarningAsError=true', 'verification/VariableEnvelopeBoxesAudit.lean'], command)
records = [json.loads(line.removeprefix('VE_AUDIT_DECL ')) for line in body.splitlines() if line.startswith('VE_AUDIT_DECL ')]
counts = [json.loads(line.removeprefix('VE_AUDIT_MODULE ')) for line in body.splitlines() if line.startswith('VE_AUDIT_MODULE ')]
totals = [int(line.removeprefix('VE_AUDIT_COUNT ')) for line in body.splitlines() if line.startswith('VE_AUDIT_COUNT ')]
actual_counts = Counter(r['module'] for r in records)
count_map = {m: actual_counts[m] for m in MODULES}
kinds = Counter(r['kind'] for r in records)
check('all_358_raw_declaration_records_equal_exported_json',
      len(records) == report['declaration_count'] == 358 and records == load(ART / 'declarations.json')
      and len({r['name'] for r in records}) == 358 and totals == [358],
      {'actual_raw_count': len(records), 'raw_count_markers': totals, 'duplicate_names': len(records) - len({r['name'] for r in records})})
check('module_counts_match_raw_markers_report_and_expected_scope',
      counts == report['module_counts'] and len(counts) == 8
      and {x['module']: x['count'] for x in counts} == count_map == EXPECTED_COUNTS,
      {'by_module': count_map, 'production_declarations': sum(actual_counts[m] for m in PRODUCTION),
       'boundary_declarations': sum(actual_counts[m] for m in BOUNDARY)})
axiom_union = sorted({a for r in records for a in r['axioms']})
check('all_358_actual_transitive_axiom_lists_allowed_and_no_own_axiom_kind',
      all(set(r['axioms']) <= ALLOWED and r['kind'] != 'axiom' for r in records)
      and set(report['allowed_transitive_axioms']) == ALLOWED,
      {'axiom_union': axiom_union, 'all_kinds': dict(kinds)})
elisions = [{'name': r['name'], 'symbol': symbol} for r in records for symbol in ['⋯', '…', '...'] if symbol in r['type']]
check('all_358_compiler_printed_default_types_present_without_observed_elision_markers',
      all(isinstance(r.get('type'), str) and r['type'] for r in records) and not elisions
      and 'Meta.ppExpr info.type' in audit_source and 'set_option pp.all true' not in audit_source,
      {'types': len(records), 'elision_markers': elisions,
       'format': 'Pinned Lean Meta.ppExpr default pretty printer; NOT pp.all, explicit-mode or raw Expr export.'})
tsv = 'module\tkind\tname\ttransitive_axioms\n' + ''.join(
    f"{r['module']}\t{r['kind']}\t{r['name']}\t{','.join(r['axioms'])}\n" for r in records)
theorem_text = (
    f'head_commit={HEAD}\n'
    'Theorem types printed by the pinned Lean elaborator.\n'
    'Includes private and automatically generated theorems.\n\n'
    + '\n\n'.join(f"[{r['module']}]\n{r['name']} :\n{r['type']}\ntransitive_axioms={','.join(r['axioms'])}"
                  for r in records if r['kind'] == 'theorem') + '\n')
check('exported_tsv_and_257_theorem_types_equal_actual_raw_inventory',
      (ART / 'declarations.tsv').read_bytes() == tsv.encode()
      and (ART / 'theorem-types.txt').read_bytes() == theorem_text.encode()
      and kinds['theorem'] == 257,
      {'theorem_count': kinds['theorem'], 'all_declaration_type_count': len(records)})
command, body = log_command('python-reference.log')
reference = json.loads(body)
check('actual_saved_python_reference_results_pass_with_scope_limits',
      command == ['/usr/bin/python3', 'verification/check_variable_envelope_reference.py']
      and reference['status'] == 'PASS' and reference['interval_cases'] == 10
      and reference['phi_range_cases'] == 15 and reference['original_sources_checked'] is False,
      {k: v for k, v in reference.items() if k != 'fixtures'})
check('targeted_mathlib_cache_evidence',
      (ART / 'cache-imports.log').read_text().splitlines() == report['mathlib_cache_imports']
      and 'Decompressed 1375 file(s)' in (ART / 'cache.log').read_text(),
      {'direct_imports': report['mathlib_cache_imports'], 'decompressed_cache_files': 1375})

passed = all(c['status'] == 'PASS' for c in checks)
receipt = {
    'schema': 'p0-independent-ve-ci-receipt-v1',
    'reviewed_utc': datetime.now(timezone.utc).isoformat(),
    'reviewer': '/root/r4_p5_intake',
    'status': 'ACCEPTED_EXISTING_CI_EVIDENCE_WITH_EXPLICIT_SCOPE' if passed else 'EVIDENCE_REVIEW_FAILED',
    'review_execution': {
        'proof_commands_executed_by_reviewer': [],
        'network_requests_by_reviewer': [],
        'method': 'Read saved original logs/metadata; verify ZIP bytes, fixed Git blobs, raw inventory and export consistency with Python. Only git show/rev-parse read Git objects.',
        'repository_mutations': False, 'original_artifact_mutations': False,
    },
    'source_commit': HEAD,
    'common_proof_baseline': BASELINE,
    'historical_checker_base_commit_only': report['base_commit'],
    'ci': {
        'run_id': RUN_ID, 'job_id': JOB_ID, 'attempt': 1,
        'run_url': run['html_url'], 'job_url': job['html_url'],
        'run_created_at': run['created_at'], 'run_updated_at': run['updated_at'],
        'job_started_at': job['started_at'], 'job_completed_at': job['completed_at'],
        'status': run['status'], 'conclusion': run['conclusion'],
        'artifact_id': ARTIFACT_ID, 'artifact_bytes': ZIP_BYTES,
        'artifact_sha256': ZIP_SHA, 'artifact_member_count': len(artifact_manifest),
    },
    'toolchain': TOOLCHAIN, 'lean_commit': LEAN_COMMIT,
    'lean_version': report['lean_version'], 'manifest_dependency_pins': pins,
    'producer_report_status': report['status'],
    'scope': report['scope'],
    'modules': [{'module': m, 'scope': 'production' if m in PRODUCTION else 'boundary',
                 'declaration_count': actual_counts[m],
                 'kind_counts': dict(Counter(r['kind'] for r in records if r['module'] == m))} for m in MODULES],
    'counts': {'all_declarations': len(records), 'production_declarations': 284,
               'boundary_declarations': 74, 'all_kinds': dict(kinds),
               'production_theorems': 191, 'boundary_theorems': 66,
               'theorem_types_txt_entries': 257, 'declarations_json_type_entries': 358},
    'axioms': {'allowed': sorted(ALLOWED), 'observed_union': axiom_union,
               'environment_safety_guard_ran': True,
               'individual_isUnsafe_field_in_original_records': False},
    'type_output': {'source': 'actual pinned Lean elaborator output in axioms.log',
                    'format': 'default Meta.ppExpr', 'pp_all': False, 'raw_expr_export': False,
                    'observed_elisions': elisions,
                    'limitation': 'Compiler-confirmed default pretty-printed types with no observed ellipsis; not an explicit/pp.all/raw-Expr completeness claim.'},
    'source_binding': {'fixed_commit_source_sha256_count': len(source_manifest),
                       'producer_before_after_source_hash_guard': True,
                       'producer_object_digest_inventory': False,
                       'stock_replay_fresh_recursive_closure': False},
    'reference_check': {k: v for k, v in reference.items() if k != 'fixtures'},
    'stage_count': len(stages), 'stages': stages,
    'first_real_lean_diagnostic_in_this_ve_run': None,
    'excluded_from_this_receipt': [
        'Full ImbalancedChen root build/replay or Round 4 414-declaration audit',
        'ImbalancedChen.StoredHistoricalBoxPermit',
        'ImbalancedChen.Certificates.PairedV2Batch4To64Data',
        'ImbalancedChen.Certificates.PairedV2Batch4To64',
        'ImbalancedChen.Certificates.PairedV2Prefix64',
        'MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser and its eight-declaration historical dependency receipt',
        'Extended x >= mu Lean envelope result and full numerical certificate acceptance',
        'Manuscript complete original Python source rehashing in this run',
        'Real analytic suppliers for K, c, hLower or hUpper and an unconditional final theorem',
    ],
    'acceptance': 'Reuse this successful producer CI receipt for the eight listed VE modules at the exact integration SHA. It supplies no new analytic hypotheses and cannot discharge the remaining conditional final bridge.',
    'check_summary': {'passed': sum(c['status'] == 'PASS' for c in checks),
                      'failed': sum(c['status'] == 'FAIL' for c in checks), 'total': len(checks)},
    'checks': checks,
    'artifact_originals_manifest': artifact_manifest,
    'fixed_sources_manifest': source_manifest,
    'input_metadata_manifest': [{'path': n, 'bytes': (INPUT / n).stat().st_size,
                                 'sha256': sha((INPUT / n).read_bytes())}
                                for n in ['run.json', 'jobs.json', 'artifacts.json']],
    'original_evidence_directory': str(INPUT),
}
(OUT / 'VE_RECEIPT.json').write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

rows = '\n'.join(f"| `{m}` | {'生产' if m in PRODUCTION else '边界'} | {actual_counts[m]} |" for m in MODULES)
stage_rows = '\n'.join(f"| `{s['log']}` | {s['elapsed_seconds']:.3f} | {s['exit_code']} |" for s in stages)
text = f'''# VE 独立实际 CI 回执

## 接收结论

**{'通过原件接收审查' if passed else '原件接收审查失败'}**：对固定集成提交 `{HEAD}`，复用已真实执行成功的 [Variable envelope verification run {RUN_ID}]({run['html_url']})，attempt 1；[实际 job {JOB_ID}]({job['html_url']}) 的步骤均执行成功。独立读取核对 {len(checks)} 项，{sum(c['status'] == 'PASS' for c in checks)} 通过、{sum(c['status'] == 'FAIL' for c in checks)} 失败。审查者只处理已保存原件与 Git 对象，没有启动 Lean、Lake、CI、网络轮询，没有修改仓库或原件。

实际 job 时间为 `{job['started_at']}` 至 `{job['completed_at']}`。API 状态为 `completed / success`；`outcome.log` 原文为 `verification=success`。因此这是一份真实已执行 CI 的验证回执。

## 固定来源与 27 件原件

| 项目 | 固定值 |
|---|---|
| 集成源码 SHA | `{HEAD}` |
| 共同证明基线 | `{BASELINE}` |
| CI artifact | `{ARTIFACT_ID}`，`{metadata['name']}` |
| ZIP 字节数 | {ZIP_BYTES} |
| ZIP SHA-256 | `{ZIP_SHA}` |
| ZIP 原件 | 27 件；与已有提取目录逐字节一致 |
| 工具链 | `{TOOLCHAIN}` |
| 实际 Lean commit | `{LEAN_COMMIT}` |
| mathlib pin | `{pins['mathlib']}` |
| goldbach pin | `{pins['goldbach']}` |

`VE_RECEIPT.json` 保存了 27 个 ZIP 成员的名称、大小、SHA-256，三份 API 元数据的 SHA-256，以及 report 中 20 项源码逐一对应的固定 Git blob、SHA-256 与匹配结果。20 项全部与集成 SHA 的 Git 对象相符。工具链文件、依赖 manifest、lakefile 与共同证明基线逐字节相同。

`report.json` 中的 `base_commit={report['base_commit']}` 是既有 VE 检查器的历史标签；本次已执行源码身份由真实 API、`provenance.log`、`head-commit.log` 和 `report.head_commit` 一致绑定为 `{HEAD}`。这两个字段不能互换。

## 显式目标与声明计数

| 模块 | 范围 | 声明数 |
|---|---|---:|
{rows}

共 **358 条声明 = 284 条生产声明 + 74 条边界声明**。`verification.VariableEnvelopeBoundary` 使用匿名 `example`，定义模块清单为 0；它仍然完成了单独的严格编译和 stock kernel replay，不能因为清单为 0 删除其执行证据。

全部声明种类是 theorem 257、definition 95、inductive 2、constructor 2、recursor 2。其中生产 theorem 191、边界 theorem 66。`theorem-types.txt` 对应 257 个 theorem；`declarations.json` 对应全部 358 条声明及其类型。接收时重新解析 `axioms.log` 的 358 条原始 JSON 记录，与该 JSON 文件完全相同，并逐字节重建核对了 TSV 与 theorem-types 文件。

## 实际编译、内核重放和公理检查

六个生产模块由原始 `lake build` 命令全部显式列出；`build.log` 各有实际 `Built` 行，并以 `Build completed successfully (1396 jobs).` 结束。该命令是项目的 Lake 构建；本回执不额外声称六个目标都带有命令行 `-DwarningAsError=true`。

两个边界模块各执行 `lake env lean -DwarningAsError=true -o ….olean ….lean`。八个模块分别执行 `lake env leanchecker --verbose MODULE`，每件 replay 原件都有准确的 `replaying MODULE` 行且 exit 0。checker 来源是 Elan 锁定工具链中的 bundled `leanchecker`。这些命令没有使用 `--fresh`；本回执不将它们扩大为所有导入依赖的递归 fresh replay。

公理审计实际执行 `lake env lean -DwarningAsError=true verification/VariableEnvelopeBoxesAudit.lean`。固定源码按 Lean 环境的 defining-module metadata 遍历常量，包含 private 与自动生成声明；遇到 `info.isUnsafe`、自定义 axiom 或不允许的传递公理即抛错。本次整个循环成功。358 条声明的实际传递公理并集为 `Classical.choice`、`Quot.sound`、`propext`，无其他公理。原始记录不含独立的 `isUnsafe` 布尔字段；这里依据实际审计源码及完整成功的循环，不伪造逐条字段。

| 原始阶段日志 | 秒 | 退出码 |
|---|---:|---:|
{stage_rows}

本次 VE 记录中没有 Lean 失败诊断；这里的“无诊断”只描述这次成功运行，不覆盖其他 Part 的历史失败记录。

## 类型输出和绑定的准确口径

358 条类型来自锁定 Lean 的 `Meta.ppExpr info.type` **默认打印器**，属于编译器确认类型。接收时未发现 `⋯`、`…`、`...` 省略标记。但本模块审计没有开启 `pp.all`、显式参数模式或输出原始 `Expr`；因此这份回执不能冒充完整展开的 `pp.all / raw Expr` 类型导出。全部 257 个 theorem 的实际文本已经在原始 `theorem-types.txt` 保留。

固定检查器在执行前记录 20 项源码 hash，并在所有阶段完成后、写入 `PASSED` 前重新比较同一列表。独立复核也把这些 hash 对齐固定 Git SHA。该 VE artifact **没有保存生产 `.olean` 的前后 digest 清单**；不能将它描述为 Round 3/4 的那类源码与对象双快照绑定。八件实际 stock replay 的证据另有原始日志保留。

Python 参考检查为 `PASS`，有 10 个 interval cases 和 15 个 phi-range cases；原始报告明确 `original_sources_checked=false`。本次使用仓库内固定参考提取物与 fixtures，没有再次读取并 rehash 手稿的完整原始 Python 文件。参考 Python 中涉及扩展表达式的 fixtures，不改变 Lean 证明的正式范围。

## 范围与仍未闭合输入

本次 Lean 的可接收范围是三变量 VE 在 **`0 ≤ z ≤ y ≤ x ≤ 25/128`** 上的结果，以及上表列出的后果、正则性、缩放、盒与 VE 证书模块和边界回归。检查器的原始 scope 也明确排除了扩展的 `x ≥ μ` 表达式与完整数值证书。

**本回执不覆盖**新增 P1 `StoredHistoricalBoxPermit`、P2 `PairedV2Batch4To64Data` / `PairedV2Batch4To64` / `PairedV2Prefix64` 的本批根验证，也不覆盖 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 的八条声明依赖接收。前者必须使用本批主工作流与 Round 4 审计原件；后者仍使用其独立历史 strict compile / stock replay / 全声明公理与绑定证据。它们都不能从这八个 VE 模块的成功推导。

本次 VE 成功不提供真实解析 `K`、`c`、`hLower`、`hUpper`，不能消去现有最终条件式桥定理的分析假设，也不构成无条件最终定理的完成记录。接收 Part 为 P0 的限定范围回归证据；各 Part 的实际构造、上下界和分布供应仍须按各自固定版本台账核验。

## 原件位置与复核入口

原始 API 与 ZIP 目录：`{INPUT}`。原件目录：`{ART}`。独立审查全部内容见同目录 `VE_RECEIPT.json`。仅重做原件一致性核对可执行：

```sh
python {OUT / 'verify_ve_receipt.py'}
```

该入口只读取 Git 对象和已有本地文件，输出本审查目录中的 JSON/Markdown；不会启动证明、CI、网络、修改 Git 或提取覆盖原件。
'''
(OUT / 'VE_RECEIPT.md').write_text(text, encoding='utf-8')
print(json.dumps({'status': receipt['status'], 'checks': receipt['check_summary'],
                  'source_sha': HEAD, 'artifact_sha256': ZIP_SHA,
                  'receipt_json_sha256': sha((OUT / 'VE_RECEIPT.json').read_bytes()),
                  'receipt_markdown_sha256': sha((OUT / 'VE_RECEIPT.md').read_bytes()),
                  'failed_checks': [c for c in checks if c['status'] == 'FAIL']},
                 ensure_ascii=False, indent=2))
raise SystemExit(0 if passed else 1)
