#!/usr/bin/env python3
"""Offline review of an ACTUAL Part 4 artifact at fixed 1089a965.

Reads an original artifact ZIP without extraction, GitHub REST metadata, and
local fixed git objects.  No network, Lean, Lake, replay, CI, or fixtures.
Writes derivatives only below this receipt-prep directory.  Never creates a
synthetic successful receipt.  Missing evidence remains INCOMPLETE.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile

PREP = Path(__file__).resolve().parent
SOURCE = '1089a965e20664e63ffd51e0105c11befa406a1f'
BASE = '1a80c1bcce67886f699d097fc37fd245cd3620bf'
RUN_ID = 38288356713
JOB_ID = 114942066124
MODULES = [
    'ImbalancedChen.ActualUpperPolicyDensity',
    'ImbalancedChen.UpperCoefficientPerturbation',
    'ImbalancedChen.ActualUpperDensityAssembly',
    'ImbalancedChen.RealPhysicalUpperWeightBridge',
    'ImbalancedChen.RealUpperCountingAssembly',
]
AUDIT = 'verification.Part4UpperAudit'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LOCKS = {
    'lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef',
    'lakefile.toml': 'b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254',
    'lake-manifest.json': '35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849',
}
FIXED_GATE_HASHES = {
    'verification/verify_part4_upper.py': '4cccc00cbb5261aedd53d3fda6a8d3d630b751cfa6f788abe29747449bbc3818',
    '.github/workflows/part4-upper.yml': '817bb054499f4b7f197957d5fe7b2fed1e26b72edef7f54fe47610fbb8ddd629',
}
PRE_LOGS = ['head-commit.log', 'working-tree.log', 'baseline-ancestor.log',
            'lean-version.log', 'lean-prefix.log', 'dependencies-and-targets-build.log']
STRICT_LOGS = [m.rsplit('.', 1)[1] + '-strict-build.log' for m in MODULES]
REPLAY_LOGS = [m.rsplit('.', 1)[1] + '-individual-replay.log' for m in MODULES]
POST_LOGS = ['axioms-and-types.log', 'all-five-and-imports-fresh-replay.log',
             'final-head-commit.log']
EXPECTED_LOGS = PRE_LOGS + STRICT_LOGS + REPLAY_LOGS + POST_LOGS
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
# Both `error:` and `error(lean.synthInstanceFailed):` are real Lean formats.
LOCATED = re.compile(
    r'^(?P<file>.+?\.lean):(?P<line>\d+):(?P<column>\d+):\s*'
    r'(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$')
SEVERITY_FIRST = re.compile(
    r'^(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s+'
    r'(?P<file>.+?\.lean):(?P<line>\d+):(?P<column>\d+):\s*(?P<message>.*)$')
GENERAL = re.compile(r'^(?:error(?:\([^)]*\))?:|uncaught exception:|'
                     r'panic(?:!|:)|AssertionError:|RuntimeError:|'
                     r'subprocess\.TimeoutExpired:)', re.I)
SHA = re.compile(r'[0-9a-f]{64}\Z')


class EvidenceUnavailable(RuntimeError):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_relative(value: str) -> bool:
    p = PurePosixPath(value)
    return bool(value) and not p.is_absolute() and '..' not in p.parts and '\\' not in value


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON key: ' + str(key))
        result[key] = value
    return result


def parse_json(data: bytes | str):
    return json.loads(data, object_pairs_hook=no_duplicate_keys)


def json_bytes(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


class Review:
    def __init__(self):
        self.gates = []
        self.inputs = []

    def gate(self, name, condition, *, missing=False, detail=None):
        status = 'PASS' if condition else ('INCOMPLETE' if missing else 'FAIL')
        self.gates.append({'name': name, 'status': status, 'detail': detail})
        return bool(condition)

    def metadata(self, path, name):
        if path is None or not path.is_file():
            self.gate(name + '_available', False, missing=True)
            return None
        data = path.read_bytes()
        self.inputs.append({'role': name, 'path': str(path.resolve()),
                            'bytes': len(data), 'sha256': digest(data)})
        try:
            return parse_json(data)
        except Exception as error:
            self.gate(name + '_json_valid', False, detail=str(error))
            return None


class Artifact:
    def __init__(self, path: Path):
        self.path = path.resolve(strict=True)
        self.raw_digest = digest(self.path.read_bytes())
        self.archive = zipfile.ZipFile(self.path)
        self.members = {}
        for info in self.archive.infolist():
            if info.is_dir():
                continue
            if not safe_relative(info.filename) or info.filename in self.members:
                raise ValueError('Unsafe or duplicate ZIP member: ' + info.filename)
            if ((info.external_attr >> 16) & 0o170000) not in {0, 0o100000}:
                raise ValueError('Nonregular ZIP member: ' + info.filename)
            self.members[info.filename] = info

    def read(self, name):
        return self.archive.read(name)

    def text(self, name):
        return self.read(name).decode('utf-8')

    def inventory(self):
        return [{'path': name, 'bytes': info.file_size, 'sha256': digest(self.read(name))}
                for name, info in sorted(self.members.items())]


class FixedSources:
    """Only git cat-file/ls-tree on explicitly supplied local repositories."""
    def __init__(self, repo, dep_repos):
        self.repos = {'project': Path(repo).resolve()}
        self.repos.update(dep_repos)
        self.revs = {'project': SOURCE}
        self.cache = {}
        self.trees = {}

    def git(self, package, *args):
        if package not in self.repos:
            return None
        env = dict(os.environ)
        env['GIT_NO_LAZY_FETCH'] = '1'
        result = subprocess.run(['git', '-C', str(self.repos[package]), *args],
                                capture_output=True, env=env, timeout=30)
        return result.stdout if result.returncode == 0 else None

    def read(self, package, path):
        key = (package, path)
        if key not in self.cache:
            self.cache[key] = (self.git(package, 'cat-file', 'blob',
                                       self.revs[package] + ':' + path)
                               if package in self.revs else None)
        return self.cache[key]

    def has(self, package, path):
        if package not in self.repos or package not in self.revs:
            return False
        if package not in self.trees:
            data = self.git(package, 'ls-tree', '-r', '--name-only', self.revs[package])
            self.trees[package] = set(data.decode().splitlines()) if data is not None else set()
        return path in self.trees[package]


def lean_code(text):
    output, depth, quoted, i = [], 0, False, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                output.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                quoted = False; i += 1
            else:
                output.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; i += 2
        elif text.startswith('--', i):
            next_line = text.find('\n', i)
            i = len(text) if next_line == -1 else next_line
        elif text[i] == '"':
            quoted = True; i += 1
        else:
            output.append(text[i]); i += 1
    if depth or quoted:
        raise ValueError('Unterminated source comment/string')
    return ''.join(output)


def first_diagnostic(name, data, *, include_warnings=False, located_only=False):
    lines = data.decode('utf-8', errors='replace').splitlines()
    for number, raw in enumerate(lines, 1):
        clean = ANSI.sub('', raw)
        located = LOCATED.match(clean) or SEVERITY_FIRST.match(clean)
        selected_lean = located and (include_warnings or located.group('severity') == 'error')
        if selected_lean or (not located_only and GENERAL.match(clean)):
            return {'artifact_member': name, 'log_sha256': digest(data),
                    'log_line': number, 'raw_line': raw,
                    'located_lean_diagnostic': located.groupdict() if located else None,
                    'context_start_line': max(1, number - 3),
                    'context': lines[max(0, number - 4):number + 35]}
    return None


def phase_for(name):
    if name == 'dependencies-and-targets-build.log':
        return 'DEPENDENCY_AND_TARGET_BUILD'
    if name in STRICT_LOGS:
        return 'STRICT_COMPILE'
    if name in REPLAY_LOGS:
        return 'INDIVIDUAL_REPLAY'
    if name == 'axioms-and-types.log':
        return 'AUDIT_COMPILE'
    if name == 'all-five-and-imports-fresh-replay.log':
        return 'AGGREGATE_FRESH_REPLAY'
    if name == 'final-head-commit.log':
        return 'FINAL_SOURCE_OBJECT_BINARY_BINDING'
    return 'PRE_TARGET_PREFLIGHT'


def derive_failure(report, stages, artifact, prefix, run_prefix):
    """Preserve raw location, without inventing diagnostics from stage labels."""
    failed = next((x for x in stages if x.get('status') != 'PASSED'
                   or x.get('exit_code') != 0), None)
    if failed:
        leaf = PurePosixPath(failed.get('log', '')).name
        phase = phase_for(leaf)
    elif report.get('status') == 'PASSED':
        phase, leaf = 'RUNNER_REPORTED_SUCCESS_PENDING_OFFLINE_REVIEW', None
    elif stages:
        leaf = PurePosixPath(stages[-1].get('log', '')).name
        if leaf == 'axioms-and-types.log':
            phase = 'AUDIT_INVENTORY_OR_POST_AUDIT_OBJECT_CHECK'
        elif leaf == 'all-five-and-imports-fresh-replay.log':
            phase = 'FRESH_MARKER_OBJECT_CHECK_OR_FINAL_BINDING'
        elif leaf in REPLAY_LOGS:
            phase = 'INDIVIDUAL_REPLAY_MARKER_OR_OBJECT_CHECK'
        elif leaf in STRICT_LOGS:
            phase = 'STRICT_OUTPUT_OBJECT_CHECK'
        elif leaf == 'final-head-commit.log':
            phase = 'FINAL_SOURCE_OBJECT_BINARY_BINDING'
        else:
            phase = 'BETWEEN_RECORDED_STAGES'
    else:
        phase, leaf = 'BEFORE_RECORDED_RUNNER_STAGE', None
    diagnostics, located_diagnostics = [], []
    order = [run_prefix + PurePosixPath(x.get('log', '')).name for x in stages]
    order += [prefix + 'runner.log', prefix + 'dependencies.log',
              prefix + 'cache.log', prefix + 'install.log']
    seen = set()
    for name in order:
        if name not in seen and name in artifact.members:
            seen.add(name)
            found = first_diagnostic(name, artifact.read(name))
            if found:
                diagnostics.append(found)
            located = first_diagnostic(name, artifact.read(name), located_only=True)
            if located:
                located_diagnostics.append(located)
    first = diagnostics[0] if diagnostics else None
    first_located = located_diagnostics[0] if located_diagnostics else None
    # A strict warning-as-error failure can have only a warning-form diagnostic.
    # Prefer actual errors; use that failed stage's warning only if no error
    # was retained. Successful dependency warnings must not mask a later error.
    failed_stage_diagnostic = None
    if failed:
        failed_member = run_prefix + PurePosixPath(failed.get('log', '')).name
        if failed_member in artifact.members:
            failed_stage_diagnostic = first_diagnostic(
                failed_member, artifact.read(failed_member), include_warnings=True)
    if first is None:
        first = failed_stage_diagnostic
    if first_located is None and failed_stage_diagnostic and failed_stage_diagnostic['located_lean_diagnostic']:
        first_located = failed_stage_diagnostic
    dependency_member = run_prefix + 'dependencies-and-targets-build.log'
    lines = artifact.text(dependency_member).splitlines()[1:] if dependency_member in artifact.members else []
    reach = []
    for module, strict in zip(MODULES, STRICT_LOGS):
        # The initial lake build names all five targets. Its command header is
        # not evidence that any target compilation was actually reached.
        markers = [line for line in lines if
                   re.search(r'\b(?:Built|Building|Replayed|Replaying)\s+'
                             + re.escape(module) + r'(?:\s|$|\()', ANSI.sub('', line))]
        source_diags = []
        module_path = module.replace('.', '/') + '.lean'
        for line in lines:
            clean = ANSI.sub('', line)
            match = LOCATED.match(clean) or SEVERITY_FIRST.match(clean)
            if match and match.group('file').endswith(module_path):
                source_diags.append(line)
        strict_stages = [x for x in stages if PurePosixPath(x.get('log', '')).name == strict]
        reach.append({'module': module, 'dependency_build_target_markers': markers,
                      'dependency_build_source_diagnostics': source_diags,
                      'strict_stage_recorded': bool(strict_stages),
                      'strict_stage': strict_stages[0] if strict_stages else None,
                      'no_evidence_is_not_proof_of_no_attempt': True})
    return {'phase': phase, 'failed_or_last_stage_log': leaf,
            'report_error_verbatim': report.get('error'),
            'first_recorded_lean_or_process_diagnostic': first,
            'first_located_lean_diagnostic': first_located,
            'first_diagnostic_in_failed_stage': failed_stage_diagnostic,
            'target_reach_evidence': reach,
            'strict_not_reached': [x['module'] for x in reach if not x['strict_stage_recorded']],
            'note': 'Phase labels are evidence triage, not reconstructed Lean diagnostics. '
                    'No strict stage does not prove the preceding lake build never reached the target.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--artifact-zip', type=Path, required=True)
    parser.add_argument('--run-json', type=Path)
    parser.add_argument('--jobs-json', type=Path)
    parser.add_argument('--artifacts-json', type=Path)
    parser.add_argument('--artifact-id', type=int)
    parser.add_argument('--repo', type=Path, required=True,
                        help='Local project git object database containing fixed 1089a965; HEAD is not changed.')
    parser.add_argument('--dependency-repo', action='append', default=[], metavar='NAME=PATH',
                        help='Explicit local git database containing the existing pinned dependency commit. Repeat as needed.')
    parser.add_argument('--output-dir', type=Path, required=True,
                        help='New, nonexisting result directory below this receipt-prep directory.')
    args = parser.parse_args()
    out = args.output_dir.resolve()
    if not out.is_relative_to(PREP) or out == PREP or out.exists():
        parser.error('--output-dir must be a new directory below receipt-prep; existing files are never overwritten')
    dep_repos = {}
    for value in args.dependency_repo:
        name, separator, path = value.partition('=')
        if (not separator or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name)
                or name == 'project' or name in dep_repos):
            parser.error('Invalid or duplicate --dependency-repo NAME=PATH')
        dep_repos[name] = Path(path).resolve()
    review = Review()
    result = {'schema': 'p0-offline-actual-p4-receipt-v1',
              'source_commit': SOURCE, 'expected_run_id': RUN_ID, 'expected_job_id': JOB_ID,
              'review_utc': datetime.now(timezone.utc).isoformat(),
              'execution_scope': 'Offline actual artifact/Git-object review only; no Lean, Lake, replay, CI, network, or fixture execution.',
              'mathematical_status': 'K, hUpper, c, full Chen mean, hLower remain open; P5 depends on P4-A, not P4-B.'}
    artifact = None
    diagnosis = None
    out.mkdir(parents=True)
    try:
        artifact = Artifact(args.artifact_zip)
        result['artifact'] = {'path': str(artifact.path), 'bytes': artifact.path.stat().st_size,
                              'sha256': artifact.raw_digest,
                              'members': artifact.inventory()}
        review.gate('original_zip_is_readable_unique_regular_members', True)
        run = review.metadata(args.run_json, 'github_run')
        jobs = review.metadata(args.jobs_json, 'github_jobs')
        artifacts = review.metadata(args.artifacts_json, 'github_artifacts')
        if run:
            review.gate('actual_run_identity', run.get('id') == RUN_ID and run.get('head_sha') == SOURCE)
            review.gate('actual_run_completed_success', run.get('status') == 'completed'
                        and run.get('conclusion') == 'success',
                        missing=run.get('status') != 'completed',
                        detail={k: run.get(k) for k in ('status', 'conclusion')})
            result['run_attempt'] = run.get('run_attempt')
        if jobs:
            entries = jobs.get('jobs', [jobs] if jobs.get('id') == JOB_ID else [])
            owned = [job for job in entries if job.get('id') == JOB_ID]
            if review.gate('actual_owned_job_present', len(owned) == 1, missing=not owned):
                job = owned[0]
                result['actual_job'] = job
                review.gate('actual_job_identity', job.get('head_sha') == SOURCE
                            and job.get('run_url', '').endswith('/actions/runs/' + str(RUN_ID)))
                review.gate('actual_job_completed_success', job.get('status') == 'completed'
                            and job.get('conclusion') == 'success', missing=job.get('status') != 'completed')
                required_steps = [
                    'Check out the exact PR head or pushed commit',
                    'Check out the existing pinned lean-action scripts',
                    'Check frozen configuration and record source provenance',
                    'Install Elan and the unchanged project toolchain',
                    'Resolve fixed dependencies and fetch their required Mathlib import closure',
                    'Five strict builds and individual replays, complete audit, and one aggregate fresh replay',
                    'Record and enforce the required outcome',
                    'Retain actual logs, complete types and inventories, including failures',
                ]
                for name in required_steps:
                    step = [x for x in job.get('steps', []) if x.get('name') == name]
                    review.gate('workflow_required_step:' + name,
                                len(step) == 1 and step[0].get('status') == 'completed'
                                and step[0].get('conclusion') == 'success',
                                missing=not step or step[0].get('status') != 'completed', detail=step)
        if artifacts:
            entries = artifacts.get('artifacts', [artifacts] if 'id' in artifacts else [])
            matching = [x for x in entries if (x.get('id') == args.artifact_id
                        if args.artifact_id is not None else
                        x.get('name') == f'part4-upper-{RUN_ID}-{result.get("run_attempt", 1)}')]
            if review.gate('actual_artifact_metadata_identified', len(matching) == 1, missing=not matching):
                meta = matching[0]
                result['artifact_metadata'] = meta
                wr = meta.get('workflow_run', {})
                review.gate('artifact_attached_to_exact_run', wr.get('id') == RUN_ID
                            and wr.get('head_sha') == SOURCE)
                review.gate('artifact_zip_digest_matches_github',
                            meta.get('digest') == 'sha256:' + artifact.raw_digest,
                            missing=not meta.get('digest'))
                review.gate('artifact_zip_size_matches_github', meta.get('size_in_bytes') == artifact.path.stat().st_size)

        top = [name for name in artifact.members if PurePosixPath(name).name == 'report.json'
               and not PurePosixPath(name).parent.name.startswith('run-')]
        if not review.gate('one_top_level_runner_report', len(top) == 1, missing=not top, detail=top):
            # Pre-runner/cache failures may legitimately have no report. Keep
            # actual early logs and their first diagnostic without fabricating one.
            first = None
            for suffix in ['runner.log', 'dependencies.log', 'cache.log', 'install.log']:
                matches = [n for n in artifact.members if PurePosixPath(n).name == suffix]
                for name in matches:
                    first = first_diagnostic(name, artifact.read(name))
                    if first:
                        break
                if first:
                    break
            diagnosis = {'phase': 'NO_RUNNER_REPORT_PRE_RUNNER_OR_MISSING_ARTIFACT',
                         'first_recorded_lean_or_process_diagnostic': first,
                         'note': 'No runner report is not a successful target check.'}
            if not top:
                raise EvidenceUnavailable('No actual top-level runner report was retained')
            raise ValueError('Cannot uniquely locate the actual top-level runner report')
        prefix = str(PurePosixPath(top[0]).parent)
        prefix = '' if prefix == '.' else prefix + '/'
        report_bytes = artifact.read(top[0])
        report = parse_json(report_bytes)
        result['runner_report'] = report
        directory = report.get('run_directory', '')
        if not review.gate('safe_exact_run_directory',
                re.fullmatch(r'\.lake/part4-upper-verification/run-[0-9]+', directory) is not None):
            raise ValueError('Unexpected run_directory')
        run_prefix = prefix + PurePosixPath(directory).name + '/'
        nested = run_prefix + 'report.json'
        review.gate('top_and_run_report_bytes_identical', nested in artifact.members
                    and artifact.read(nested) == report_bytes, missing=nested not in artifact.members)
        stages = report.get('stages', [])
        if not isinstance(stages, list):
            raise ValueError('Invalid stage list')
        diagnosis = derive_failure(report, stages, artifact, prefix, run_prefix)
        review.gate('runner_fixed_identity', report.get('head_commit') == SOURCE
                    and report.get('base_commit') == BASE and report.get('modules') == MODULES)
        review.gate('runner_final_status_passed', report.get('status') == 'PASSED',
                    missing=report.get('status') == 'RUNNING', detail=report.get('error'))
        review.gate('runner_allowed_axioms_exact', report.get('allowed_transitive_axioms') == sorted(ALLOWED))
        review.gate('runner_root_working_tree_clean', report.get('working_tree') == '')
        actual_order = [PurePosixPath(x.get('log', '')).name for x in stages]
        review.gate('all_nineteen_stages_in_fixed_order', actual_order == EXPECTED_LOGS,
                    missing=len(actual_order) < len(EXPECTED_LOGS), detail=actual_order)
        logs, bodies = {}, {}
        for stage in stages:
            leaf = PurePosixPath(stage.get('log', '')).name
            member = run_prefix + leaf
            review.gate('stage_path:' + leaf, stage.get('log') == directory + '/' + leaf)
            review.gate('stage_actual_exit_zero:' + leaf,
                        stage.get('status') == 'PASSED' and type(stage.get('exit_code')) is int
                        and stage['exit_code'] == 0,
                        missing=stage.get('status') == 'RUNNING', detail=stage)
            review.gate('stage_timeout_matches_fixed_runner:' + leaf,
                        type(stage.get('timeout_seconds')) is int
                        and stage['timeout_seconds'] == (5400 if leaf == PRE_LOGS[-1] else 1800))
            if not review.gate('original_stage_log:' + leaf, member in artifact.members, missing=True):
                continue
            text = artifact.text(member)
            header, newline, body = text.partition('\n')
            command = parse_json(header.removeprefix('command=')) if header.startswith('command=') else None
            review.gate('raw_log_command_matches_report:' + leaf,
                        bool(newline) and command == stage.get('command'))
            logs[leaf], bodies[leaf] = text, body
        source = FixedSources(args.repo, dep_repos)
        manifest_bytes = source.read('project', 'lake-manifest.json')
        if manifest_bytes is None:
            review.gate('fixed_project_git_objects_available', False, missing=True)
            manifest = None
        else:
            manifest = parse_json(manifest_bytes)
            source.revs.update({p['name']: p['rev'] for p in manifest['packages']})
            review.gate('reported_dependency_pins_match_fixed_manifest',
                        report.get('dependency_revisions') == {p['name']: p['rev'] for p in manifest['packages']})
        mandatory_sources = {*(m.replace('.', '/') + '.lean' for m in MODULES),
            'verification/Part4UpperAudit.lean', 'verification/verify_part4_upper.py',
            'verification/verify_variable_envelope_boxes.py', '.github/workflows/part4-upper.yml', *LOCKS}
        recorded_sources = report.get('source_sha256', {})
        review.gate('mandatory_source_hashes_recorded', isinstance(recorded_sources, dict)
                    and mandatory_sources <= recorded_sources.keys())
        binding, unresolved, source_bytes = [], [], {}
        packages_dir = manifest.get('packagesDir', '.lake/packages') if manifest else '.lake/packages'
        package_prefix = packages_dir.rstrip('/') + '/'
        for path, expected in recorded_sources.items():
            if not safe_relative(path) or not isinstance(expected, str) or not SHA.fullmatch(expected):
                review.gate('source_hash_record_valid:' + path, False)
                continue
            if path.startswith(package_prefix):
                package, _, relative = path.removeprefix(package_prefix).partition('/')
            else:
                package, relative = 'project', path
            raw = source.read(package, relative)
            if raw is None:
                unresolved.append({'path': path, 'package': package, 'commit': source.revs.get(package),
                                   'reported_sha256': expected})
                continue
            good = digest(raw) == expected
            review.gate('source_hash_matches_fixed_git:' + path, good)
            source_bytes[path] = raw
            binding.append({'path': path, 'package': package, 'commit': source.revs[package],
                            'sha256': digest(raw), 'git_blob': hashlib.sha1(
                                b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()})
        review.gate('all_recorded_source_bytes_independently_resolved', not unresolved,
                    missing=True, detail=unresolved)
        result['source_bindings'] = binding
        result['unresolved_fixed_source_objects'] = unresolved
        for path, expected in {**LOCKS, **FIXED_GATE_HASHES}.items():
            raw = source.read('project', path)
            review.gate('frozen_gate_source:' + path, raw is not None and digest(raw) == expected,
                        missing=raw is None)
        # Rebuild the *source* import set using fixed project/dependency objects.
        # This graph is not a compiler or kernel execution.
        pending, seen, closure, unknown, mathlib = list(MODULES), set(), set(), [], set()
        package_order = ['project'] + ([p['name'] for p in manifest['packages']] if manifest else [])
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            if module == 'Mathlib' or module.startswith('Mathlib.'):
                mathlib.add(module); continue
            if module.split('.', 1)[0] in {'Lean', 'Lake', 'Std', 'Init'}:
                continue
            relative = module.replace('.', '/') + '.lean'
            package = next((p for p in package_order if source.has(p, relative)), None)
            if package is None:
                unknown.append(module); continue
            path = relative if package == 'project' else package_prefix + package + '/' + relative
            closure.add(path)
            raw = source.read(package, relative)
            if raw is None:
                unknown.append(module); continue
            for line in lean_code(raw.decode()).splitlines():
                match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
                if match:
                    imports = match.group(1).split()
                    if imports and imports[0] == 'all':
                        imports = imports[1:]
                    if not imports or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name) for name in imports):
                        raise ValueError('Unsupported fixed import syntax: ' + path)
                    pending.extend(imports)
        review.gate('fixed_import_graph_fully_resolved', not unknown, missing=True, detail=unknown)
        if not unknown:
            expected_set = closure | (mandatory_sources - {m.replace('.', '/') + '.lean' for m in MODULES})
            review.gate('source_hash_inventory_exact_import_scope', set(recorded_sources) == expected_set,
                        detail={'missing': sorted(expected_set - set(recorded_sources)),
                                'extra': sorted(set(recorded_sources) - expected_set)})
            expected_cache = ['Mathlib'] if 'Mathlib' in mathlib else sorted(mathlib)
            review.gate('reported_mathlib_cache_import_scope', report.get('mathlib_cache_imports') == expected_cache)
        result['source_import_graph'] = {'resolved_source_files': sorted(closure),
                                         'unresolved_modules': unknown, 'mathlib_leaf_imports': sorted(mathlib)}

        by_leaf = {PurePosixPath(x.get('log', '')).name: x for x in stages}
        commands = {leaf: stage.get('command') for leaf, stage in by_leaf.items()}
        for leaf, expected in [('head-commit.log', ['git', 'rev-parse', 'HEAD']),
                               ('working-tree.log', ['git', 'status', '--porcelain']),
                               ('baseline-ancestor.log', ['git', 'merge-base', '--is-ancestor', BASE, 'HEAD']),
                               ('lean-version.log', ['lake', 'env', 'lean', '--version']),
                               ('lean-prefix.log', ['lake', 'env', 'lean', '--print-prefix']),
                               ('dependencies-and-targets-build.log', ['lake', 'build', *MODULES]),
                               ('final-head-commit.log', ['git', 'rev-parse', 'HEAD'])]:
            review.gate('fixed_command:' + leaf, commands.get(leaf) == expected, missing=leaf not in commands)
        review.gate('initial_and_final_head_logs_match', bodies.get('head-commit.log', '').strip() == SOURCE
                    and bodies.get('final-head-commit.log', '').strip() == SOURCE,
                    missing='final-head-commit.log' not in bodies)
        review.gate('actual_working_tree_log_clean', 'working-tree.log' in bodies
                    and not bodies['working-tree.log'].strip(), missing='working-tree.log' not in bodies)
        version = bodies.get('lean-version.log', '').strip()
        review.gate('actual_pinned_lean_version', version == report.get('lean_version')
                    and re.search(r'\bversion 4\.33\.0-rc1(?:[, )]|$)', version) is not None,
                    missing=not version)
        sysroot = bodies.get('lean-prefix.log', '').strip()
        review.gate('actual_sysroot_absolute', sysroot.startswith('/') and '..' not in PurePosixPath(sysroot).parts,
                    missing=not sysroot)
        binaries = report.get('toolchain_binaries', {})
        review.gate('three_binary_records_present', set(binaries) == {'lean', 'lake', 'leanchecker'},
                    missing=not binaries)
        for name in ('lean', 'lake', 'leanchecker'):
            item = binaries.get(name, {})
            review.gate('binary_record:' + name, item.get('path') == sysroot + '/bin/' + name
                        and isinstance(item.get('sha256'), str) and SHA.fullmatch(item['sha256']) is not None,
                        missing=not item)
        target_roots = []
        for module, leaf in zip(MODULES + [AUDIT], STRICT_LOGS + ['axioms-and-types.log']):
            command = commands.get(leaf, [])
            module_path = module.replace('.', '/')
            suffix = '/.lake/build/lib/lean/' + module_path + '.olean'
            good = (len(command) == 7 and command[:5] == ['lake', 'env', 'lean', '-DwarningAsError=true', '-o']
                    and isinstance(command[5], str) and command[5].startswith('/') and command[5].endswith(suffix)
                    and '..' not in PurePosixPath(command[5]).parts and command[6] == module_path + '.lean')
            review.gate('explicit_strict_command:' + module, good, missing=not command)
            if good:
                target_roots.append(command[5].removesuffix(suffix))
        review.gate('all_strict_outputs_share_one_runner_root', len(target_roots) == 6
                    and len(set(target_roots)) == 1, missing=len(target_roots) < 6)
        for module, leaf in zip(MODULES, REPLAY_LOGS):
            review.gate('individual_stock_command:' + module, commands.get(leaf)
                        == ['lake', 'env', sysroot + '/bin/leanchecker', '--verbose', module],
                        missing=leaf not in commands)
            review.gate('one_exact_individual_replay_marker:' + module,
                        bodies.get(leaf, '').splitlines().count('replaying ' + module) == 1,
                        missing=leaf not in bodies)
        fresh_leaf = 'all-five-and-imports-fresh-replay.log'
        review.gate('aggregate_fresh_stock_command', commands.get(fresh_leaf)
                    == ['lake', 'env', sysroot + '/bin/leanchecker', '--fresh', '--verbose', AUDIT],
                    missing=fresh_leaf not in commands)
        review.gate('one_exact_aggregate_fresh_marker', bodies.get(fresh_leaf, '').splitlines()
                    .count('replaying ' + AUDIT + ' with --fresh') == 1, missing=fresh_leaf not in bodies)
        review.gate('aggregate_fresh_module_record', report.get('aggregate_fresh_replay_module') == AUDIT,
                    missing='aggregate_fresh_replay_module' not in report)
        for field, modules in [('compiled_module_sha256', MODULES), ('audit_module_sha256', [AUDIT])]:
            hashes = report.get(field, {})
            primary = {'.lake/build/lib/lean/' + m.replace('.', '/') + '.olean' for m in modules}
            allowed_parts = {s + suffix for s in primary for suffix in ('', '.server', '.private')}
            good = isinstance(hashes, dict) and primary <= hashes.keys() and hashes.keys() <= allowed_parts
            good = good and all(isinstance(h, str) and SHA.fullmatch(h) for h in hashes.values())
            review.gate('recorded_object_part_sets:' + field, good, missing=not hashes,
                        detail={'paths': sorted(hashes) if isinstance(hashes, dict) else None})
        review.gate('runtime_object_part_sets_hashes_rechecked', report.get('output_part_sets_and_hashes_rechecked') is True,
                    missing='output_part_sets_and_hashes_rechecked' not in report)
        review.gate('runtime_three_binary_hashes_rechecked', report.get('toolchain_binary_hashes_rechecked') is True,
                    missing='toolchain_binary_hashes_rechecked' not in report)
        result['object_and_binary_evidence_scope'] = (
            'Recorded hashes plus successful execution of the exact fixed runner recheck guards. '
            'This artifact directory does not ordinarily contain target object or executable bytes; '
            'the offline reviewer does not claim to rehash absent bytes. Only .olean/.olean.server/.olean.private '
            'target/audit parts are inventoried; imported object bytes are covered by stock --fresh semantics, not a per-object hash inventory.')

        audit_body = bodies.get('axioms-and-types.log', '')
        records = [parse_json(line.removeprefix('PART4_UPPER_AUDIT_DECL ')) for line in audit_body.splitlines()
                   if line.startswith('PART4_UPPER_AUDIT_DECL ')]
        counts = [parse_json(line.removeprefix('PART4_UPPER_AUDIT_MODULE ')) for line in audit_body.splitlines()
                  if line.startswith('PART4_UPPER_AUDIT_MODULE ')]
        totals = [int(line.removeprefix('PART4_UPPER_AUDIT_COUNT ')) for line in audit_body.splitlines()
                  if line.startswith('PART4_UPPER_AUDIT_COUNT ')]
        review.gate('raw_complete_audit_inventory_present', bool(records) and totals == [len(records)],
                    missing=not totals, detail={'actual_records': len(records), 'raw_totals': totals})
        review.gate('raw_five_module_count_records', len(counts) == 5
                    and {x.get('module') for x in counts} == set(MODULES), missing=not counts)
        review.gate('unique_owned_declaration_names', len({x.get('name') for x in records}) == len(records))
        computed = Counter(x.get('module') for x in records)
        for item in counts:
            review.gate('actual_module_count:' + str(item.get('module')),
                        type(item.get('count')) is int and item['count'] > 0
                        and item['count'] == computed[item.get('module')])
        allowed_kinds = {'theorem', 'definition', 'opaque', 'quotient', 'inductive', 'constructor', 'recursor'}
        invalid = []
        for item in records:
            reasons = []
            if item.get('module') not in MODULES or item.get('kind') not in allowed_kinds:
                reasons.append('wrong owned module or forbidden/unknown declaration kind')
            if not isinstance(item.get('name'), str) or not item['name']:
                reasons.append('missing declaration name')
            axes = item.get('axioms')
            if not isinstance(axes, list) or any(not isinstance(x, str) for x in axes) or set(axes) - ALLOWED:
                reasons.append('forbidden or malformed transitive axiom list')
            universes = item.get('universe_parameters')
            if not isinstance(universes, list) or any(not isinstance(x, str) for x in universes):
                reasons.append('missing/malformed universe parameters')
            typ = item.get('type')
            if not isinstance(typ, str) or not typ.strip() or '⋯' in typ:
                reasons.append('missing/elided complete type')
            if reasons:
                invalid.append({'name': item.get('name'), 'reasons': reasons})
        review.gate('every_owned_type_and_axiom_record_valid', not invalid, detail=invalid)
        review.gate('report_counts_match_raw_inventory',
                    type(report.get('declaration_count')) is int and report['declaration_count'] == len(records)
                    and report.get('module_counts') == counts, missing='declaration_count' not in report)
        public_names = {}
        for module in MODULES:
            path = module.replace('.', '/') + '.lean'
            raw = source_bytes.get(path)
            if raw:
                names = re.findall(r'(?m)^(?:@\[[^\n]*?\] )?theorem ([A-Za-z_][A-Za-z0-9_]*)\b', raw.decode())
                public_names.update({'ImbalancedChen.' + name: module for name in names})
        actual_names = {x.get('name'): x for x in records}
        absent_public = [name for name, module in public_names.items()
                         if name not in actual_names or actual_names[name].get('module') != module
                         or actual_names[name].get('kind') != 'theorem']
        review.gate('fixed_public_source_theorems_in_owned_inventory', len(public_names) == 53
                    and not absent_public, missing=not records or len(public_names) != 53,
                    detail={'source_public_theorem_count': len(public_names), 'missing': absent_public,
                            'note': '53 is only the independently source-extracted public subset, never the owned declaration total.'})
        header = (f'head_commit={SOURCE}\n'
                  'Complete types printed by the pinned Lean elaborator with pp.all=true.\n'
                  'Includes private and generated declarations. Hypotheses remain hypotheses.\n\n')
        generated = {'declarations.json': json_bytes(records),
                     'declarations.tsv': ('module\tkind\tname\ttransitive_axioms\n' + ''.join(
                         f"{x['module']}\t{x['kind']}\t{x['name']}\t{','.join(x['axioms'])}\n"
                         for x in records)).encode()}
        # The fixed runner uses json.dumps with ensure_ascii=True for this one
        # file; compare its parsed data below, while type/TSV bytes remain exact.
        for filename, selected in [('declaration-types.txt', records),
                                    ('theorem-types.txt', [x for x in records if x.get('kind') == 'theorem'])]:
            text = header + '\n\n'.join(
                f"[{x['module']}]\n{x['name']}\nuniverse_parameters={','.join(x['universe_parameters'])}\n"
                f"type:\n{x['type']}\ntransitive_axioms={','.join(x['axioms'])}" for x in selected) + '\n'
            generated[filename] = text.encode()
        for filename, expected in generated.items():
            name = run_prefix + filename
            available = name in artifact.members
            same = (parse_json(artifact.read(name)) == records if filename == 'declarations.json'
                    else artifact.read(name) == expected) if available else False
            review.gate('complete_export_matches_raw_audit:' + filename, same, missing=not available)
        result['actual_inventory_counts'] = {'declarations': len(records),
            'theorems': sum(x.get('kind') == 'theorem' for x in records),
            'by_module': dict(computed), 'by_kind': dict(Counter(x.get('kind') for x in records)),
            'transitive_axiom_union': sorted({a for x in records for a in x.get('axioms', [])})}

        for name in ('provenance.log', 'lockfiles.log', 'install.log', 'dependencies.log',
                     'cache-imports.log', 'cache.log', 'runner.log', 'outcome.log'):
            review.gate('workflow_original_log:' + name, prefix + name in artifact.members, missing=True)
        provenance = artifact.text(prefix + 'provenance.log') if prefix + 'provenance.log' in artifact.members else ''
        values = dict(line.split('=', 1) for line in provenance.splitlines() if '=' in line)
        review.gate('provenance_exact_head_toolchain_action', values.get('head_commit') == SOURCE
                    and values.get('expected_head') == SOURCE and values.get('event_commit') == SOURCE
                    and values.get('lean_action_commit') == 'f061402b660e0c34644504b324e830f2991d4865'
                    and values.get('toolchain') == 'leanprover/lean4:v4.33.0-rc1', missing=not provenance)
        run_marker = re.search(r'^run=(\d+) attempt=(\d+) event=(\S+)\s*$', provenance, re.M)
        review.gate('provenance_exact_run_attempt', bool(run_marker)
                    and int(run_marker.group(1)) == RUN_ID
                    and int(run_marker.group(2)) == result.get('run_attempt'), missing=not run_marker)
        outcome = artifact.text(prefix + 'outcome.log') if prefix + 'outcome.log' in artifact.members else ''
        review.gate('required_outcomes_actual_success', outcome == 'cache=success\nverification=success\n', missing=not outcome)
        wrapper = artifact.text(prefix + 'runner.log') if prefix + 'runner.log' in artifact.members else ''
        wrapper_lines = wrapper.splitlines()
        for leaf in EXPECTED_LOGS:
            review.gate('wrapper_stage_start_and_pass:' + leaf,
                        wrapper_lines.count('START ' + leaf) == 1 and wrapper_lines.count('PASS ' + leaf) == 1,
                        missing=not wrapper)
        final_message = (f'PASS: 5 explicit builds and individual kernel replays; '
                         'one aggregate fresh replay of all five modules and their imports; '
                         f'{len(records)} declarations with complete types and only allowed axioms.')
        review.gate('actual_final_runner_pass_message', wrapper_lines.count(final_message) == 1, missing=not wrapper)
    except Exception as error:
        review.gate('offline_review_completed_without_parse_exception', False,
                    missing=isinstance(error, (FileNotFoundError, zipfile.BadZipFile, EvidenceUnavailable)),
                    detail=f'{type(error).__name__}: {error}')
    finally:
        result['failure_localization'] = diagnosis
        result['gates'] = review.gates
        result['metadata_inputs'] = review.inputs
        failures = [x for x in review.gates if x['status'] == 'FAIL']
        incomplete = [x for x in review.gates if x['status'] == 'INCOMPLETE']
        result['offline_receipt_status'] = ('REJECTED_OR_FAILED_EVIDENCE' if failures else
                                             'INCOMPLETE_EVIDENCE' if incomplete else
                                             'READY_FOR_P0_COMPONENT_ACCEPTANCE_REVIEW')
        result['gate_counts'] = dict(Counter(x['status'] for x in review.gates))
        result['proof_commands_run_by_offline_reviewer'] = []
        result['numerical_or_analytic_hypotheses_discharged_by_receipt'] = False
        first = diagnosis.get('first_recorded_lean_or_process_diagnostic') if diagnosis else None
        if first and artifact:
            (out / 'FIRST_DIAGNOSTIC.json').write_bytes(json_bytes(first))
            member = first['artifact_member']
            (out / 'first-diagnostic-original-stage.log').write_bytes(artifact.read(member))
            (out / 'FIRST_DIAGNOSTIC.txt').write_text(
                'Actual original artifact member: ' + member + '\n'
                + 'SHA-256: ' + first['log_sha256'] + '\n'
                + 'First diagnostic at log line ' + str(first['log_line']) + '\n\n'
                + '\n'.join(first['context']) + '\n')
        first_lean = diagnosis.get('first_located_lean_diagnostic') if diagnosis else None
        if first_lean and artifact:
            (out / 'FIRST_LOCATED_LEAN_DIAGNOSTIC.json').write_bytes(json_bytes(first_lean))
            (out / 'first-located-lean-diagnostic-original-stage.log').write_bytes(
                artifact.read(first_lean['artifact_member']))
        if diagnosis and diagnosis.get('failed_or_last_stage_log') and artifact:
            leaf = diagnosis['failed_or_last_stage_log']
            matches = [n for n in artifact.members if PurePosixPath(n).name == leaf]
            if len(matches) == 1:
                (out / 'first-failing-or-last-stage.log').write_bytes(artifact.read(matches[0]))
        (out / 'OFFLINE_RECEIPT.json').write_bytes(json_bytes(result))
        lines = ['# Actual P4 artifact offline receipt', '',
                 f"Status: **{result['offline_receipt_status']}**", '',
                 f'Fixed source: `{SOURCE}`; expected run `{RUN_ID}`, job `{JOB_ID}`.', '',
                 'No proof commands were run by this offline review. Actual declaration counts are read from the artifact.', '',
                 '## Failing or incomplete gates', '']
        lines += [f"- `{x['status']}` `{x['name']}`: {json.dumps(x['detail'], ensure_ascii=False)}" for x in failures + incomplete]
        if not failures and not incomplete:
            lines.append('All implemented receipt gates passed on this actual artifact; P0 still owns integration and analytic scope review.')
        lines += ['', '## Scope', '', result['mathematical_status'], '',
                  'Recorded target/executable hashes and successful runtime rechecks are distinguished from offline rehashing of absent object bytes.']
        (out / 'OFFLINE_RECEIPT.md').write_text('\n'.join(lines) + '\n')
        output_manifest = []
        for file in sorted(out.iterdir()):
            if file.is_file():
                data = file.read_bytes()
                output_manifest.append({'path': file.name, 'bytes': len(data), 'sha256': digest(data)})
        (out / 'OUTPUT_MANIFEST.json').write_bytes(json_bytes(output_manifest))
        print(json.dumps({'status': result['offline_receipt_status'], 'gate_counts': result['gate_counts'],
                          'output_dir': str(out), 'source_commit': SOURCE,
                          'diagnostic_phase': diagnosis.get('phase') if diagnosis else None}, ensure_ascii=False))
    return 1 if failures else 2 if incomplete else 0


if __name__ == '__main__':
    sys.exit(main())
