#!/usr/bin/env python3
"""Resume unchanged 377-module / 69-owned gates from completed round 10."""
from pathlib import Path
import argparse
import copy
import datetime
import gzip
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import traceback
import types

ROOT = Path('/workspace/p2-saving16-20261125')
PREVIOUS = 'f7871b382377385a75495b360f974b1ccabeb638'
# Digest of the original remote round-10 RUN_RESULT.json, verified after transport.
PRIOR_RESULT_SHA = '0c727a13fd016dc97b0de35674998c91f76b30f78bbdffe1ad86b12001084d6a'
PRIOR_NORMAL_SUCCESSFUL = 355
PRIOR_NORMAL_REUSED = 354
PRIOR_OWNED_ACCEPTED = 48
ROUND2 = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'
HELPER = ROUND2 + '/run_followup_round2.py'
HELPER_SHA = 'bd3a0e94025c837897ec12d9c1350cb6f236c2902c09844517cab7a0a91b3591'
ROUND4_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round4.py'
ROUND4_RUNNER_SHA = '803a84486461cf1b5f775c2b4d6af1a380826680de94648233cfa86e45d89ad3'
ROUND4_SELECTION = 'docs/source-only/20261126-p2-5-round4-repairs/SOURCE_SELECTION.json'
ROUND4_SELECTION_SHA = '196e4617434c4f11daef8f13a1b29cece718125a945805292c1783c9100ee574'
ROUND5_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round5.py'
ROUND5_RUNNER_SHA = '86958de9c9a265fa39fa6ea79f019f376fc425e5445c9b75ba6306b98d5ae9ab'
ROUND5_SELECTION = 'docs/source-only/20261126-p2-5-round5-repairs/SOURCE_SELECTION.json'
ROUND5_SELECTION_SHA = '9bfb235dbd60eae3872b114e9569dfce315cd6dc0f96f4107b7df34ae16d6da5'
ROUND6_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round6.py'
ROUND6_RUNNER_SHA = '11c62f535a94f53ed4b22b7f08e55c8476529c49ec4b5d3cd6e219d3f04292f3'
ROUND6_SELECTION = 'docs/source-only/20261126-p2-5-round6-candidates/SOURCE_SELECTION.json'
ROUND6_SELECTION_SHA = 'f5859c478bf4b80b436e6c756f6aa9529c24d003c2ebd63dba8fbd6512f9c1f9'
ROUND7_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round7.py'
ROUND7_RUNNER_SHA = '7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0'
ROUND7_SELECTION = 'docs/source-only/20261126-p2-5-round7-candidates/SOURCE_SELECTION.json'
ROUND7_SELECTION_SHA = 'a50d75f57d17a781b4330d41249c168e1fabfbca1af979ec2a451ec791fd7269'
ROUND8_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round8.py'
ROUND8_RUNNER_SHA = '80621605d26f106af1343caee1679e4b1db5e5f36c4264722032add9a383be73'
ROUND8_SELECTION = 'docs/source-only/20261126-p2-5-round8-candidates/SOURCE_SELECTION.json'
ROUND8_SELECTION_SHA = '3e9c62ca4dec8f88a15aaead1c80448de245d969a48bd82ee7c4748114ba9ba4'
ROUND9_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round9.py'
ROUND9_RUNNER_SHA = '651cdc8e5a919eb3b3009eeb1a16bb7708947b2e0f25516f95a17abf9c9c20f8'
ROUND9_SELECTION = 'docs/source-only/20261126-p2-5-round9-candidates/SOURCE_SELECTION.json'
ROUND9_SELECTION_SHA = '8bccb1c8975ef4470b75af82a2c7b64bf8d6d1e94a444faf73dad47397b6c1a1'
ROUND10_RUNNER = 'docs/verification/20261127-p2-5-resumed/run_p2_round10.py'
ROUND10_RUNNER_SHA = '7ad62f06c88fa0d145cc125bb9044e939f8a3988e8691c9116eb62364b517fd1'
ROUND10_SELECTION = 'docs/source-only/20261127-p2-5-round10-candidate/SOURCE_SELECTION.json'
ROUND10_SELECTION_SHA = 'b5f86332194f3fdf54d8dc7c44a603faec02ded85939da3b29221863d5e51908'
RUNNER = 'docs/verification/20261127-p2-5-resumed/run_p2_round11.py'
PACKAGE = 'docs/source-only/20261127-p2-5-round11-candidate'
EXPECTED_REPAIRS = (
    'ImbalancedChen.P1OriginalVariableFifthFullModulusBound',
)
PRIOR_OUT = '.lake/p25-followup-repairs-attempt010'
NEW_OUT = '.lake/p25-followup-repairs-attempt011'
PRIOR_SUMMARY = '.lake/p2-private/audit/p25-round10-repairs-owned-audit.json'
SUMMARY_NAME = 'p25-round11-repairs-owned-audit.json'
MIN_FREE_BYTES = 1073741824


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()


def validated_graph(graph, target_document, selection):
    modules, targets = graph['modules'], target_document['modules']
    require(len(modules) == graph['project_modules'] == 377, 'Expected the unchanged 377-module scope')
    require(len(graph['roots']) == len(set(graph['roots'])) == 5
            and set(graph['roots']) <= set(modules), 'Compile roots changed')
    require(len(targets) == len(set(targets)) == target_document['count'] == 69
            and set(targets) <= set(modules), 'Expected 69 distinct owned targets')
    rows = selection['changed_modules']
    require(tuple(row['module'] for row in rows) == EXPECTED_REPAIRS,
            'Expected the single reviewed round-11 repair')
    updated = copy.deepcopy(graph)
    for row in rows:
        name = row['module']
        require(name in modules and row['source'] == modules[name]['source']
                == name.replace('.', '/') + '.lean', 'Repair source path differs')
        require(row['before_sha256'] == modules[name]['sha256'], 'Repair preimage differs: ' + name)
        require(re.fullmatch(r'[0-9a-f]{64}', row['after_sha256']) is not None
                and row['after_sha256'] != row['before_sha256'], 'Invalid repair postimage: ' + name)
        require(row['imports_unchanged'] and row['options_unchanged'], 'Repair import/option scope changed')
        updated['modules'][name]['sha256'] = row['after_sha256']
    priority = [row['module'] for row in rows if row['module'] in targets]
    ordered = priority + [name for name in targets if name not in priority]
    require(priority == selection['changed_audit_targets'] and len(priority) == 0
            and len(ordered) == 69 and set(ordered) == set(targets), 'Audit scope/order differs')
    dependency_only = [row['module'] for row in rows if row['module'] not in targets]
    require(dependency_only == selection['changed_dependency_only_modules'] and len(dependency_only) == 1,
            'Changed dependency-only scope differs')
    return updated, ordered


def verify_sources(root, graph, parse_imports):
    for name, row in graph['modules'].items():
        path = root / row['source']
        require(row['source'] == name.replace('.', '/') + '.lean'
                and root.resolve() in path.resolve().parents, 'Source escapes project: ' + name)
        require(path.is_file() and sha(path) == row['sha256'], 'Source hash differs: ' + name)
        actual = [item for item in parse_imports(path.read_text()) if item.startswith('ImbalancedChen.')]
        require(actual == row['imports'], 'Source imports differ: ' + name)


def validate_previous_result(previous, roots, targets, prior_selection):
    require_prior_pins()
    require(previous['source_commit'] == PREVIOUS and previous.get('ended_utc'), 'Round 10 is not complete at its recorded origin')
    require(previous['runner_sha256'] == ROUND10_RUNNER_SHA
            and previous['source_selection_sha256'] == ROUND10_SELECTION_SHA
            and previous['changed_sources'] == prior_selection['changed_modules']
            and previous['changed_owned_targets'] == prior_selection['changed_audit_targets']
            and previous['changed_dependency_only_modules'] == prior_selection['changed_dependency_only_modules'],
            'Round-10 source/control provenance differs')
    compiled, audited = previous['compile_summary'], previous['audit_summary']
    require(compiled['roots'] == roots == previous['compile_roots'] and compiled['total'] == 377
            and compiled['successful_closure'] == PRIOR_NORMAL_SUCCESSFUL and compiled['reused'] == PRIOR_NORMAL_REUSED
            and compiled['pending'] == [] and previous['project_modules'] == 377, 'Round-10 normal result differs')
    require(audited['requested'] == previous['owned_targets'] == 69 and audited['accepted'] == PRIOR_OWNED_ACCEPTED
            and set(audited['modules']) == set(targets)
            and sum(row['accepted'] is True for row in audited['modules'].values()) == PRIOR_OWNED_ACCEPTED,
            'Round-10 owned result differs')
    require(previous['accepted'] is False and previous['compile_exit'] == previous['audit_exit'] == 1
            and all(previous.get(key) is True for key in ['source_after_matches', 'gate_after_matches',
                'runner_after_matches', 'external_after_matches', 'head_after_matches',
                'history_after_matches', 'baseline_after_matches', 'prior_normal_reuse_after_matches',
                'prior_owned_reuse_after_matches']), 'Round-10 completed postflight differs')


def require_prior_pins():
    require(isinstance(PRIOR_RESULT_SHA, str) and re.fullmatch(r'[0-9a-f]{64}', PRIOR_RESULT_SHA) is not None,
            'Round-10 final receipt has not been pinned; this draft cannot execute')
    require(all(type(value) is int for value in
                (PRIOR_NORMAL_SUCCESSFUL, PRIOR_NORMAL_REUSED, PRIOR_OWNED_ACCEPTED))
            and 0 <= PRIOR_NORMAL_REUSED <= PRIOR_NORMAL_SUCCESSFUL <= 377
            and 0 <= PRIOR_OWNED_ACCEPTED <= 69,
            'Round-10 final counts have not been pinned; this draft cannot execute')


def validate_repair_failures(selection, compiled, compile_log):
    rows = re.findall(r'^FAIL (ImbalancedChen\.[A-Za-z0-9_.]+) (-?\d+)\s*$', compile_log, re.M)
    require(all(int(code) != 0 for _, code in rows), 'A successful exit was labelled as a normal failure')
    direct = sorted({name for name, _ in rows})
    require(set(direct) <= set(compiled['failed_or_blocked']),
            'Direct failure is outside the terminal failed scope')
    require({row['module'] for row in selection['changed_modules']} <= set(direct),
            'A selected repair was not an actually executed failure; blocked modules cannot be preemptively changed')
    return direct


def validate_reuse(graph, previous, selection, external, original):
    """Prove the failed closure and replay eligibility before allocating this attempt."""
    from run_winner9_private_audit import (
        artifacts_valid, project_nodes, snapshot, verify_compilation,
    )
    from winner9_external_snapshot import mark_project_nodes

    modules = graph['modules']
    affected = set(EXPECTED_REPAIRS)
    while True:
        expanded = affected | {m for m, row in modules.items() if affected.intersection(row['imports'])}
        if expanded == affected:
            break
        affected = expanded
    prior_failed = set(previous['compile_summary']['failed_or_blocked'])
    summaries = previous['audit_summary']['modules']
    unaccepted = {m for m, r in summaries.items() if not r['accepted']}
    require(affected == prior_failed == set(selection['affected_closure'])
            and affected.intersection(summaries) == unaccepted == set(selection['affected_owned_targets']),
            'Repair invalidates a previously qualified normal or owned result')
    normal = set(modules) - affected
    owned = set(summaries) - unaccepted
    require(len(normal) == selection['qualified_normal_reuse_candidates'] == PRIOR_NORMAL_SUCCESSFUL
            and len(owned) == selection['qualified_owned_reuse_candidates'] == PRIOR_OWNED_ACCEPTED,
            'Unexpected prior qualification counts')
    lib = ROOT / '.lake/p2-private/lib'
    nodes = {n: {'source': ROOT / modules[n]['source'], 'deps': modules[n]['imports']} for n in normal}
    mark_project_nodes(nodes, set(external.modules))
    toolchain = {'lean_version': subprocess.check_output([original.LEAN, '--version'], text=True).strip(),
                 'lean_binary_sha256': sha(original.LEAN), 'mathlib_commit': original.MATHLIB_COMMIT}
    frozen = snapshot(ROOT, lib, nodes, toolchain, external)
    records = json.loads((ROOT / '.lake/p2-private/records.json').read_bytes())
    verify_compilation(records, nodes, frozen)
    for name in sorted(owned):
        closure = project_nodes(ROOT, name)
        require(set(closure) <= normal, 'An accepted audit includes a modified dependency: ' + name)
        expected = dict(frozen, project={m: frozen['project'][m] for m in closure})
        if not any(nodes[m]['requires_external'] for m in closure):
            expected.pop('external_snapshot', None)
        prior = json.loads((ROOT / '.lake/p2-private/audit' / name / 'latest.json').read_bytes())
        require(prior.get('accepted') is True and prior.get('input_snapshot') == expected
                and artifacts_valid(ROOT, prior.get('artifacts', {})),
                'A previously accepted audit cannot be reused by the original audit driver: ' + name)


def normal_reuse_postflight(modules, prior_failed, before, after, summary, log):
    """Cross-check each actual START with the stock driver's attempts and terminal events."""
    affected = set(prior_failed)
    preserved = set(modules) - affected
    starts = re.findall(r'^START (ImbalancedChen\.[\w.]+)$', log, re.M)
    finishes = re.findall(r'^(PASS|FAIL) (ImbalancedChen\.[\w.]+) [\d.-]+$', log, re.M)
    completed = [name for _, name in finishes]
    grew, replaced = [], []
    for name in sorted(modules):
        old = before.get(name, {}).get('attempts', [])
        new = after.get(name, {}).get('attempts', [])
        if new[:len(old)] != old:
            replaced.append(name)
        if len(new) > len(old):
            grew.append(name)
    evidence = {'start_events': starts, 'terminal_events': completed, 'fresh_attempt_modules': grew,
                'changed_historical_attempts': replaced, 'prior_passes_started': sorted(preserved.intersection(starts))}
    if not summary:
        return False, evidence
    unfinished = set(summary['failed_or_blocked']) | set(summary['pending'])
    passed = sum(stage == 'PASS' for stage, _ in finishes)
    valid = (not replaced and len(set(starts)) == len(starts) == len(completed) == len(set(completed))
             and set(starts) == set(completed) == set(grew) and set(starts) <= affected
             and not preserved.intersection(unfinished) and summary['reused'] >= len(preserved)
             and summary['successful_closure'] == summary['reused'] + passed)
    return valid, evidence


def owned_reuse_postflight(prior_rows, summary, log):
    """Check the old successful inventory against reuse rows and both kernel execution markers."""
    prior = {name: row['declarations'] for name, row in prior_rows.items() if row['accepted']}
    rows = (summary or {}).get('modules', {})
    reused = re.findall(r'^REUSE_AUDIT (ImbalancedChen\.[\w.]+) (\d+)$', log, re.M)
    reused_counts = {name: int(count) for name, count in reused}
    executed = re.findall(r'^(?:REPLAY|AUDIT) (ImbalancedChen\.[\w.]+)$', log, re.M)
    expected = {name: row.get('declarations') for name, row in rows.items()
                if row.get('accepted') is True and row.get('reused') is True}
    invalid = sorted(name for name, count in prior.items() if expected.get(name) != count)
    redundant = sorted(set(prior).intersection(executed))
    evidence = {'reuse_events': reused_counts, 'executed_replay_or_audit': sorted(set(executed)),
                'prior_passes_without_qualified_reuse_row': invalid, 'prior_passes_executed': redundant}
    return (len(reused) == len(reused_counts) and expected == reused_counts and not invalid and not redundant), evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('--runner-sha256', required=True)
    parser.add_argument('--selection-sha256', required=True)
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Run without Python -O; original gate assertions must remain enabled')
    require_prior_pins()
    require(re.fullmatch(r'[0-9a-f]{40}', args.publication_commit) is not None, 'Expected full publication commit')
    require(re.fullmatch(r'[0-9a-f]{64}', args.runner_sha256) is not None
            and sha(__file__) == args.runner_sha256, 'Runner review pin differs')
    require(re.fullmatch(r'[0-9a-f]{64}', args.selection_sha256) is not None,
            'Expected a complete reviewed selection hash')
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    sys.dont_write_bytecode = True

    def output(command):
        return subprocess.check_output(command, cwd=ROOT, text=True).strip()

    def published(path):
        return subprocess.check_output(['git', 'show', args.publication_commit + ':' + path], cwd=ROOT)

    def save_json(path, value):
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

    def now():
        return datetime.datetime.now(datetime.timezone.utc).isoformat()

    require(output(['git', 'rev-parse', 'HEAD']) == PREVIOUS, 'Expected the preserved round-10 checkout')
    require(not output(['git', 'status', '--porcelain', '--untracked-files=no']), 'Tracked worktree is not clean')
    subprocess.check_call(['git', 'merge-base', '--is-ancestor', PREVIOUS, args.publication_commit], cwd=ROOT)
    require(published(RUNNER) == Path(__file__).read_bytes(), 'Published runner differs from reviewed runner')
    prior_controls = {HELPER: HELPER_SHA, ROUND4_RUNNER: ROUND4_RUNNER_SHA,
                      ROUND4_SELECTION: ROUND4_SELECTION_SHA,
                      ROUND5_RUNNER: ROUND5_RUNNER_SHA, ROUND5_SELECTION: ROUND5_SELECTION_SHA,
                      ROUND6_RUNNER: ROUND6_RUNNER_SHA, ROUND6_SELECTION: ROUND6_SELECTION_SHA,
                      ROUND7_RUNNER: ROUND7_RUNNER_SHA, ROUND7_SELECTION: ROUND7_SELECTION_SHA,
                      ROUND8_RUNNER: ROUND8_RUNNER_SHA, ROUND8_SELECTION: ROUND8_SELECTION_SHA,
                      ROUND9_RUNNER: ROUND9_RUNNER_SHA, ROUND9_SELECTION: ROUND9_SELECTION_SHA,
                      ROUND10_RUNNER: ROUND10_RUNNER_SHA, ROUND10_SELECTION: ROUND10_SELECTION_SHA}
    for path, expected in prior_controls.items():
        require(sha(ROOT / path) == expected and hashlib.sha256(published(path)).hexdigest() == expected,
                'Original helper/prior-round control changed: ' + path)
    round4_runner = types.ModuleType('p25_round4_helpers')
    round4_runner.__file__ = str(ROOT / ROUND4_RUNNER)
    exec(compile((ROOT / ROUND4_RUNNER).read_bytes(), str(ROOT / ROUND4_RUNNER), 'exec'), round4_runner.__dict__)
    round5_runner = types.ModuleType('p25_round5_helpers')
    round5_runner.__file__ = str(ROOT / ROUND5_RUNNER)
    exec(compile((ROOT / ROUND5_RUNNER).read_bytes(), str(ROOT / ROUND5_RUNNER), 'exec'), round5_runner.__dict__)
    round6_runner = types.ModuleType('p25_round6_helpers')
    round6_runner.__file__ = str(ROOT / ROUND6_RUNNER)
    exec(compile((ROOT / ROUND6_RUNNER).read_bytes(), str(ROOT / ROUND6_RUNNER), 'exec'), round6_runner.__dict__)
    round7_runner = types.ModuleType('p25_round7_helpers')
    round7_runner.__file__ = str(ROOT / ROUND7_RUNNER)
    exec(compile((ROOT / ROUND7_RUNNER).read_bytes(), str(ROOT / ROUND7_RUNNER), 'exec'), round7_runner.__dict__)
    round8_runner = types.ModuleType('p25_round8_helpers')
    round8_runner.__file__ = str(ROOT / ROUND8_RUNNER)
    exec(compile((ROOT / ROUND8_RUNNER).read_bytes(), str(ROOT / ROUND8_RUNNER), 'exec'), round8_runner.__dict__)
    round9_runner = types.ModuleType('p25_round9_helpers')
    round9_runner.__file__ = str(ROOT / ROUND9_RUNNER)
    exec(compile((ROOT / ROUND9_RUNNER).read_bytes(), str(ROOT / ROUND9_RUNNER), 'exec'), round9_runner.__dict__)
    prior_runner = types.ModuleType('p25_round10_helpers')
    prior_runner.__file__ = str(ROOT / ROUND10_RUNNER)
    exec(compile((ROOT / ROUND10_RUNNER).read_bytes(), str(ROOT / ROUND10_RUNNER), 'exec'), prior_runner.__dict__)
    require(prior_runner.ROOT == round9_runner.ROOT == round8_runner.ROOT == round7_runner.ROOT == round6_runner.ROOT == round5_runner.ROOT == round4_runner.ROOT == ROOT,
            'Prior runner root differs')
    round4_selection = json.loads((ROOT / ROUND4_SELECTION).read_bytes())
    round5_selection = json.loads((ROOT / ROUND5_SELECTION).read_bytes())
    round6_selection = json.loads((ROOT / ROUND6_SELECTION).read_bytes())
    round7_selection = json.loads((ROOT / ROUND7_SELECTION).read_bytes())
    round8_selection = json.loads((ROOT / ROUND8_SELECTION).read_bytes())
    round9_selection = json.loads((ROOT / ROUND9_SELECTION).read_bytes())
    prior_selection_raw = (ROOT / ROUND10_SELECTION).read_bytes()
    prior_selection = json.loads(prior_selection_raw)
    original = types.ModuleType('p25_round2_helpers')
    original.__file__ = str(ROOT / HELPER)
    exec(compile((ROOT / HELPER).read_bytes(), str(ROOT / HELPER), 'exec'), original.__dict__)
    require(original.ROOT == ROOT, 'Original helper root differs')
    for path, expected in original.PINS.items():
        require(sha(ROOT / path) == expected and hashlib.sha256(published(path)).hexdigest() == expected,
                'Original gate/table pin differs: ' + path)
    raw_selection = published(PACKAGE + '/SOURCE_SELECTION.json')
    require(hashlib.sha256(raw_selection).hexdigest() == args.selection_sha256, 'Source selection review pin differs')
    selection = json.loads(raw_selection)
    base_graph = json.loads((ROOT / ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    target_document = json.loads((ROOT / ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_text())
    round4_graph, _ = round4_runner.validated_graph(base_graph, target_document, round4_selection)
    round5_graph, _ = round5_runner.validated_graph(round4_graph, target_document, round5_selection)
    round6_graph, _ = round6_runner.validated_graph(round5_graph, target_document, round6_selection)
    round7_graph, _ = round7_runner.validated_graph(round6_graph, target_document, round7_selection)
    round8_graph, _ = round8_runner.validated_graph(round7_graph, target_document, round8_selection)
    round9_graph, _ = round9_runner.validated_graph(round8_graph, target_document, round9_selection)
    graph, _ = prior_runner.validated_graph(round9_graph, target_document, prior_selection)
    require(json.loads((ROOT / PRIOR_OUT / 'SOURCE_CLOSURE.json').read_text()) == graph,
            'Saved round-10 graph differs from the reconstructed round-4 through round-10 postimages')
    require(json.loads((ROOT / PRIOR_OUT / 'AUDIT_TARGETS.json').read_text()) == target_document
            and (ROOT / PRIOR_OUT / 'SOURCE_SELECTION.json').read_bytes() == prior_selection_raw,
            'Saved round-10 target/selection provenance differs')
    updated, ordered = validated_graph(graph, target_document, selection)
    targets = target_document['modules']
    for row in selection['changed_modules']:
        require(published(row['source']) == published(PACKAGE + '/after/' + row['source']),
                'Published production source differs from its reviewed candidate: ' + row['module'])
        require(hashlib.sha256(published(PACKAGE + '/after/' + row['source'])).hexdigest()
                == row['after_sha256'], 'Published candidate bytes differ: ' + row['module'])
    sys.path.insert(0, str(ROOT / 'verification/part2'))
    from inspect_winner9_owner_native import imports
    from winner9_external_snapshot import ExternalSnapshot
    verify_sources(ROOT, graph, imports)
    prior_result_path = ROOT / PRIOR_OUT / 'RUN_RESULT.json'
    require(sha(prior_result_path) == PRIOR_RESULT_SHA, 'Original completed round-10 result differs')
    prior_raw = prior_result_path.read_bytes()
    previous = json.loads(prior_raw)
    validate_previous_result(previous, graph['roots'], targets, prior_selection)
    require(json.loads((ROOT / PRIOR_SUMMARY).read_text()) == previous['audit_summary'], 'Original audit summary differs')
    for filename, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256'),
                          ('EXECUTED_RUNNER.py', 'runner_sha256')]:
        require(sha(ROOT / PRIOR_OUT / filename) == previous[key], 'Original round-10 evidence differs: ' + filename)
    direct_failures = validate_repair_failures(selection, previous['compile_summary'],
                                               (ROOT / PRIOR_OUT / 'COMPILE.log').read_text())
    require(direct_failures == selection['round10_direct_normal_failures'],
            'Selected direct-failure provenance differs from the original round-10 compile log')
    original.baseline_checks()
    external = ExternalSnapshot(original.SNAPSHOT, lean=original.LEAN, mathlib_pin=original.MATHLIB_COMMIT,
                                project_lib=ROOT / '.lake/p2-private/lib')
    external_before = external.verify()
    require(external_before == previous['external_after'], 'Qualified external environment changed after round 10')
    validate_reuse(graph, previous, selection, external, original)
    require(shutil.disk_usage(ROOT).free >= MIN_FREE_BYTES, 'Original disk minimum not met before archiving')
    out = ROOT / NEW_OUT
    summary = ROOT / '.lake/p2-private/audit' / SUMMARY_NAME
    require(not out.exists() and not out.is_symlink() and not summary.exists()
            and not summary.is_symlink(), 'Preserve existing round-11 output')

    def historical_files():
        result = {PRIOR_SUMMARY: sha(ROOT / PRIOR_SUMMARY)}
        for number in range(1, 11):
            folder = ROOT / f'.lake/p25-followup-repairs-attempt{number:03d}'
            require(folder.is_dir(), 'Missing prior attempt: ' + str(folder))
            result.update({str(path.relative_to(ROOT)): sha(path) for path in sorted(folder.rglob('*')) if path.is_file()})
        return result

    history_before = historical_files()
    records_path = ROOT / '.lake/p2-private/records.json'
    records_raw = records_path.read_bytes()
    json.loads(records_raw)
    records_sha = hashlib.sha256(records_raw).hexdigest()
    out.mkdir(parents=True, exist_ok=False)
    (out / 'previous-records.json.gz').write_bytes(gzip.compress(records_raw, mtime=0))
    (out / 'PRIOR_RUN_RESULT.json').write_bytes(prior_raw)
    shutil.copyfile(ROOT / PRIOR_SUMMARY, out / 'PRIOR_AUDIT_SUMMARY.json')
    shutil.copyfile(__file__, out / 'EXECUTED_RUNNER.py')
    save_json(out / 'PRESERVED_HISTORY.json', history_before)
    save_json(out / 'SOURCE_CLOSURE.json', updated)
    save_json(out / 'AUDIT_TARGETS.json', target_document)
    (out / 'SOURCE_SELECTION.json').write_bytes(raw_selection)
    receipt_archive = out / 'prior-audit-latest'
    receipt_archive.mkdir()
    for target in targets:
        source = ROOT / '.lake/p2-private/audit' / target / 'latest.json'
        receipt = json.loads(source.read_text())
        require(receipt['module'] == target and receipt.get('accepted') is previous['audit_summary']['modules'][target]['accepted'],
                'Prior latest audit receipt differs: ' + target)
        shutil.copyfile(source, receipt_archive / (target + '.json'))
    origin = {'source_commit': PREVIOUS, 'records_sha256': records_sha, 'records_bytes': len(records_raw),
              'records_gzip_sha256': sha(out / 'previous-records.json.gz'), 'normal_successful': PRIOR_NORMAL_SUCCESSFUL,
              'owned_accepted': PRIOR_OWNED_ACCEPTED, 'owned_requested': 69, 'prior_result_sha256': PRIOR_RESULT_SHA,
              'prior_source_closure_sha256': sha(ROOT / PRIOR_OUT / 'SOURCE_CLOSURE.json'),
              'per_record_historical_provenance_preserved': True, 'historical_objects_imported': False,
              'reuse_decided_by_unchanged_source_dependency_environment_qualified_drivers': True}
    save_json(out / 'CACHE_ORIGIN.json', origin)
    archived = {str(path.relative_to(out)): sha(path) for path in out.rglob('*') if path.is_file()}
    state = {'schema': 'p25-round11-reused-drivers-v1', 'source_commit': args.publication_commit,
             'previous_commit': PREVIOUS, 'runner_sha256': args.runner_sha256, 'source_selection_sha256': args.selection_sha256,
             'started_utc': now(), 'project_modules': 377, 'owned_targets': 69, 'compile_roots': graph['roots'],
             'changed_sources': selection['changed_modules'], 'changed_owned_targets': selection['changed_audit_targets'],
             'changed_dependency_only_modules': selection['changed_dependency_only_modules'],
             'source_and_gate_pins': original.PINS, 'prior_control_pins': prior_controls,
             'cache_origin': origin, 'external_before': external_before,
             'minimum_free_bytes': MIN_FREE_BYTES, 'accepted': False, 'finite_guard_credit': False, 'P2_5_proved': False}

    def save():
        save_json(out / 'RUN_RESULT.json', state)

    def history_preserved():
        return historical_files() == history_before and all(sha(out / path) == expected for path, expected in archived.items())

    try:
        save()
        require(sha(records_path) == records_sha and history_preserved(), 'Historical input changed before checkout')
        subprocess.check_call(['git', 'checkout', '--detach', args.publication_commit], cwd=ROOT)
        verify_sources(ROOT, updated, imports)
        require(all(sha(ROOT / path) == expected for path, expected in {**original.PINS, **prior_controls}.items()), 'Original gate/control changed after checkout')
        require(sha(ROOT / RUNNER) == args.runner_sha256
                and sha(ROOT / PACKAGE / 'SOURCE_SELECTION.json') == args.selection_sha256, 'Published round-11 controls differ')
        original.baseline_checks()
        require(external.verify() == external_before, 'External environment changed during checkout')
        state['source_tree'] = output(['git', 'rev-parse', 'HEAD^{tree}'])
        state['disk_free_start'] = shutil.disk_usage(ROOT).free
        save()
        require(state['disk_free_start'] >= MIN_FREE_BYTES, 'Original 1 GiB disk minimum not met; no Lean stage started')
        command = [sys.executable, str(ROOT / original.OLD / 'prepare-q96-original-inputs.py')]
        state['input_preparation_exit'] = original.logged_call(command, out / 'INPUT_PREPARATION.log')
        save()
        require(state['input_preparation_exit'] == 0, 'Original input preparation failed')
        require(sha(records_path) == records_sha and history_preserved(), 'Historical inputs changed before compilation')
        verify_sources(ROOT, updated, imports)
        command = [sys.executable, 'verification/part2/run_winner9_private_checks.py', *graph['roots'],
                   '--baseline-root', str(original.BASELINE), '--workers', '1', '--threads', '1', '--memory-mb', '11264',
                   '--external-snapshot', str(original.SNAPSHOT), '--time-budget-seconds', '1400']
        state['compile_command'] = command
        save()
        state['compile_exit'] = original.logged_call(command, out / 'COMPILE.log')
        state['compile_summary'] = original.compile_summary(out / 'COMPILE.log')
        state['compile_log_sha256'] = sha(out / 'COMPILE.log')
        state['prior_normal_reuse_after_matches'], state['normal_reuse_evidence'] = normal_reuse_postflight(
            graph['modules'], previous['compile_summary']['failed_or_blocked'], json.loads(records_raw),
            json.loads(records_path.read_bytes()), state['compile_summary'], (out / 'COMPILE.log').read_text())
        save()
        original.baseline_checks()
        require(external.verify() == external_before, 'External environment changed after compilation')
        command = [sys.executable, 'verification/part2/run_winner9_private_audit.py', *ordered,
                   '--summary-name', SUMMARY_NAME, '--memory-mb', '11264', '--external-snapshot', str(original.SNAPSHOT)]
        state['audit_command'] = command
        save()
        state['audit_exit'] = original.logged_call(command, out / 'AUDIT.log')
        state['audit_summary'] = json.loads(summary.read_text()) if summary.is_file() else None
        state['audit_log_sha256'] = sha(out / 'AUDIT.log')
        state['prior_owned_reuse_after_matches'], state['owned_reuse_evidence'] = owned_reuse_postflight(
            previous['audit_summary']['modules'], state['audit_summary'], (out / 'AUDIT.log').read_text())
        save()
        verify_sources(ROOT, updated, imports)
        state['source_after_matches'] = True
        state['gate_after_matches'] = all(sha(ROOT / path) == expected for path, expected in {**original.PINS, **prior_controls}.items())
        state['runner_after_matches'] = sha(__file__) == sha(ROOT / RUNNER) == args.runner_sha256
        state['external_after'] = external.verify()
        state['external_after_matches'] = state['external_after'] == external_before
        state['head_after_matches'] = output(['git', 'rev-parse', 'HEAD']) == args.publication_commit and not output(['git', 'status', '--porcelain', '--untracked-files=no'])
        state['history_after_matches'] = history_preserved()
        original.baseline_checks()
        state['baseline_after_matches'] = True
        checks = ['source_after_matches', 'gate_after_matches', 'runner_after_matches', 'external_after_matches',
                  'head_after_matches', 'history_after_matches', 'baseline_after_matches',
                  'prior_normal_reuse_after_matches', 'prior_owned_reuse_after_matches']
        state['accepted'] = original.accepted_summaries(state['compile_exit'], state['audit_exit'], state['compile_summary'],
            state['audit_summary'], graph['roots'], targets) and all(state[key] for key in checks)
        state.update(ended_utc=now(), disk_free_end=shutil.disk_usage(ROOT).free)
        save()
        print('P25_ROUND11_RESULT ' + json.dumps(state), flush=True)
        return 0 if state['accepted'] else 1
    except Exception as error:
        state.update(accepted=False, error=str(error), traceback=traceback.format_exc(), ended_utc=now(),
                     disk_free_end=shutil.disk_usage(ROOT).free)
        save()
        print('P25_ROUND11_FAILED ' + json.dumps(state), flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
