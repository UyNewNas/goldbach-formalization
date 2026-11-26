#!/usr/bin/env python3
"""Resume P2's unchanged 377-module / 69-owned gates after six source repairs."""
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
PREVIOUS = '168973571f795dbe8fb1c1bccfd7f7c54899b36a'
PRIOR_RESULT_SHA = 'bf84d4551c73db7ff634c95f797df967815d2e8c5ded65bd5f0b04a756b0c17e'
ROUND2 = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'
HELPER = ROUND2 + '/run_followup_round2.py'
HELPER_SHA = 'bd3a0e94025c837897ec12d9c1350cb6f236c2902c09844517cab7a0a91b3591'
ROUND4_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round4.py'
ROUND4_RUNNER_SHA = '803a84486461cf1b5f775c2b4d6af1a380826680de94648233cfa86e45d89ad3'
ROUND4_SELECTION = 'docs/source-only/20261126-p2-5-round4-repairs/SOURCE_SELECTION.json'
ROUND4_SELECTION_SHA = '196e4617434c4f11daef8f13a1b29cece718125a945805292c1783c9100ee574'
RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round5.py'
PACKAGE = 'docs/source-only/20261126-p2-5-round5-repairs'
SELECTION_SHA = '9bfb235dbd60eae3872b114e9569dfce315cd6dc0f96f4107b7df34ae16d6da5'
PRIOR_OUT = '.lake/p25-followup-repairs-attempt004'
NEW_OUT = '.lake/p25-followup-repairs-attempt005'
PRIOR_SUMMARY = '.lake/p2-private/audit/p25-round4-repairs-owned-audit.json'
SUMMARY_NAME = 'p25-round5-repairs-owned-audit.json'
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
    require(len(rows) == len({row['module'] for row in rows}) == 6, 'Expected exactly six distinct repairs')
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
    require(priority == selection['changed_audit_targets'] and len(priority) == 2
            and len(ordered) == 69 and set(ordered) == set(targets), 'Audit scope/order differs')
    dependency_only = [row['module'] for row in rows if row['module'] not in targets]
    require(dependency_only == selection['changed_dependency_only_modules'] and len(dependency_only) == 4,
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
    require(previous['source_commit'] == PREVIOUS and previous.get('ended_utc'), 'Round 4 is not complete at its recorded origin')
    require(previous['runner_sha256'] == ROUND4_RUNNER_SHA
            and previous['source_selection_sha256'] == ROUND4_SELECTION_SHA
            and previous['changed_sources'] == prior_selection['sources']
            and previous['changed_owned_targets'] == prior_selection['changed_audit_targets']
            and previous['changed_dependency_only_modules'] == prior_selection['changed_dependency_only_modules'],
            'Round-4 source/control provenance differs')
    compiled, audited = previous['compile_summary'], previous['audit_summary']
    require(compiled['roots'] == roots == previous['compile_roots'] and compiled['total'] == 377
            and compiled['successful_closure'] == 330 and compiled['reused'] == 325
            and compiled['pending'] == [] and previous['project_modules'] == 377, 'Round-4 normal result differs')
    require(audited['requested'] == previous['owned_targets'] == 69 and audited['accepted'] == 41
            and set(audited['modules']) == set(targets)
            and sum(row['accepted'] is True for row in audited['modules'].values()) == 41,
            'Round-4 owned result differs')
    require(previous['accepted'] is False and previous['compile_exit'] == previous['audit_exit'] == 1
            and all(previous.get(key) is True for key in ['source_after_matches', 'gate_after_matches',
                'runner_after_matches', 'external_after_matches', 'head_after_matches',
                'history_after_matches', 'baseline_after_matches']), 'Round-4 completed postflight differs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('--runner-sha256', required=True)
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Run without Python -O; original gate assertions must remain enabled')
    require(re.fullmatch(r'[0-9a-f]{40}', args.publication_commit) is not None, 'Expected full publication commit')
    require(re.fullmatch(r'[0-9a-f]{64}', args.runner_sha256) is not None
            and sha(__file__) == args.runner_sha256, 'Runner review pin differs')
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

    require(output(['git', 'rev-parse', 'HEAD']) == PREVIOUS, 'Expected the preserved round-4 checkout')
    require(not output(['git', 'status', '--porcelain', '--untracked-files=no']), 'Tracked worktree is not clean')
    subprocess.check_call(['git', 'merge-base', '--is-ancestor', PREVIOUS, args.publication_commit], cwd=ROOT)
    require(published(RUNNER) == Path(__file__).read_bytes(), 'Published runner differs from reviewed runner')
    prior_controls = {HELPER: HELPER_SHA, ROUND4_RUNNER: ROUND4_RUNNER_SHA,
                      ROUND4_SELECTION: ROUND4_SELECTION_SHA}
    for path, expected in prior_controls.items():
        require(sha(ROOT / path) == expected and hashlib.sha256(published(path)).hexdigest() == expected,
                'Original helper/round-4 control changed: ' + path)
    prior_runner = types.ModuleType('p25_round4_helpers')
    prior_runner.__file__ = str(ROOT / ROUND4_RUNNER)
    exec(compile((ROOT / ROUND4_RUNNER).read_bytes(), str(ROOT / ROUND4_RUNNER), 'exec'), prior_runner.__dict__)
    require(prior_runner.ROOT == ROOT, 'Prior runner root differs')
    prior_selection_raw = (ROOT / ROUND4_SELECTION).read_bytes()
    prior_selection = json.loads(prior_selection_raw)
    original = types.ModuleType('p25_round2_helpers')
    original.__file__ = str(ROOT / HELPER)
    exec(compile((ROOT / HELPER).read_bytes(), str(ROOT / HELPER), 'exec'), original.__dict__)
    require(original.ROOT == ROOT, 'Original helper root differs')
    for path, expected in original.PINS.items():
        require(sha(ROOT / path) == expected and hashlib.sha256(published(path)).hexdigest() == expected,
                'Original gate/table pin differs: ' + path)
    raw_selection = published(PACKAGE + '/SOURCE_SELECTION.json')
    require(hashlib.sha256(raw_selection).hexdigest() == SELECTION_SHA, 'Source selection review pin differs')
    selection = json.loads(raw_selection)
    base_graph = json.loads((ROOT / ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
    target_document = json.loads((ROOT / ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_text())
    graph, _ = prior_runner.validated_graph(base_graph, target_document, prior_selection)
    require(json.loads((ROOT / PRIOR_OUT / 'SOURCE_CLOSURE.json').read_text()) == graph,
            'Saved round-4 graph differs from its eight reviewed postimages')
    require(json.loads((ROOT / PRIOR_OUT / 'AUDIT_TARGETS.json').read_text()) == target_document
            and (ROOT / PRIOR_OUT / 'SOURCE_SELECTION.json').read_bytes() == prior_selection_raw,
            'Saved round-4 target/selection provenance differs')
    updated, ordered = validated_graph(graph, target_document, selection)
    targets = target_document['modules']
    for row in selection['changed_modules']:
        require(hashlib.sha256(published(PACKAGE + '/after/' + row['source'])).hexdigest()
                == row['after_sha256'], 'Published candidate bytes differ: ' + row['module'])
    sys.path.insert(0, str(ROOT / 'verification/part2'))
    from inspect_winner9_owner_native import imports
    from winner9_external_snapshot import ExternalSnapshot
    verify_sources(ROOT, graph, imports)
    prior_result_path = ROOT / PRIOR_OUT / 'RUN_RESULT.json'
    require(sha(prior_result_path) == PRIOR_RESULT_SHA, 'Original completed round-4 result differs')
    prior_raw = prior_result_path.read_bytes()
    previous = json.loads(prior_raw)
    validate_previous_result(previous, graph['roots'], targets, prior_selection)
    require(json.loads((ROOT / PRIOR_SUMMARY).read_text()) == previous['audit_summary'], 'Original audit summary differs')
    for filename, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256'),
                          ('EXECUTED_RUNNER.py', 'runner_sha256')]:
        require(sha(ROOT / PRIOR_OUT / filename) == previous[key], 'Original round-4 evidence differs: ' + filename)
    original.baseline_checks()
    external = ExternalSnapshot(original.SNAPSHOT, lean=original.LEAN, mathlib_pin=original.MATHLIB_COMMIT,
                                project_lib=ROOT / '.lake/p2-private/lib')
    external_before = external.verify()
    require(external_before == previous['external_after'], 'Qualified external environment changed after round 4')
    out = ROOT / NEW_OUT
    summary = ROOT / '.lake/p2-private/audit' / SUMMARY_NAME
    require(not out.exists() and not out.is_symlink() and not summary.exists()
            and not summary.is_symlink(), 'Preserve existing round-5 output')

    def historical_files():
        result = {PRIOR_SUMMARY: sha(ROOT / PRIOR_SUMMARY)}
        for number in (1, 2, 3, 4):
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
              'records_gzip_sha256': sha(out / 'previous-records.json.gz'), 'normal_successful': 330,
              'owned_accepted': 41, 'owned_requested': 69, 'prior_result_sha256': PRIOR_RESULT_SHA,
              'prior_source_closure_sha256': sha(ROOT / PRIOR_OUT / 'SOURCE_CLOSURE.json'),
              'per_record_historical_provenance_preserved': True, 'historical_objects_imported': False,
              'reuse_decided_by_unchanged_source_dependency_environment_qualified_drivers': True}
    save_json(out / 'CACHE_ORIGIN.json', origin)
    archived = {str(path.relative_to(out)): sha(path) for path in out.rglob('*') if path.is_file()}
    state = {'schema': 'p25-round5-reused-drivers-v1', 'source_commit': args.publication_commit,
             'previous_commit': PREVIOUS, 'runner_sha256': args.runner_sha256, 'source_selection_sha256': SELECTION_SHA,
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
                and sha(ROOT / PACKAGE / 'SOURCE_SELECTION.json') == SELECTION_SHA, 'Published round-5 controls differ')
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
                  'head_after_matches', 'history_after_matches', 'baseline_after_matches']
        state['accepted'] = original.accepted_summaries(state['compile_exit'], state['audit_exit'], state['compile_summary'],
            state['audit_summary'], graph['roots'], targets) and all(state[key] for key in checks)
        state.update(ended_utc=now(), disk_free_end=shutil.disk_usage(ROOT).free)
        save()
        print('P25_ROUND5_RESULT ' + json.dumps(state), flush=True)
        return 0 if state['accepted'] else 1
    except Exception as error:
        state.update(accepted=False, error=str(error), traceback=traceback.format_exc(), ended_utc=now(),
                     disk_free_end=shutil.disk_usage(ROOT).free)
        save()
        print('P25_ROUND5_FAILED ' + json.dumps(state), flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
