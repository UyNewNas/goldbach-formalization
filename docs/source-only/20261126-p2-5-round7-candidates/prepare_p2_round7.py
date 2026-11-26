#!/usr/bin/env python3
"""Bind four completed local candidates to the preserved round-6 receipt.

This prepares metadata only. It never installs production Lean sources, invokes
Lean, changes Git state, or contacts the compilation environment.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import posixpath
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
PACKAGE = Path(__file__).resolve().parent
RESUMED = ROOT / 'docs/verification/20261126-p2-5-resumed'
RECEIPT = RESUMED / 'p2-round6-attempt006/PRINTED_RUN_RESULT.json'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_module(path, name, expected=None):
    raw = path.read_bytes()
    require(expected is None or digest(raw) == expected, 'Pinned control differs: ' + str(path))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def context():
    runner = read_module(RESUMED / 'run_p2_round7.py', 'p25_round7_prepare')
    prior4 = read_module(ROOT / runner.ROUND4_RUNNER, 'p25_round4_prepare', runner.ROUND4_RUNNER_SHA)
    prior5 = read_module(ROOT / runner.ROUND5_RUNNER, 'p25_round5_prepare', runner.ROUND5_RUNNER_SHA)
    prior6 = read_module(ROOT / runner.ROUND6_RUNNER, 'p25_round6_prepare', runner.ROUND6_RUNNER_SHA)
    helper = read_module(ROOT / runner.HELPER, 'p25_round2_prepare', runner.HELPER_SHA)
    for path, expected in helper.PINS.items():
        require(digest((ROOT / path).read_bytes()) == expected, 'Original source/gate pin differs: ' + path)
    raw4 = (ROOT / runner.ROUND4_SELECTION).read_bytes()
    raw5 = (ROOT / runner.ROUND5_SELECTION).read_bytes()
    raw6 = (ROOT / runner.ROUND6_SELECTION).read_bytes()
    require(digest(raw4) == runner.ROUND4_SELECTION_SHA, 'Round-4 selection differs')
    require(digest(raw5) == runner.ROUND5_SELECTION_SHA, 'Round-5 selection differs')
    require(digest(raw6) == runner.ROUND6_SELECTION_SHA, 'Round-6 selection differs')
    base = json.loads((ROOT / runner.ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_bytes())
    targets = json.loads((ROOT / runner.ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_bytes())
    graph4, _ = prior4.validated_graph(base, targets, json.loads(raw4))
    graph5, _ = prior5.validated_graph(graph4, targets, json.loads(raw5))
    graph6, _ = prior6.validated_graph(graph5, targets, json.loads(raw6))
    raw = RECEIPT.read_bytes()
    require(digest(raw) == runner.PRIOR_RESULT_SHA, 'Actual completed round-6 receipt differs')
    previous = json.loads(raw)
    runner.validate_previous_result(previous, graph6['roots'], targets['modules'], json.loads(raw6))
    return runner, graph6, targets, previous


def committed_bytes(commit, path, visited=()):
    require(path not in visited and not posixpath.isabs(path) and not path.startswith('../'),
            'Invalid committed source link: ' + path)
    env = dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')
    prefix = ['git', '-c', 'protocol.allow=never']
    entry = subprocess.check_output(prefix + ['ls-tree', '-z', commit, '--', path], cwd=ROOT, env=env)
    require(entry.endswith(b'\0') and entry.count(b'\0') == 1, 'Missing unique committed source: ' + path)
    metadata, actual = entry[:-1].split(b'\t', 1)
    mode, kind, oid = metadata.decode().split()
    require(actual.decode() == path and kind == 'blob', 'Expected a committed source blob: ' + path)
    raw = subprocess.check_output(prefix + ['cat-file', 'blob', oid], cwd=ROOT, env=env)
    if mode == '120000':
        target = posixpath.normpath(posixpath.join(posixpath.dirname(path), raw.decode()))
        return committed_bytes(commit, target, (*visited, path))
    return raw


def affected_modules(graph, changed):
    affected = set(changed)
    while True:
        extended = affected | {name for name, row in graph['modules'].items()
                               if set(row['imports']) & affected}
        if extended == affected:
            return sorted(affected)
        affected = extended


def option_commands(tokens):
    """Compare commands after comment removal, excluding surrounding doc whitespace."""
    return [line.strip() for line in re.findall(r'^[ \t]*set_option\b[^\n]*', tokens, re.M)]


def build_selection(runner, graph, targets, previous, package=PACKAGE):
    sys.path.insert(0, str(ROOT / 'verification/part2'))
    from inspect_winner9_owner_native import imports, source_tokens
    rows = []
    for name in runner.EXPECTED_REPAIRS:
        source = name.replace('.', '/') + '.lean'
        before_path, after_path = 'before/' + source, 'after/' + source
        before_file, after_file = package / before_path, package / after_path
        require(before_file.is_file() and after_file.is_file(),
                'Candidate pair is not complete; no selection written: ' + name)
        before, after = before_file.read_bytes(), after_file.read_bytes()
        require(before == committed_bytes(runner.PREVIOUS, source), 'Preimage differs from round-6 commit: ' + name)
        require(digest(before) == graph['modules'][name]['sha256'], 'Preimage differs from round-6 graph: ' + name)
        require(before != after, 'Candidate has no repair: ' + name)
        old_text, new_text = before.decode(), after.decode()
        require(imports(old_text) == imports(new_text), 'Candidate imports changed: ' + name)
        options = lambda value: option_commands(source_tokens(value))
        require(options(old_text) == options(new_text), 'Candidate options changed: ' + name)
        forbidden = re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', source_tokens(new_text))
        require(not forbidden, 'Forbidden proof tokens in candidate: ' + name)
        rows.append({'module': name, 'source': source,
                     'before_path': before_path, 'before_sha256': digest(before), 'before_bytes': len(before),
                     'after_path': after_path, 'after_sha256': digest(after), 'after_bytes': len(after),
                     'before_matches_round6_publication': True,
                     'imports_unchanged': True, 'options_unchanged': True,
                     'added_forbidden_proof_tokens': [], 'current_context_accepted': False})
    changed = [row['module'] for row in rows]
    affected = affected_modules(graph, changed)
    prior_failed = set(previous['compile_summary']['failed_or_blocked'])
    require(set(affected) <= prior_failed, 'A previously successful module would be invalidated')
    audit_targets = targets['modules']
    accepted = [name for name, row in previous['audit_summary']['modules'].items() if row['accepted']]
    require(not set(accepted) & set(affected), 'A previously accepted owned target would be invalidated')
    selection = {
        'schema': 'p25-round7-four-source-selection-v1',
        'status': 'SOURCE_ONLY_EXACT_BYTES_BOUND_PENDING_CURRENT_P2_COMPILATION',
        'round6_publication': runner.PREVIOUS,
        'round6_terminal_result': {'path': str(RECEIPT.relative_to(ROOT)),
                                  'derived_from_complete_task_stdout': True,
                                  'remote_sha_must_match_before_any_new_Lean': True,
                                  'sha256': runner.PRIOR_RESULT_SHA,
                                  'normal_successful': 339, 'normal_reused': 336,
                                  'owned_accepted': 45, 'owned_requested': 69,
                                  'postflights_all_true': True},
        'changed_modules': rows,
        'changed_audit_targets': [name for name in changed if name in audit_targets],
        'changed_dependency_only_modules': [name for name in changed if name not in audit_targets],
        'expected_changed_dependency_closure': affected,
        'previously_successful_modules_invalidated': [],
        'previously_accepted_owned_targets_invalidated': [],
        'qualified_normal_reuse_candidates': 339,
        'qualified_owned_reuse_candidates': 45,
        'reuse_decided_by_unchanged_source_dependency_environment_qualified_drivers': True,
        'project_module_count': 377, 'owned_target_count': 69,
        'production_installed': False, 'Lean_or_cloud_executions': False,
        'historical_objects_transferred': False, 'new_current_context_formal_credit': False,
        'P2_5_proved': False,
    }
    runner.validated_graph(graph, targets, selection)
    return selection


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Write source selection and run configuration after all four candidates pass')
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Run without Python -O')
    runner, graph, targets, previous = context()
    selection = build_selection(runner, graph, targets, previous)
    selection_raw = encoded(selection)
    runner_sha = digest((ROOT / runner.RUNNER).read_bytes())
    selection_sha = digest(selection_raw)
    config = {
        'schema': 'p25-round7-publication-run-config-v1',
        'cloud_root': str(runner.ROOT), 'required_previous_commit': runner.PREVIOUS,
        'runner_path': runner.RUNNER, 'runner_sha256': runner_sha,
        'selection_path': runner.PACKAGE + '/SOURCE_SELECTION.json', 'selection_sha256': selection_sha,
        'preparer_path': str(Path(__file__).relative_to(ROOT)), 'preparer_sha256': digest(Path(__file__).read_bytes()),
        'runner_arguments': ['<publication_commit>', '--runner-sha256', runner_sha, '--selection-sha256', selection_sha],
        'execution': 'Run an exact published copy of the runner before checkout; the runner installs published bytes by detached checkout after all prior-context gates pass.',
        'output': runner.NEW_OUT, 'audit_summary_name': runner.SUMMARY_NAME,
        'minimum_free_bytes': runner.MIN_FREE_BYTES,
        'project_modules': 377, 'owned_targets': 69,
        'expected_changed_dependency_closure': selection['expected_changed_dependency_closure'],
        'qualified_normal_reuse_candidates': 339, 'qualified_owned_reuse_candidates': 45,
        'cloud_executed': False, 'P2_5_proved': False,
    }
    if args.write:
        (PACKAGE / 'SOURCE_SELECTION.json').write_bytes(selection_raw)
        (PACKAGE / 'RUN_CONFIG.json').write_bytes(encoded(config))
    print(json.dumps({'written': args.write, 'runner_sha256': runner_sha,
                      'selection_sha256': selection_sha,
                      'changed_modules': len(selection['changed_modules']),
                      'affected_modules': len(selection['expected_changed_dependency_closure']),
                      'normal_reuse_candidates': 339, 'owned_reuse_candidates': 45,
                      'owned_targets': 69, 'project_modules': 377}, sort_keys=True))


if __name__ == '__main__':
    main()
