#!/usr/bin/env python3
"""Validate the 23 retained P1.5 owner audits against the installed source commit."""
import argparse
import json
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import run_selected as runner


def audit_paths(roots, owner):
    return sorted(path for root in roots
                  for path in (root / owner / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))


def validate(s, result_path, owner, graph, sources):
    audit = result_path.parent.parent
    owner_dir = audit.parent.parent
    original = owner_dir.parent.name
    normal_path = owner_dir / 'normal' / owner / 'NORMAL_PASS.json'
    plan_path = audit / 'AUDIT_PLAN.json'
    paths = {'normal': normal_path, 'audit_plan': plan_path, 'audit_result': result_path}
    fingerprints = {name: s.d.fingerprint(path) for name, path in paths.items()}
    normal = s.api.read_json(normal_path)
    result = s.api.read_json(result_path)
    # audit_valid calls normal_valid with a fresh context for the installed closure.
    owners = s.api.audit_valid(original, runner.PROJECT, audit, s.api.read_json(plan_path),
                               {owner: normal}, graph, sources, s.h, s.d)
    runner.require(owners == {owner}, 'retained audit owner differs')
    runner.require(fingerprints == {k: s.d.fingerprint(p) for k, p in paths.items()},
                   'receipt changed during validation')
    record = {'original_source_commit': original, 'source_sha256': sources[owner],
            'receipts': {k: {'path': str(p), **fingerprints[k]} for k, p in paths.items()},
            'total_owned_exports': result['total_owned_exports'],
            'total_public_exports': result['total_public_exports']}
    files = {**normal['dependency_context']['dependency_objects_and_traces'],
             **normal['source_plus_five_outputs']}
    return record, files


def candidates():
    roots = sorted(p for p in runner.ROOT.iterdir() if re.fullmatch('[0-9a-f]{40}', p.name)
                   and p.is_dir() and not p.is_symlink())
    return {owner: audit_paths(roots, owner) for owner in runner.TARGETS}


def review(s, commit):
    before_git = s.d.original_git_state(runner.REPO)
    config, graph, sources, before, order = runner.preflight(s, commit, list(runner.TARGETS))
    runner.require(len(order) == len(set(order)) == 23, 'expected exactly 23 different owners')
    receipts = candidates()
    owners, failures, rejected, verified_files = {}, {}, {}, {}
    changed_files = set()
    for module in order:
        matches = []
        for path in receipts[module]:
            try:
                matches.append(validate(s, path, module, graph, sources))
            except (OSError, ValueError, RuntimeError, KeyError, TypeError, AssertionError) as error:
                rejected[str(path)] = str(error) or type(error).__name__
        if len(matches) == 1:
            owners[module], files = matches[0]
            for path, binding in files.items():
                if verified_files.setdefault(path, binding) != binding:
                    changed_files.add(path)
        else:
            failures[module] = {'valid_audit_count': len(matches),
                                'candidates': [str(p) for p in receipts[module]]}
    for path, expected in verified_files.items():
        try:
            if s.d.fingerprint(runner.PROJECT / path) != expected:
                changed_files.add(path)
        except OSError:
            changed_files.add(path)
    changed_receipts = set()
    for owner in owners.values():
        for receipt in owner['receipts'].values():
            path = Path(receipt['path'])
            expected = {k: receipt[k] for k in ('bytes', 'sha256')}
            try:
                if path.is_symlink() or s.d.fingerprint(path) != expected:
                    changed_receipts.add(str(path))
            except OSError:
                changed_receipts.add(str(path))
    after = runner.snapshot(s, graph, config)
    after_git = s.d.original_git_state(runner.REPO)
    stable = (before == after and before_git == after_git and receipts == candidates()
              and not changed_files and not changed_receipts)
    return {'schema': 'p15_retained_actual_means_review_v1', 'current_source_commit': commit,
            'context_before': before, 'context_after': after, 'git_before': before_git,
            'git_after': after_git, 'context_and_inventory_stable': stable,
            'unique_verified_files_rechecked': len(verified_files), 'changed_files': sorted(changed_files),
            'changed_receipts': sorted(changed_receipts),
            'owners': owners, 'failures': failures, 'rejected_candidates': rejected,
            'all_23_accepted': len(owners) == 23 and not failures and stable,
            'whole_P1_complete': False, 'compilation_performed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    runner.require(re.fullmatch('[0-9a-f]{40}', args.source_commit), 'full source commit required')
    output = args.output.resolve()
    runner.require(not args.output.is_symlink() and output.suffix == '.json', 'expected JSON output file')
    for protected in (runner.REPO, runner.PROJECT):
        runner.require(not output.is_relative_to(protected.resolve()), 'output inside protected project')
    if output.is_relative_to(runner.ROOT):
        relative = output.relative_to(runner.ROOT)
        runner.require(relative.parts and not re.fullmatch('[0-9a-f]{40}', relative.parts[0])
                       and relative.parts[0] != 'source-installs', 'output inside retained evidence')
    s = runner.helpers()
    report = review(s, args.source_commit)
    s.d.save(output, report)
    print(json.dumps({'output': str(output), 'sha256': s.d.fingerprint(output)['sha256'],
                      'accepted_owner_count': len(report['owners']),
                      'all_23_accepted': report['all_23_accepted']}))
    return int(not report['all_23_accepted'])


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
