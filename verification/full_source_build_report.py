#!/usr/bin/env python3
"""Record exhaustive source-target outcomes without promoting partial builds."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def validate_selected_targets(targets, selected):
    if not isinstance(targets, list) or not targets or any(not isinstance(m, str) or not m for m in targets):
        raise ValueError('Inventory targets must be a nonempty list of module names')
    if len(targets) != len(set(targets)):
        raise ValueError('Inventory contains duplicate targets')
    if selected is None:
        return list(targets)
    if not isinstance(selected, list) or not selected:
        raise ValueError('Selected targets must be a nonempty list')
    if any(not isinstance(m, str) or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", m) is None for m in selected):
        raise ValueError('Malformed selected module name')
    if len(selected) != len(set(selected)):
        raise ValueError('Selected targets contain duplicates')
    unknown = set(selected) - set(targets)
    if unknown:
        raise ValueError(f'Unknown selected targets: {sorted(unknown)}')
    return list(selected)


def classify(targets, log, exit_code, existing=(), selected=None):
    selected = set(validate_selected_targets(targets, selected))
    passed = set(re.findall(r'^[✔⚠ℹ] \[\d+/\d+\] (?:Built|Replayed) ([\w.]+)(?:\s|$)', log, re.M))
    failed = set(re.findall(r'^✖ \[\d+/\d+\] Building ([\w.]+)(?:\s|$)', log, re.M))
    existing = set(existing)
    return {module: ('outside_this_build_shard' if module not in selected else
                     'build_passed_or_validated_cache' if exit_code == 0 else
                     'compile_failed' if module in failed else
                     'compiled_or_replayed_successfully' if module in passed else
                     'unconfirmed_existing_object' if module in existing else
                     'not_completed_or_dependency_blocked') for module in targets}


def make_report(inventory, raw_log, exit_code, existing=(), selected=None):
    targets = inventory['targets']
    selected = validate_selected_targets(targets, selected)
    outcomes = classify(targets, raw_log.decode(errors='replace'), exit_code, existing, selected)
    rows = []
    for row in inventory['files']:
        row = dict(row)
        module = row.get('module')
        row['build_status'] = outcomes[module] if module else 'not_a_production_build_target'
        rows.append(row)
    full_scope = set(selected) == set(targets)
    return {'schema': 1, 'head': inventory['head'], 'exit_code': exit_code,
            'all_production_targets_passed': exit_code == 0 and full_scope,
            'all_requested_targets_passed': exit_code == 0,
            'full_production_scope_requested': full_scope,
            'requested_target_count': len(selected), 'requested_targets': selected,
            'claim': 'Compilation only. This report is not complete kernel replay or axiom-audit acceptance.',
            'log_sha256': hashlib.sha256(raw_log).hexdigest(),
            'counts': dict(Counter(outcomes.values())), 'targets': outcomes, 'files': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--exit-code', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--targets-file', type=Path, help='Optional nonempty unique selected module subset, one name per line')
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    root = Path(__file__).resolve().parents[1]
    targets = inventory['targets']
    try:
        selected = args.targets_file.read_text().splitlines() if args.targets_file else None
        selected = validate_selected_targets(targets, selected)
        existing = [module for module in selected if (root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')).is_file()]
        raw_log = args.log.read_bytes()
        result = make_report(inventory, raw_log, args.exit_code, existing, selected)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'exit_code': args.exit_code, 'counts': result['counts']}))


if __name__ == '__main__':
    main()
