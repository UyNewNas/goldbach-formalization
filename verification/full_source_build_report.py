#!/usr/bin/env python3
"""Record exhaustive source-target outcomes without promoting partial builds."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def classify(targets, log, exit_code, existing=()):
    passed = set(re.findall(r'^[✔⚠] \[\d+/\d+\] (?:Built|Replayed) ([\w.]+)(?:\s|$)', log, re.M))
    failed = set(re.findall(r'^✖ \[\d+/\d+\] Building ([\w.]+)(?:\s|$)', log, re.M))
    existing = set(existing)
    return {module: ('build_passed_or_validated_cache' if exit_code == 0 else
                     'compile_failed' if module in failed else
                     'compiled_successfully' if module in passed else
                     'unconfirmed_existing_object' if module in existing else
                     'not_completed_or_dependency_blocked') for module in targets}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--exit-code', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    inventory = json.loads(args.inventory.read_text())
    root = Path(__file__).resolve().parents[1]
    targets = inventory['targets']
    existing = [module for module in targets if (root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')).is_file()]
    raw_log = args.log.read_bytes()
    outcomes = classify(targets, raw_log.decode(errors='replace'), args.exit_code, existing)
    rows = []
    for row in inventory['files']:
        row = dict(row)
        module = row.get('module')
        row['build_status'] = outcomes[module] if module else 'not_a_production_build_target'
        rows.append(row)
    result = {'schema': 1, 'head': inventory['head'], 'exit_code': args.exit_code,
              'all_production_targets_passed': args.exit_code == 0,
              'claim': 'Compilation only. This report is not complete kernel replay or axiom-audit acceptance.',
              'log_sha256': hashlib.sha256(raw_log).hexdigest(),
              'counts': dict(Counter(outcomes.values())), 'targets': outcomes, 'files': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'exit_code': args.exit_code, 'counts': result['counts']}))


if __name__ == '__main__':
    main()
