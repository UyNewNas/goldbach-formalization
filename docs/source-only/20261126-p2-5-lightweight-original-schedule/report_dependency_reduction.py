#!/usr/bin/env python3
"""Compare existing source-selection graphs with this source-only import cut.

The result is an import-graph comparison, never compilation or acceptance.
Historical graph entries retain their existing selection/transform records.
Only the frozen current 377 map and explicitly listed source-only overlays
replace them. This does not choose arbitrary current production versions.
"""
from pathlib import Path
import copy
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FAMILY = ROOT / 'docs/source-only/20261125-p2-5-fourteen-family'
BASE = FAMILY / 'PREIMAGE_CLOSURE_SELECTION_1688.json'
CURRENT = ROOT / 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental/CONTINUATION_SOURCE_CLOSURE.json'
SCHEDULE = FAMILY / 'SCHEDULE_SOURCE_MAP.json'
P = 'ImbalancedChen.'
sys.path.insert(0, str(ROOT / 'verification/part2'))
from inspect_winner9_owner_native import imports


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def path_text(path):
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def main():
    graph = {row['module']: copy.deepcopy(row) for row in json.loads(BASE.read_text())['modules']}
    overlays = []
    for name, row in json.loads(CURRENT.read_text())['modules'].items():
        graph[name] = {'module': name, 'path': row['source'], 'sha256': row['sha256'],
                       'imports': row['imports'], 'kind': 'current_frozen_377_selection_not_acceptance'}

    def add(path, kind):
        raw = path.read_bytes()
        name = P + path.stem
        row = {'module': name, 'path': path_text(path), 'sha256': sha(raw),
               'imports': imports(raw.decode()), 'kind': kind}
        graph[name] = row
        overlays.append(row)

    for path in sorted((FAMILY / 'owners').glob('*.lean')):
        add(path, 'existing_negative_finite_owner_postimage')
    for row in json.loads(SCHEDULE.read_text())['upstream_sources']:
        path = ROOT / row['path']
        if not path.is_file() and row.get('local_read_path'):
            path = Path(row['local_read_path'])
        if P + path.stem not in graph and path.is_file():
            assert sha(path.read_bytes()) == row['sha256']
            add(path, 'existing_fourteen_schedule_named_upstream')
    add(Path('/workspace/scratch/e5f883a2215a/reference/topic-p2/docs/source-only/20261120-p2-saving16-negative-switch/P2Saving16NegativeCoefficientComparison.lean'),
        'existing_original_negative_comparison_donor_no_new_proof')
    for name in ['P2Saving16FourteenCornerReciprocalResidual', 'P2Saving16R17StrictFourteenCorners']:
        add(FAMILY / 'ImbalancedChen' / (name + '.lean'), 'existing_fourteen_wrapper_source_only')
    for path in sorted((HERE / 'before/ImbalancedChen').glob('*.lean')):
        add(path, 'exact_preimage_of_this_package')
    roots = [P + 'P4AOriginalR17PaidIntegral', P + 'P2Saving16R17StrictFourteenCorners']

    def closure(root):
        seen, missing, stack, cycles = set(), set(), [], []

        def walk(name):
            if not name.startswith(P):
                return
            if name in stack:
                cycles.append(stack[stack.index(name):] + [name])
                return
            if name in seen:
                return
            seen.add(name)
            if name not in graph:
                missing.add(name)
                return
            stack.append(name)
            for dependency in graph[name]['imports']:
                walk(dependency)
            stack.pop()

        walk(root)
        return {'nodes': sorted(seen), 'count_including_unresolved_nodes': len(seen),
                'missing_providers': sorted(missing), 'cycles': cycles}

    before = {root: closure(root) for root in roots}
    before_graph = copy.deepcopy(graph)
    for folder in ['after/ImbalancedChen', 'ImbalancedChen']:
        for path in sorted((HERE / folder).glob('*.lean')):
            add(path, 'new_source_only_mechanical_postimage')
    after = {root: closure(root) for root in roots}
    comparisons = {}
    for root in roots:
        old, new = set(before[root]['nodes']), set(after[root]['nodes'])
        comparisons[root] = {'before': before[root], 'after': after[root],
                             'removed_modules': sorted(old - new), 'removed_count': len(old - new),
                             'added_modules': sorted(new - old), 'added_count': len(new - old),
                             'net_reduction_in_declared_graph': len(old) - len(new),
                             'saving19_or20_modules_after': sorted(n for n in new if re.search('Saving(?:19|20)', n)),
                             'numeric_guard_owners_after': sorted(n for n in new if any(s in n for s in [
                                 'P2OriginalSaving16OwnedIntegral', 'P2OriginalSaving19OwnedSource',
                                 'P2OriginalSaving19OwnedIntegral', 'P2OriginalSaving20FirstFailureIntegral',
                                 'P4AOriginalFull87SavedGain', 'P4AOriginalFull87Saved86']))}
        assert not after[root]['cycles']
    used = set().union(*(set(row['nodes']) for row in after.values()))
    output = {
        'schema': 'p25-ordinary-schedule-source-only-import-reduction-v1',
        'status': 'STATIC_SELECTION_GRAPH_NOT_COMPILED_NOT_INSTALLED_NO_ACCEPTANCE',
        'basis': [{'path': path_text(p), 'sha256': sha(p.read_bytes())} for p in [BASE, CURRENT, SCHEDULE]],
        'selection_rule': __doc__,
        'comparisons': comparisons,
        'after_module_selection': {name: graph[name] for name in sorted(used) if name in graph},
        'baseline_postimages_already_required': [
            'The seven existing docs/source-only/20261125-p2-5-fourteen-family/owners postimages are reused; not regenerated here.',
            'The two original IntegralDefinitions owners still require their existing original-modules-refactor.patch hunks before an actual complete analytic source selection: P4AOriginalFull87EighthKernelControl and P4AOriginalFull87SourcePrimeTests.',
            'Historical source path relocations and published_install_transform entries remain part of their existing exact selection; this report is not a production installation map.',
        ],
        'remaining_distribution_obligation': {
            'source': 'docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/P4AOrderedThirdSameCoefficient.lean',
            'theorem': 'ImbalancedChen.P4AOrderedThirdSameCoefficient.joined_below',
            'current_result': 'The same compiled Q and rho have compiler reserve, density comparison, support, and a RealB majorant whose right side still contains realPhysicalDistributionError b N T Q rho.',
            'missing_quantitative_input': 'A bound for that actual distribution error on the one beta/k/N0 schedule and exact compiled coefficient, sufficient together with the retained ceil(z) and T+1 terms for the target endpoint. The fourteen wrapper identifies the same error with E14 but does not bound it.',
            'introduced_or_assumed_by_this_patch': False,
        },
        'accepted': False, 'P2_5_proved': False, 'lean_executions': [], 'cloud_actions': [],
    }
    path = HERE / 'DEPENDENCY_REDUCTION.json'
    path.write_text(json.dumps(output, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({root: {key: value for key, value in row.items() if key not in ['before', 'after', 'removed_modules']}
                      | {'before_count': row['before']['count_including_unresolved_nodes'],
                         'after_count': row['after']['count_including_unresolved_nodes'],
                         'missing_after': row['after']['missing_providers']} for root, row in comparisons.items()}, indent=2))


if __name__ == '__main__':
    main()
