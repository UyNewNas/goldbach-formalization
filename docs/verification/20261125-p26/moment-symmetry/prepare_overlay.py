#!/usr/bin/env python3
"""Prepare an isolated symmetry facade and its static provenance; never invoke Lean."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
MOMENTS = Path('/workspace/p26-recovery-candidates/moments')
MATHLIB = Path('/workspace/library-files/p34-proof-work/.lake/packages/mathlib')
BASELINE = Path('/workspace/scratch/8c9d3a651a4e/goldbach/docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean')
NS = 'ImbalancedChen.P2OriginalSaving19HigherMoments'
OLD_FACADE_SHA = '910de365b810a41d17f7781856e384512cb0080d5051c6be7045643f0004b3b1'
CORE_SHA = '3738b75a69892c1f9ab68a395b6394817e24a94083ca5254b38c32d73a859832'
SYMMETRY_SHA = '5425985922dae867d1a1be2903c2def751187894373d700ca3a8a62b3346e16d'

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

# This script does not render or rewrite any of the three pilot owners.
# In particular, retain the explicit final rfl diagnosed in duplicateH_perm.
symmetry_path = HERE / 'ImbalancedChen/P2OriginalSaving19HigherMomentsSymmetry.lean'
assert sha(symmetry_path.read_bytes()) == SYMMETRY_SHA, 'review changed symmetry source before updating the optional overlay'

# Reuse the existing declaration/header checker without running its main routine.
checker_path = MOMENTS / 'generate_saving19_higher_partition.py'
checker = {'__name__': 'partition_static_checker', '__file__': str(checker_path)}
exec(compile(checker_path.read_text(), str(checker_path), 'exec'), checker)
declarations, header, mask_comments = (checker[n] for n in ['declarations', 'header', 'mask_comments'])

facade_path = MOMENTS / 'ImbalancedChen/P2OriginalSaving19HigherMoments.lean'
old = facade_path.read_bytes()
assert sha(old) == OLD_FACADE_SHA
old_text = old.decode()
before = declarations(old_text)
guard = before['integratedPower_newton_guard']
replacement = (header(guard) + ' := by\n'
               '  exact integratedPower_newton_guard_via_index_zero y i k hk')
new = old_text.replace(guard['text'], replacement, 1)
lines = []
inserted = False
for line in new.splitlines(keepends=True):
    if line.startswith('import ' + NS + 'Guard'):
        if not inserted:
            lines.append('import ' + NS + 'GuardBySymmetry\n')
            inserted = True
        continue
    lines.append(line)
new = ''.join(lines)
assert inserted
after = declarations(new)
assert set(before) == set(after) and len(after) == 30
for name in before:
    assert header(before[name]) == header(after[name]), name
    if name != 'integratedPower_newton_guard':
        assert before[name]['text'] == after[name]['text'], name
out_facade = HERE / 'ImbalancedChen/P2OriginalSaving19HigherMoments.lean'
if not out_facade.exists() or out_facade.read_bytes() != new.encode():
    out_facade.write_text(new)

core_path = MOMENTS / 'ImbalancedChen/P2OriginalSaving19HigherMomentsCore.lean'
assert sha(core_path.read_bytes()) == CORE_SHA
core = declarations(core_path.read_text())
original = declarations(BASELINE.read_text())
recovered = {name: after[name] if name in after else core[name] for name in original}
assert len(recovered) == 36
for name in original:
    assert header(original[name]) == header(recovered[name]), name
    if original[name]['kind'] in ['def', 'structure']:
        assert original[name]['text'] == recovered[name]['text'], name

modules = {}
for path in sorted((HERE / 'ImbalancedChen').glob('*.lean')):
    source = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', mask_comments(source)), path
    name = 'ImbalancedChen.' + path.stem
    modules[name] = {'path': str(path), 'sha256': sha(path.read_bytes()),
                     'bytes': path.stat().st_size,
                     'imports': re.findall(r'^import (.+)$', source, re.M),
                     'status': 'SOURCE_CANDIDATE_NO_P1_ACCEPTANCE'}

project_graph = {}
active = []
def visit(module: str) -> None:
    assert module not in active, 'import cycle: ' + module
    if module in project_graph:
        return
    relative = Path(module.replace('.', '/') + '.lean')
    path = HERE / relative
    if not path.exists():
        path = MOMENTS / relative
    assert path.exists(), module
    deps = [m for m in re.findall(r'^import (.+)$', path.read_text(), re.M)
            if m.startswith(NS) or m == 'ImbalancedChen.P2OriginalSaving19MomentFiniteReindex']
    project_graph[module] = deps
    active.append(module)
    for dep in deps:
        visit(dep)
    active.pop()
visit(NS)
assert len(project_graph) == 17

api_paths = {
    'Finset.mem_piAntidiag': 'Mathlib/Algebra/Order/Antidiag/Pi.lean',
    'Finset.sum_bij; Equiv.sum_comp; Equiv.prod_comp':
        'Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean',
    'Equiv.swap_apply_left': 'Mathlib/Logic/Equiv/Basic.lean',
}
diagnostic = Path('/workspace/p26-local-checks/symmetry/FINITE_REINDEX_LOCAL_DIAGNOSTIC.json')
axioms = Path('/workspace/p26-local-checks/symmetry/FINITE_REINDEX_LOCAL_AXIOMS.json')
copied_core = Path('/workspace/p26-local-checks/symmetry/CORE_SHAPES_LOCAL_DIAGNOSTIC.json')
copied_core_result = json.loads(copied_core.read_text())
assert copied_core_result['exit_code'] == 0
assert copied_core_result['candidate_symmetry_source_sha256'] == SYMMETRY_SHA
report = {
    'status': 'STATIC_OVERLAY_CHECKED_NO_P1_ACCEPTANCE',
    'original_public_headers_preserved': 36,
    'original_definitions_and_structure_fields_byte_equal': True,
    'only_changed_existing_facade_proof': 'integratedPower_newton_guard',
    'other_29_facade_declarations_byte_equal': True,
    'baseline_monolith_sha256': sha(BASELINE.read_bytes()),
    'old_facade_sha256': OLD_FACADE_SHA, 'unchanged_core_sha256': CORE_SHA,
    'preserved_symmetry_sha256': SYMMETRY_SHA,
    'three_pilot_sources_regenerated_or_rewritten': False,
    'modules': modules, 'higher_moment_dependency_graph': project_graph,
    'old_partition_modules': 68, 'proposed_partition_modules': 17,
    'diagnostic_pilot_excluded_from_final_closure': NS + 'SymmetryPilot',
    'needed_integrated_zero_index_leaves': [[k, 0] for k in range(7)],
    'retained_low_bundle_extra_leaves': [[0, 1], [1, 1]],
    'same_single_K6I0_work_remains': True,
    'mathlib_pin': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    'api_sources': {names: {'path': str(MATHLIB / path),
                           'sha256': sha((MATHLIB / path).read_bytes())}
                    for names, path in api_paths.items()},
    'local_diagnostic_record': {'path': str(diagnostic), 'sha256': sha(diagnostic.read_bytes())},
    'local_axiom_inspection_record': {'path': str(axioms), 'sha256': sha(axioms.read_bytes())},
    'local_copied_core_diagnostic_record': {'path': str(copied_core), 'sha256': sha(copied_core.read_bytes())},
    'local_finite_reindex_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'local_diagnostic_scope': 'Finite reindex plus exact copied duplicateH definition/proof and Core factored RHS. Actual production Core-importing wrapper, pilot, facade and P1 acceptance are not claimed.',
    'parent_compile_suggestion': [
        'FiniteReindex -> Symmetry -> SymmetryPilot, retaining accepted Core and LowBoundary.',
        'Retain or obtain K3I0, K4I0, K5I0, K6I0 and unchanged AuthorK0..K6 receipts.',
        'Then GuardBySymmetry -> facade; audit every source owner in the new dependency closure.'],
    'classification': 'Finite expression reindexing; manuscript moment identity unchanged; no new estimate or final-conclusion assumption.',
    'compiled_by_this_preparation_script': False,
    'production_or_existing_moment_sources_modified': False,
}
(HERE / 'SYMMETRY_STATIC_MANIFEST.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'candidate_lean_files': len(modules),
                  'proposed_partition_modules': len(project_graph),
                  'public_headers_preserved': len(recovered)}, indent=2))
