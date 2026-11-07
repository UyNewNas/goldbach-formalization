"""Ordinary source/hash bookkeeping only. Never invokes Lean, Lake, or a checker."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re
import subprocess

ROOT = Path('/workspace/shared/chen-coordination/p5-buffer-boundary')
OUT = Path('/workspace/shared/chen-coordination/p5-buffer-boundary-evidence/repair-20261015T043000Z')
MODULE = 'ImbalancedChen.CurrentChenUpsilon6LogDomain'
BASELINE = '6d87935429a2b72a32af05bd3ab3a28a8ea50813'
REQUEST = '20261015T043000Z-p5-log-domain-api-repair'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(name, obj):
    (OUT / name).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')


source_path = ROOT / (MODULE.replace('.', '/') + '.lean')
source_bytes = source_path.read_bytes()
source = source_bytes.decode()
closure, frontier, todo = {}, set(), [MODULE]
while todo:
    name = todo.pop()
    if name in closure:
        continue
    path = ROOT / (name.replace('.', '/') + '.lean')
    if not path.exists():
        frontier.add(name)
        continue
    data = path.read_bytes()
    imports = re.findall(r'^import\s+([\w.]+)', data.decode(), re.M)
    closure[name] = {
        'path': str(path.relative_to(ROOT)), 'sha256': sha(data), 'imports': imports
    }
    todo += imports
closure_digest = sha(json.dumps(closure, sort_keys=True, separators=(',', ':')).encode())
save('source-closure.json', {
    'verification': 'SOURCE_ONLY; exact local project sources, not imported-object acceptance',
    'project_source_closure_sha256': closure_digest,
    'project_source_closure': closure,
    'external_module_frontier': sorted(frontier),
    'external_objects': 'Unavailable here; P0 must bind actual pinned object and companion closure.'
})
types = []
pattern = r'(?m)^(?:@\[[^\n]+\]\s*)?(?:(private|protected)\s+)?(def|theorem)\s+([^\s]+)'
for match in re.finditer(pattern, source):
    signature = source[match.start():source.index(':=', match.end())].strip()
    types.append({
        'source_name': match[3], 'visibility': match[1] or 'public',
        'kind': match[2], 'line': source.count('\n', 0, match.start()) + 1,
        'complete_source_type': signature
    })
save('proposed-types.json', {
    'verification': 'SOURCE_ONLY; not elaborated. Generated/private mangled census remains P0 responsibility.',
    'declarations': types
})
pins = {name: sha((ROOT / name).read_bytes())
        for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide)\b', source)
whitespace = [n for n, line in enumerate(source.splitlines(), 1) if line != line.rstrip()]
assert not forbidden, forbidden
assert not whitespace, whitespace
assert Fraction(1, 2) - 2 * Fraction(417, 5000) == Fraction(833, 2500)
assert 0 < Fraction(417, 5000) < Fraction(19, 125) < Fraction(59, 250)
assert not [name for name in frontier if not name.startswith(('Mathlib.', 'Lean.'))]
save('static-checks.json', {
    'level': 'STATIC_SOURCE_ONLY',
    'source_sha256': sha(source_bytes),
    'trailing_whitespace_lines': whitespace,
    'forbidden_token_matches': forbidden,
    'rational_identity': '1/2 - 2*(417/5000) = 833/2500',
    'positive_rectangle': '0 < 417/5000 < 19/125 < 59/250',
    'project_modules': len(closure), 'external_frontier_count': len(frontier),
    'non_Mathlib_Lean_external_frontier': [],
    'source_declarations': len(types),
    'private_source_declarations': sum(t['visibility'] == 'private' for t in types),
    'proof_environment_started': False,
    'warning': 'No elaboration, kernel replay, complete axiom audit, or numeric h248 claim.'
})
(OUT / 'CurrentChenUpsilon6LogDomain.lean').write_bytes(source_bytes)
request = {
    'schema': 'chen-part-verification-request-v1', 'request_id': REQUEST,
    'part': 'p5', 'status': 'REQUESTED', 'state': 'WAITING_FOR_P0',
    'created_at': '2026-10-15T04:30:00Z', 'baseline_commit': BASELINE,
    'candidate_commit': None, 'candidate_branch': 'codex/chen-p5-buffer-boundary',
    'candidate_worktree': str(ROOT), 'module': MODULE,
    'source_path': str(source_path), 'source_sha256': sha(source_bytes),
    'frozen_source_snapshot': str(OUT / 'CurrentChenUpsilon6LogDomain.lean'),
    'source_git_blob': subprocess.check_output(['git', 'hash-object', str(source_path)], text=True).strip(),
    'source_declaration_count': len(types),
    'source_types_not_compiler_confirmed': str(OUT / 'proposed-types.json'),
    'project_source_closure_sha256': closure_digest,
    'project_source_closure_manifest': str(OUT / 'source-closure.json'),
    'external_module_frontier': sorted(frontier), 'pins': pins,
    'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
    'mathlib_pin': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    'goldbach_pin': '09b97db5764ade1246bfb77206baa1b124760958',
    'mathlib_source_API_evidence': str(OUT.parent / 'read-only-source-api.json'),
    'predecessor_acceptance': {
        'module': 'ImbalancedChen.CurrentChenUpsilon6ProductRestriction',
        'source_sha256': closure['ImbalancedChen.CurrentChenUpsilon6ProductRestriction']['sha256'],
        'run_id': 38673452960, 'declarations': 17,
        'receipt': '/workspace/shared/chen-coordination/p0/automation/parts/p0/runs/20261015T025345Z-p5-buffer/acceptance.json'
    },
    'static_checks': str(OUT / 'static-checks.json'),
    'requested_stages': [
        'Strict -t0 -j2 -M4096 warnings-as-errors compilation',
        'Original-object stock kernel replay',
        'Complete defining-module inventory including private/generated declarations; full types and transitive axiom whitelist',
        'Audit-object kernel replay and exact imported-object/companion binding'
    ],
    'verification': {
        'source': 'SOURCE_ONLY', 'compile': 'NOT_RUN', 'kernel_replay': 'NOT_RUN',
        'complete_audit': 'NOT_RUN', 'integration': 'NOT_RUN'
    },
    'execution_policy': {
        'coordinator': 'P0', 'max_heavy_processes_per_host': 1,
        'lean_threads': 2, 'lean_memory_mb': 4096,
        'producer_started_lean_lake_checker_ci': False,
        'producer_commit_or_push': False
    },
    'unpaid_for_candidate': ['P0 elaboration, original-object replay, complete inventory/type/axiom/import-object acceptance'],
    'unpaid_for_actual_hLower': [
        'Actual fixed-eta arithmetic mean on the retained selector',
        'Frozen manuscript h248 improved kernel integrability, exact admitted-domain estimate and numerical certificate',
        'Correct ordered N-to-infinity then eta-to-zero limit assembly for the actual kernel',
        'All required strong causal means and signed negative-row upper bounds',
        'Complete current coefficient ledger, error absorption and common threshold for actual D12'
    ],
    'scope': {
        'density': 'Only 1/(u*t) on the actual fixed positive rectangle',
        'mask': 'E preserved exactly in arithmetic equivalence; no continuous measurability assumption about E',
        'endpoints': '[417/5000,19/125) x [19/125,59/250), product <=833/2500-eta',
        'eta_limit': 'Two-sided eta-to-zero limit of concrete closed boundary-strip mass; no arithmetic N-limit exchanged',
        'currentC': '49044063/25000000, unchanged',
        'D12': 'Unchanged actual repository count', 'h248_replaced': False,
        'hLower_proved': False, 'PNT_supplier_needed_for_new_boundary_step': False
    },
    'next_action': 'P0 verifies the exact frozen new leaf; P5 repairs only concrete diagnostics after this bounded increment.'
}
save('REQUESTED.json', request)
old_source = (OUT.parent / 'CurrentChenUpsilon6LogDomain.lean').read_text()
old_types = []
for match in re.finditer(pattern, old_source):
    old_types.append(old_source[match.start():old_source.index(':=', match.end())].strip())
assert old_types == [entry['complete_source_type'] for entry in types]
assert re.findall(r'^import .+', old_source, re.M) == re.findall(r'^import .+', source, re.M)
request['previous_failed_execution'] = {
    'run_id': 38680984398, 'attempt': 1, 'job_id': 116245255438,
    'source_commit': '178b018f86bd99dd016f3d5d09aa6ea90aa745b4',
    'source_sha256': '37ab3f2ccfcf6ecf859cd9003b31d23b42f7d63542186e3292e237539d013936',
    'status': 'FAILED_STRICT_COMPILATION_API_TYPING_LINT',
    'original_archive': '/workspace/shared/chen-coordination/p0-38680984398.zip',
    'archive_sha256': 'a3800a447a5ceb5ad477eaae06f4720f63cc982f00d9b39debd36da1a1071c0b',
    'compile_log': str(OUT / 'compile-ImbalancedChen.CurrentChenUpsilon6LogDomain.log'),
    'compile_log_sha256': '37abed0640aae6f64f832366b2c8f5b9d1c6610793aad8e7e87253b8b35ec1dd',
    'receipt': str(OUT / 'receipt.json'),
    'receipt_sha256': '39f4b534e107d7004349713c8b433022471d552b7f94519ed8c1ac5070bc47fa',
    'fresh_prerequisites_compiled': 34, 'resource_failure': False
}
request['changed_source_retry_basis'] = [
    'Replace deprecated Set.mem_setOf_eq with Set.mem_ofPred_eq',
    'Remove reported unused one_div_mul_one_div simp argument',
    'Explicitly unfold rectangle before finite-product integrability conversion',
    'Annotate both projection indices and complete continuous-linear-map types',
    'Unfold concrete product form when applying the null-wall supplier',
    'Explicitly expose closed-rectangle and loss-domain membership propositions',
    'Use pinned norm_indicator_le_norm_self directly with explicit set/function instead of failing simplification',
    'Expose eta membership in Iio as a strict inequality before linarith'
]
request['unchanged_scope_checks'] = {
    'all_27_complete_source_declaration_types': 'BYTE_FOR_BYTE_IDENTICAL',
    'direct_imports': 'BYTE_FOR_BYTE_IDENTICAL',
    'no_new_assumptions': True, 'linter_or_gate_disabled': False,
    'original_failed_source_preserved': str(OUT.parent / 'CurrentChenUpsilon6LogDomain.lean'),
    'source_diff': str(OUT / 'source.diff'),
    'new_pinned_API_evidence': str(OUT / 'norm-indicator-api.json')
}
save('REQUESTED.json', request)
print(json.dumps({'source_sha256': sha(source_bytes), 'source_declarations': len(types),
                  'closure_sha256': closure_digest, 'request': str(OUT / 'REQUESTED.json')}, indent=2))
