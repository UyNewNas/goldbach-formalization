#!/usr/bin/env python3
"""Record only the three symmetry pilot owners and their unchanged source inputs."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE_ROOT = Path('/workspace/p26-source-closure')
LOCAL = Path('/workspace/p26-local-checks/symmetry')
PREFIX = 'ImbalancedChen.P2OriginalSaving19HigherMoments'
OWNERS = ['ImbalancedChen.P2OriginalSaving19MomentFiniteReindex',
          PREFIX + 'Symmetry', PREFIX + 'SymmetryPilot']
FROZEN = {
    PREFIX + 'Core': '3738b75a69892c1f9ab68a395b6394817e24a94083ca5254b38c32d73a859832',
    PREFIX + 'GuardLowBoundary': '3fa7f12eb715a9aabac0c431533fbb515ad3d2512aadd8eec677c5b098486604',
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def module_path(module: str) -> str:
    return module.replace('.', '/') + '.lean'

base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SOURCE_ROOT, text=True).strip()
def git_source(path: str) -> bytes:
    return subprocess.check_output(['git', 'show', base + ':' + path], cwd=SOURCE_ROOT)

finite = json.loads((LOCAL / 'FINITE_REINDEX_LOCAL_DIAGNOSTIC.json').read_text())
shapes = json.loads((LOCAL / 'CORE_SHAPES_LOCAL_DIAGNOSTIC.json').read_text())
assert finite['exit_code'] == shapes['exit_code'] == 0
assert finite['source_sha256'] == sha((HERE / module_path(OWNERS[0])).read_bytes())
assert shapes['candidate_symmetry_source_sha256'] == sha((HERE / module_path(OWNERS[1])).read_bytes())
assert shapes['accepted_core_source_sha256'] == FROZEN[PREFIX + 'Core']

modules, inputs, graph = {}, {}, {}
active = []
def visit(module: str) -> None:
    assert module not in active, 'import cycle: ' + module
    if module in inputs:
        return
    path = module_path(module)
    owned = module in OWNERS
    source = HERE / path if owned else SOURCE_ROOT / path
    data = source.read_bytes() if owned else git_source(path)
    if not owned:
        assert source.read_bytes() == data, 'local dependency differs from observed Git base: ' + module
    imports = [m.strip() for m in re.findall(r'^import (.+)$', data.decode(), re.M)]
    digest = sha(data)
    if module in FROZEN:
        assert digest == FROZEN[module], module
    row = {'path': path, 'sha256': digest, 'bytes': len(data), 'imports': imports}
    inputs[module] = {**row, 'local_source_path': str(source),
                      'origin_kind': 'NEW_PILOT_OWNER' if owned else 'UNCHANGED_COHERENT_BASE',
                      'observed_base_commit': None if owned else base}
    if owned:
        modules[module] = {**row, 'local_source_path': str(source),
                           'status': 'SOURCE_CANDIDATE_PENDING_P1_NORMAL_KERNEL_FULL_OWNED'}
    graph[module] = [m for m in imports if m.startswith('ImbalancedChen.')]
    active.append(module)
    for dep in graph[module]:
        visit(dep)
    active.pop()

for owner in OWNERS:
    visit(owner)
assert set(modules) == set(OWNERS)
assert all(m in inputs for m in FROZEN)
assert PREFIX not in inputs
assert PREFIX + 'GuardBySymmetry' not in inputs
assert not any(re.search(r'GuardK[3-6]I', m) for m in inputs)

def closure(module: str) -> list[str]:
    seen, pending = set(), [module]
    while pending:
        m = pending.pop()
        if m not in seen:
            seen.add(m)
            pending.extend(graph[m])
    return sorted(seen)

closure_rows = {m: closure(m) for m in OWNERS}
inputs_payload = {
    'schema': 'p26_symmetry_pilot_local_source_inputs_v1',
    'status': 'STATIC_SOURCE_BINDING_ONLY_NO_P1_ACCEPTANCE',
    'observed_base_source_commit': base,
    'new_owner_order': OWNERS,
    'project_sources': inputs,
    'project_import_graph': graph,
    'source_closures': closure_rows,
    'all_base_sources_match_observed_git_commit': True,
    'all_new_owners_are_unpublished_candidates_at_manifest_generation': True,
}
inputs_path = HERE / 'PILOT_SOURCE_INPUTS.json'
inputs_path.write_text(json.dumps(inputs_payload, indent=2) + '\n')
diagnostic_names = ['FINITE_REINDEX_LOCAL_DIAGNOSTIC.json',
                    'FINITE_REINDEX_LOCAL_AXIOMS.json', 'CORE_SHAPES_LOCAL_DIAGNOSTIC.json']
manifest = {
    'schema': 'p26_symmetry_pilot_three_owner_manifest_v1',
    'status': 'READY_FOR_PARENT_P1_SOURCE_PUBLICATION_NOT_ACCEPTED',
    'baseline_sha256': '59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e',
    'owner_count': 3,
    'recommended_first_order': OWNERS,
    'modules': {m: modules[m] for m in OWNERS},
    'retained_accepted_source_bindings': {m: inputs[m] for m in FROZEN},
    'retained_acceptance_basis': 'Parent-reported existing P1 acceptance; this manifest checks source bytes only.',
    'observed_base_source_commit': base,
    'source_inputs': {'path': str(inputs_path), 'sha256': sha(inputs_path.read_bytes())},
    'source_closure_counts': {m: len(c) for m, c in closure_rows.items()},
    'source_configuration': {p: {'sha256': sha(git_source(p)), 'bytes': len(git_source(p))}
                             for p in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']},
    'local_diagnostics': {name: {'path': str(LOCAL / name), 'sha256': sha((LOCAL / name).read_bytes())}
                          for name in diagnostic_names},
    'diagnostic_limit': 'Only finite reindex and exact copied Core shapes were checked locally; no actual production Core, Symmetry owner, or Pilot acceptance is claimed.',
    'explicitly_out_of_scope': [PREFIX, PREFIX + 'GuardBySymmetry',
                                'Any new high-degree enumeration or Author provider compile'],
    'production_facade_changed': False,
    'old_suppliers_recompiled_by_this_work': False,
    'remote_job_started_by_this_work': False,
    'parent_runner_requirement': 'Use a new three-owner scope; publish these owners and this manifest, then bind every source input to that one published commit. Reuse existing normal/context/kernel/full-owned machinery unchanged.',
}
path = HERE / 'PILOT_SOURCE_MANIFEST.json'
path.write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'status': manifest['status'], 'manifest': str(path),
                  'manifest_sha256': sha(path.read_bytes()), 'observed_base_source_commit': base,
                  'owners': {m: modules[m]['sha256'] for m in OWNERS},
                  'source_closure_counts': manifest['source_closure_counts']}, indent=2))
