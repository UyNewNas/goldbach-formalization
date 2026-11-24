"""Partition the frozen Higher source; do not synthesize any mathematical body.

This script writes only its own candidate directory. It never invokes Lean,
touches the canonical repository, downloads objects, or creates compile credit.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path('/workspace/scratch/638a86a3af73')
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / 'goldbach-p1/ImbalancedChen/P2OriginalSixthHigherMoments.lean'
EXPECTED = 'a9a4e532991af5ba3b397b7381fd4a1fdf3302ee25ef27a16ebba04e68a68334'
NS = 'ImbalancedChen.P2OriginalSixthHigherMoments'
INTERNAL = NS + '.ProofPieces'
CORE = NS + 'Core'
sha = lambda b: hashlib.sha256(b).hexdigest()


def declarations(text):
    """Extract these ordinary declarations, omitting adjacent outer doc comments."""
    matches = list(re.finditer(r'^(private )?(theorem|def)\s+(\w+)', text, re.M))
    result = {}
    for pos, m in enumerate(matches):
        stop = matches[pos + 1].start() if pos + 1 < len(matches) else text.index('\nend\n', m.start())
        chunk = text[m.start():stop].rstrip()
        while chunk.endswith('-/'):
            begin = chunk.rfind('/--')
            assert begin >= 0
            chunk = chunk[:begin].rstrip()
        result[m[3]] = {
            'name': m[3], 'kind': m[2], 'private': bool(m[1]),
            'line': text[:m.start()].count('\n') + 1,
            'text': chunk,
        }
    return result


def strip_comments(text):
    out = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if text[i] == '\n':
                    out.append('\n')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def body(text):
    if ':=' in text:
        return text.split(':=', 1)[1]
    # Original equation-compiler definitions duplicateH and completeH.
    at = text.index('\n  |')
    return text[at:]


def exported(d):
    return d['text'].removeprefix('private ')


def render(imports, namespace, decl_texts, note, extra_open=''):
    return ('\n'.join('import ' + x for x in imports) + '\n\n'
        + '/-! SOURCE_ONLY / UNCOMPILED.\n'
        + note + '\n'
        + 'The existing a9a4e532 proof bodies are retained; this file changes only\n'
        + 'compilation organization. No numerical row or new evaluator is introduced.\n-/'
        + '\nnamespace ' + namespace + '\nnoncomputable section\n'
        + 'open Set MeasureTheory\nopen scoped BigOperators\n'
        + 'open ImbalancedChen.P2OriginalSixthSimplexMoments\n'
        + extra_open
        + '\n' + '\n\n'.join(decl_texts) + '\n\nend\nend ' + namespace + '\n')


data = SOURCE.read_bytes()
assert sha(data) == EXPECTED
source = data.decode()
original = declarations(source)
assert len(original) == 90
assert sum(d['kind'] == 'def' for d in original.values()) == 10
assert sum(d['kind'] == 'theorem' and not d['private'] for d in original.values()) == 15

core_public = ['duplicateH', 'baryCoefficient', 'bumped', 'integratedPower',
               'completeH', 'completeH_cons_succ']
helpers = ['ofFn_seven', 'ofFn_six', 'rational_smul_self', 'rational_smul_real',
           'baryCoefficient_eq_product', 'multinomial_bumped_factorial',
           'integratedPower_eq_factored', 'completeH_nil', 'completeH_zero']
core_private = {'baryCoefficient_eq_product', 'multinomial_bumped_factorial'}
integrated = [f'integratedPower_newton_guard_{k}_{i}' for k in range(7) for i in range(7)]
author = [f'duplicateH_author_guard_{k}' for k in range(7)]
remaining = [n for n in original if n not in core_public + helpers + integrated + author]
assert len(remaining) == 19
assert all(not original[n]['private'] for n in remaining)

low = ['integratedPower_newton_guard_' + x for x in ['0_0','0_1','1_0','1_1','2_0']]
middle = ['integratedPower_newton_guard_' + x for x in ['4_0','5_1']]
groups = [(NS + 'GuardLowBoundary', low), (NS + 'GuardMiddle', middle)]
groups += [(NS + f'GuardK{k}I{i}', [f'integratedPower_newton_guard_{k}_{i}'])
           for k in range(7) for i in range(7)
           if f'integratedPower_newton_guard_{k}_{i}' not in low + middle]
groups += [(NS + f'AuthorK{k}', [f'duplicateH_author_guard_{k}']) for k in range(7)]
assert len(groups) == 51
assert sorted(n for _, names in groups for n in names) == sorted(integrated + author)

target = HERE / 'candidates/ImbalancedChen'
target.mkdir(parents=True, exist_ok=True)
pre = HERE / 'preimages'
pre.mkdir(exist_ok=True)
(pre / SOURCE.name).write_bytes(data)
original_imports = re.findall(r'^import (.+)$', source, re.M)
files = {}
owners = {}


def save(module, text, names):
    path = target / (module.split('.')[-1] + '.lean')
    assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b', strip_comments(text))
    path.write_bytes(text.encode())
    files[module] = {'path': str(path.relative_to(HERE)), 'bytes': path.stat().st_size,
                     'sha256': sha(path.read_bytes()), 'source_declarations': names,
                     'imports': re.findall(r'^import (.+)$', text, re.M),
                     'status': 'SOURCE_ONLY_UNCOMPILED'}
    for n in names:
        assert n not in owners
        owners[n] = module


core_text = render(original_imports, NS, [original[n]['text'] for n in core_public],
                   'Shared definitions and the existing complete-homogeneous successor law.')
closing = '\nend\nend ' + NS + '\n'
assert core_text.endswith(closing)
core_text = (core_text[:-len(closing)] + '\n\nnamespace ProofPieces\n\n'
             + '\n\n'.join(original[n]['text'] if n in core_private else exported(original[n])
                             for n in helpers)
             + '\n\nend ProofPieces' + closing)
save(CORE, core_text, core_public + helpers)
for module, names in groups:
    save(module, render([CORE], INTERNAL, [exported(original[n]) for n in names],
                        'Existing universal polynomial guards: ' + ', '.join(names) + '.'), names)
save(NS, render(original_imports + [m for m, _ in groups], NS,
                [original[n]['text'] for n in remaining],
                'Public facade for the original degree-zero-through-six simplex moments.\n'
                'All original public fully qualified names, theorem headers, and definition\n'
                'bodies are retained. Five definitions and completeH_cons_succ are imported\n'
                'from Core; the other public declarations remain owned by this module.',
                'open ProofPieces\n'), remaining)
assert set(owners) == set(original)
assert len(files) == 53

# Recover every moved declaration and compare the exact mathematical source text.
new_decls = {}
for module, meta in files.items():
    for n, d in declarations((HERE / meta['path']).read_text()).items():
        # Core contains a namespace command between its two declaration groups.
        # It belongs to neither mathematical declaration.
        d['text'] = re.sub(r'\n+(?:namespace|end) ProofPieces\s*$', '', d['text']).rstrip()
        assert n not in new_decls
        new_decls[n] = d
assert set(new_decls) == set(original)
mapping = []
for n, old in original.items():
    new = new_decls[n]
    expected = old['text'] if n in core_private or not old['private'] else exported(old)
    assert expected == new['text'], n
    mapping.append({
        'source_name': n, 'kind': old['kind'], 'original_line': old['line'],
        'original_source_owner': NS, 'new_source_owner': owners[n],
        'original_visibility': 'private' if old['private'] else 'public',
        'new_visibility': 'private' if n in core_private else ('internal_namespace' if old['private'] else 'public'),
        'original_public_fqn': None if old['private'] else NS + '.' + n,
        'new_public_fqn': None if n in core_private else (INTERNAL if old['private'] else NS) + '.' + n,
        'old_private_kernel_name': None,
        'private_kernel_name_note': 'Enumerate actual serialized owner declarations during the new audit; no generated private kernel name is guessed.' if old['private'] else None,
        'mathematical_declaration_text_identical_except_private_modifier': True,
        'body_sha256': sha(body(old['text']).encode()),
        'new_body_sha256': sha(body(new['text']).encode()),
    })

# Verify successful probe groups contain these exact bodies and retain their order.
probe_root = ROOT / 'context-recovery/batch9-verification/batch9-higher-full-and-frontier/higher/reused-batch8-evidence/inputs/probes'
batch9_root = probe_root.parents[3]
probe_execution = probe_root.parents[1] / 'execution/lane-0'
probe_specs = [
    ('Low', probe_root / 'P2OriginalSixthHigherMomentsFactoredLowBoundaryProbe.lean',
     '50045703c1e682b25a2b85e49ed13d657461267d9d8a6343cdc85f7a97f98bd0', low,
     '5e10c9a52f8dd5729d250bcf120445a3f9ce365fdd4f83b95438daf20608b6d0', 29.350),
    ('Middle', probe_root / 'P2OriginalSixthHigherMomentsFactoredMiddleProbe.lean',
     '989ba9d558fb5675b457f87c7a127976763cca261a2ded17657cffe3e97c6c4c', middle,
     'a7ebd39f29b098a75e09fb5d5ea1b06d5a339e666bfd9cc0e8edf0a6de527189', 62.816),
]
probes = []
for label, path, expected_sha, names, log_sha, seconds in probe_specs:
    blob = path.read_bytes()
    assert sha(blob) == expected_sha
    parsed = declarations(blob.decode())
    for n in names:
        pn = n.replace('integratedPower_newton_guard_', 'integrated_')
        assert body(parsed[pn]['text']) == body(original[n]['text']), (label, n)
    command_stem = 'higher-corrected-lowboundary-probe' if label == 'Low' else 'higher-first-middle-probe'
    command_path = probe_execution / (command_stem + '-command.json')
    command = json.loads(command_path.read_text())
    assert command['exit_code'] == 0 and command['log_sha256'] == log_sha
    assert sha((probe_execution / (command_stem + '.log')).read_bytes()) == log_sha
    probes.append({'label': label, 'source': str(path), 'source_sha256': expected_sha,
                   'actual_normal_exit_code': 0, 'actual_normal_seconds': command['elapsed_seconds'],
                   'actual_log_sha256': log_sha, 'exact_existing_group': names,
                   'actual_command_receipt': str(command_path),
                   'actual_command_receipt_sha256': sha(command_path.read_bytes()),
                   'new_group_module': next(m for m, ns in groups if ns == names),
                   'receipt_scope': 'Original probe owner only; new module owner is uncompiled.'})

failure_path = ROOT / 'context-recovery/batch9-module-errors/P2OriginalSixthHigherMoments.log'
failure = failure_path.read_bytes()
assert b'lean::memory_exception' in failure and b'Lean exited with code 134' in failure
evidence = HERE / 'evidence'
evidence.mkdir(exist_ok=True)
shutil.copyfile(failure_path, evidence / failure_path.name)
full_receipt_root = ROOT / 'context-recovery/batch9-verification/batch9-higher-full-and-frontier/higher'
normal_command = json.loads((full_receipt_root / 'execution/lane-0/higher-full-module-normal-command.json').read_text())
normal_result = json.loads((full_receipt_root / 'execution/lane-0/NORMAL_RESULT.json').read_text())
assert normal_command['exit_code'] == 1
assert normal_result['source_sha256'] == EXPECTED
assert sha((full_receipt_root / 'execution/lane-0/higher-full-module-normal.log').read_bytes()) == normal_command['log_sha256']
for rel in ['execution/lane-0/higher-full-module-normal-command.json',
            'execution/lane-0/higher-full-module-normal.log',
            'execution/lane-0/NORMAL_RESULT.json',
            'execution/lane-0/DEPENDENCIES_BEFORE.json',
            'execution/lane-0/FOUR_ROOTS_BEFORE.json',
            'execution/lane-0/SOURCE_FIVE_BEFORE.json',
            'execution/lane-0/SOURCE_FIVE_AFTER.json']:
    shutil.copyfile(full_receipt_root / rel, evidence / Path(rel).name)
for label, path, _, _, _, _ in probe_specs:
    stem = 'higher-corrected-lowboundary-probe' if label == 'Low' else 'higher-first-middle-probe'
    for suffix in ['-command.json', '.log']:
        shutil.copyfile(probe_execution / (stem + suffix), evidence / (stem + suffix))

degree6_root = ROOT / 'context-recovery/accepted-seed90-and-frontier-records/higher-reduction-and-parent-frontier'
degree6_source = degree6_root / 'FactoredDegreeSixProbe.lean'
degree6_command_path = degree6_root / 'higher-degree-six-probe-COMMAND.json'
degree6_command = json.loads(degree6_command_path.read_text())
assert degree6_command['exit_code'] == 0
assert sha(degree6_source.read_bytes()) == '11b4a705fd2ec992d84d9e63a0ce6a47e3247f7ee679b8b515c341b8eef099cd'
assert sha((degree6_root / 'higher-degree-six-probe.log').read_bytes()) == degree6_command['log_sha256']
degree6 = declarations(degree6_source.read_text())['integrated_six_six']
assert body(degree6['text']).replace('real_smul]', 'rational_smul_real]') == body(original['integratedPower_newton_guard_6_6']['text'])
for name in ['higher-degree-six-probe-COMMAND.json', 'higher-degree-six-probe.log', 'higher-degree-six-probe-lane.json']:
    shutil.copyfile(degree6_root / name, evidence / name)
probes.append({'label': 'DegreeSix', 'source': str(degree6_source),
               'source_sha256': sha(degree6_source.read_bytes()),
               'actual_normal_exit_code': 0,
               'actual_normal_seconds': degree6_command['elapsed_seconds'],
               'actual_log_sha256': degree6_command['log_sha256'],
               'actual_command_receipt_sha256': sha(degree6_command_path.read_bytes()),
               'exact_existing_group': ['integratedPower_newton_guard_6_6'],
               'body_comparison': 'Identical after the existing helper alias real_smul -> rational_smul_real.',
               'new_group_module': NS + 'GuardK6I6',
               'receipt_scope': 'Original probe owner only; new module owner is uncompiled.'})
dependency_sources = normal_result['project_dependency_sources']
for module, expected_sha in dependency_sources.items():
    path = ROOT / 'goldbach-p1' / (module.replace('.', '/') + '.lean')
    assert sha(path.read_bytes()) == expected_sha, module
protected_roots = json.loads((full_receipt_root / 'execution/lane-0/FOUR_ROOTS_BEFORE.json').read_text())
protected_root_sources = {}
for module, records in protected_roots.items():
    rel = module.replace('.', '/') + '.lean'
    actual_sha = sha((ROOT / 'goldbach-p1' / rel).read_bytes())
    assert actual_sha == records[rel]['sha256'], module
    protected_root_sources[module] = actual_sha
resource_evidence = {
    'status': 'READ_ONLY_EXISTING_RECEIPTS',
    'probes': [{
        'label': p['label'], 'exit_code': p['actual_normal_exit_code'],
        'elapsed_seconds': p['actual_normal_seconds'],
        'log_sha256': p['actual_log_sha256'],
        'probe_specific_peak_bytes': None,
        'peak_availability': 'Unknown: the existing command/lane/raw-log records provide no per-probe RSS or peak-memory measurement.',
    } for p in probes],
    'degree_six_inner_lane_wall_seconds': 109.03445014600584,
    'full_monolithic_batch9_outer_job_peak_bytes': 21231366144,
    'outer_peak_scope': 'Whole two-lane MCP job, reported by parent; it cannot be assigned to Higher or any individual guard.',
    'scheduling_implication': 'Do not infer a safe heavy-heavy two-lane combination from elapsed time. Parent plans a separate guarded Core -> proof-unit chunks -> root -> closure-audit schedule, reusing valid successful units.',
    'cloud_queries_or_probe_reruns_performed': False,
}
(HERE / 'PROBE_RESOURCES.json').write_text(json.dumps(resource_evidence, ensure_ascii=False, indent=2) + '\n')

manifest = {
    'status': 'SOURCE_ONLY_UNCOMPILED',
    'baseline_commit': 'e44e941df0a4cdf126fc0a0c41df3abd7637d1e8',
    'original_source_sha256': EXPECTED, 'original_source_bytes': len(data),
    'actual_failure': {'path': 'evidence/' + failure_path.name, 'bytes': len(failure),
                       'sha256': sha(failure), 'lean_exit_code': 134,
                       'outer_normal_exit_code': 1, 'lake_display_seconds': 808,
                       'classification': 'interpreter memory_exception; no proof-level goal or leaf location emitted',
                       'complete_normal_command': normal_command,
                       'outer_job_peak_bytes_reported_by_parent': 21231366144,
                       'outer_job_peak_is_not_proven_single_leaf_memory': True},
    'counts': {'original_source_declarations': 90, 'public_definitions': 10,
               'public_theorems': 15, 'original_private_theorems': 65,
               'guard_files': 51, 'new_files': 52, 'total_files': 53,
               'core_definitions_moved': 5, 'core_public_theorems_moved': 1,
               'private_helpers_kept_private': 2, 'private_helpers_exported_in_internal_namespace': 7,
               'private_guards_exported_in_internal_namespace': 56},
    'core_public_migrations': core_public,
    'all_declaration_mapping': mapping,
    'files': files,
    'successful_group_reuse': probes,
    'unchanged_existing_project_dependency_sources': dependency_sources,
    'protected_original_four_roots_sha256': protected_root_sources,
    'probe_resource_evidence': 'PROBE_RESOURCES.json',
    'observed_direct_consumer': {
        'module': 'ImbalancedChen.P2OriginalSixthMomentRow',
        'imports_original_root': True,
        'explicitly_opened_names': ['rationalMoment','rationalMoment_cast','realMoment','integral_interpolate_mul_power'],
        'these_four_names_keep_original_source_owner': True,
        'external_references_to_original_private_leaf_names_found': False,
    },
    'original_complete_normal_receipt': 'evidence/NORMAL_RESULT.json',
    'compile_order': [CORE] + [m for m, _ in groups] + [NS],
    'compile_requirements': [
        'Use existing exact guard/serializer, normal driver and unchanged 4m heartbeats/100k depth.',
        'Build Core first, then one listed proof unit at a time; do not ask Lake to cold-build all 51 guards concurrently.',
        'Each unit imports only Core, never an earlier guard. Existing successful units can be reused by source/object/context hashes after a later failure.',
        'The public root is last, after all proof units have valid normal receipts; it assembles the original statements without rerunning their tactic bodies.',
        'Retain complete raw logs and source/five-artifact records per new owner. No object rename, synthetic Lake trace, or probe credit migration.',
        'New serialized and full-owned audits must cover the union of Core, all 51 proof units and the original root. Root-only audit is insufficient.',
        'Enumerate generated declaration owners from actual environments; the 90 source declarations are a static coverage checklist, not an exhaustive serialized-owner whitelist.',
    ],
    'manuscript': {'pin': 'a988cba584d803ae2856a0de50efb582f4f3dd6a',
                   'file': 'paper/release-20261106/en/numerical-appendix.tex',
                   'formula': 'num:simplex-moment', 'lines': [181,188],
                   'preserved_scope': 'd=6, seven barycentric coordinates, duplicated eighth node, degree k <= 6, factorial 7! times choose(7+k,k); all node values arbitrary'},
    'limitations': [
        'This is a source partition, not a proven diagnosis of which individual declaration exhausted memory.',
        'Successful probe groups establish useful previous compilation granularity, not acceptance under the new module owners.',
        'The two known successful groups are retained intact. Every other proof body is preserved exactly; no polynomial derivation is rewritten.',
        'Fresh processes reduce accumulated elaboration state, but one previously unobserved individual guard or final facade could still expose an error or memory limit.',
        'The final facade imports the compiled proof objects; its import/audit memory must be measured, not assumed negligible.',
        'No new Lean run, cloud command, canonical edit or Git mutation was performed by this package generator.',
    ],
}
(HERE / 'MANIFEST.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
(HERE / 'COMPILE_PLAN.json').write_text(json.dumps({k: manifest[k] for k in ['status','original_source_sha256','compile_order','compile_requirements','files','unchanged_existing_project_dependency_sources','protected_original_four_roots_sha256','probe_resource_evidence']}, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'directory': str(HERE), 'files': len(files),
                  'guards': len(groups), 'manifest_sha256': sha((HERE/'MANIFEST.json').read_bytes()),
                  'core_sha256': files[CORE]['sha256'], 'root_sha256': files[NS]['sha256']}, indent=2))
