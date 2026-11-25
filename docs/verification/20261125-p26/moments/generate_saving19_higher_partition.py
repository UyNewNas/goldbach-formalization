#!/usr/bin/env python3
"""Render isolated Saving19 proof modules without invoking Lean or reading witnesses.

Default output is Core, the five-leaf LowBoundary pilot, and the K6I0 pilot.
All 68 planned modules are constructed in memory and checked before any writes.
--all emits the full source partition; --module additionally emits named modules.
--only-module emits only the named module(s), retaining existing accepted sources.
The parent owns source installation, serialized compilation, and acceptance.
"""

from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_BASELINE = Path('/workspace/scratch/8c9d3a651a4e/goldbach/docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean')
BASELINE_SHA = '59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e'
DONOR_COMMIT = '99c1f8ba1dc453b21f47e30b667db0de93d73387'
DONOR_INDEX_SHA = 'f501759f3d10c55970a87e233cd49f3f98439e69f10842f51e81711d35ccda97'
NS = 'ImbalancedChen.P2OriginalSaving19HigherMoments'
OLD_NS = 'ImbalancedChen.P2OriginalSixthHigherMoments'
RECORDED_DONOR_SOURCES = {
    OLD_NS: '7d49c1d9c5b7a2fdd3b5071b9dc3ad8b2252db293f69c430f8e9a08a6eba0523',
    OLD_NS + 'Core': '303b803ece5db306a5f78d59aba7245ac79379f42d1e11b4d7dbc636a8a59aed',
    OLD_NS + 'GuardLowBoundary': '7aedf2320996cf81a2c42c59fca66437473639af7540e5cb8aa40583aa910718',
    OLD_NS + 'GuardK6I0': 'bb64ccc65175200fc13d2c06dae3aac44aac83f8bb8a42d4e34bc8fc6cb204a4',
    OLD_NS + 'AuthorK0': '55dcc2eebcdfba881b697577f1220a827c7e79c3a8f8ba7667365c19dde68cc9',
    OLD_NS + 'AuthorK1': '08eaa1b54a0e0008814f7780e802cc31fce8dd8ae9acc476250df389ea80806a',
    OLD_NS + 'AuthorK2': 'bb6cd79c70deb9699b35796b742b4275b44c036b3cc6a5bd2db60c71f5cec3d6',
    OLD_NS + 'AuthorK3': '8da5af1314b15fa2776acffd324301be73c8cdf549c85aff1eeea4047ac4f8f6',
    OLD_NS + 'AuthorK4': 'bf90b1ff14add843ff96eafa1e57a3e3451b4905e069dad327bb23f816b8df88',
    OLD_NS + 'AuthorK5': '7328d1ceb0b629cfa67552061c93252619fe148898b07a5c28ba0f23f902e825',
    OLD_NS + 'AuthorK6': 'b97c246736d895a684a758e5f4275a5a88972ebbae134d6fca12a9b15b2b3b78',
}
CORE = NS + 'Core'
K6I0 = NS + 'GuardK6I0'
K6I0_ENUMERATION_MAX_STEPS = 2_000_000
K6I0_FAILED_SOURCE_SHA = 'da73c863f0155ae3bfbe7c48424a6b8b89a8a0b56b5a6968296b3972a12bd338'
PARENT_ACCEPTED_PILOTS = {
    CORE: {'sha256': '3738b75a69892c1f9ab68a395b6394817e24a94083ca5254b38c32d73a859832',
           'job_id': 'job_b86c096a5ec74c7bad39e7155fb6f8ec'},
    NS + 'GuardLowBoundary': {
        'sha256': '3fa7f12eb715a9aabac0c431533fbb515ad3d2512aadd8eec677c5b098486604',
        'job_id': None},
}
K6I0_PARENT_FAILURE = {
    'evidence_source': 'Parent compile feedback; this generator did not execute Lean.',
    'job_id': 'job_89bd4c3ac4574f5e922ed0fd428835b8',
    'source_sha256': K6I0_FAILED_SOURCE_SHA,
    'phase': 'normal compilation; Phase 2 finite tuple enumeration',
    'line': 23,
    'error': 'simp failed: maximum number of steps exceeded',
    'normal_seconds': 21.75,
    'peak_memory_gb_as_reported': 7.55,
    'memory_failure': False,
}
INTERNAL = NS + '.ProofPieces'
LOW_PAIRS = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)]
CORE_PUBLIC = ['duplicateH', 'baryCoefficient', 'bumped', 'integratedPower', 'completeH', 'completeH_cons_succ']
CORE_HELPERS = ['ofFn_nine', 'ofFn_eight', 'rational_smul_self', 'rational_smul_real',
                'baryCoefficient_eq_product', 'multinomial_bumped_factorial',
                'integratedPower_eq_factored', 'completeH_nil', 'completeH_zero']


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def mask_comments(text: str) -> str:
    """Mask nested Lean comments while preserving source offsets and newlines."""
    out = list(text)
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i + 2] = [' ', ' ']
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                out[i:i + 2] = [' ', ' ']
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i + 2] = [' ', ' ']
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            out[i:j] = [' '] * (j - i)
            i = j
        else:
            i += 1
    assert depth == 0
    return ''.join(out)


def declarations(text: str) -> dict[str, dict]:
    code = mask_comments(text)
    matches = list(re.finditer(r'^(private )?(theorem|def|structure)\s+([A-Za-z0-9_.]+)', code, re.M))
    boundaries = [m.start() for m in re.finditer(r'^(?:namespace|end)(?:\s|$)', code, re.M)]
    result = {}
    for i, m in enumerate(matches):
        stop = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        stop = min([stop] + [p for p in boundaries if m.start() < p < stop])
        end = m.start() + len(code[m.start():stop].rstrip())
        assert m[3] not in result
        result[m[3]] = {'kind': m[2], 'private': bool(m[1]),
                        'text': text[m.start():end], 'line': text.count('\n', 0, m.start()) + 1}
    return result


def header(decl: dict) -> str:
    text = decl['text']
    if decl['kind'] == 'structure':
        return text
    stops = [m.start() for m in re.finditer(r':=|\bwhere\b|\n  \|', mask_comments(text))]
    assert stops
    return text[:min(stops)].rstrip()


def proof_body(text: str) -> str:
    assert ':=' in text
    return text.split(':=', 1)[1]


def with_body(original: dict, body: str) -> str:
    return original['text'].split(':=', 1)[0] + ':=' + body


def normalize(text: str) -> str:
    return re.sub(r'\s+', ' ', text).strip()


def render(imports: list[str], namespace: str, texts: list[str], note: str, opens: list[str]) -> str:
    return ('\n'.join('import ' + m for m in imports) + '\n\n'
            + '/-! SOURCE_ONLY / UNCOMPILED CANDIDATE.\n' + note + '\n'
            + 'Original Saving19 public definitions and statement types are retained.\n'
            + 'Finite proof representation specializes the accepted Fin 7 donor.\n'
            + 'No numerical witness, evaluator, assumption, or external estimate is added.\n-/\n'
            + 'namespace ' + namespace + '\nnoncomputable section\n'
            + 'open Set MeasureTheory\nopen scoped BigOperators\n'
            + ''.join('open ' + n + '\n' for n in opens)
            + '\n' + '\n\n'.join(texts) + '\n\nend\nend ' + namespace + '\n')


def dimension_specialize(text: str) -> str:
    # The degree literal is never rewritten.
    return (text.replace(OLD_NS, NS).replace('Fin 7', 'Fin 9').replace('Fin 6', 'Fin 8')
            .replace('Nat.factorial 7', 'Nat.factorial 9').replace('(7 + ', '(9 + ')
            .replace('ofFn_seven', 'ofFn_nine').replace('ofFn_six', 'ofFn_eight'))


def core_helper_specialize(text: str) -> str:
    # Only these three dimension offsets occur in the coefficient helpers.
    return (dimension_specialize(text)
            .replace('((∑ r, e r) + 6).factorial', '((∑ r, e r) + 8).factorial')
            .replace('(∑ r : Fin 9, bumped e i r) + 6 = k + 7',
                     '(∑ r : Fin 9, bumped e i r) + 8 = k + 9')
            .replace('(k + 7).factorial', '(k + 9).factorial'))


def build(baseline: Path, donor_root: Path) -> tuple[dict, dict, dict]:
    blob = baseline.read_bytes()
    assert sha(blob) == BASELINE_SHA, 'review changed baseline before rebasing'
    original = declarations(blob.decode())
    assert len(original) == 36 and all(not d['private'] for d in original.values())
    index_path = donor_root / 'docs/p1/20261125/acceptance-index/ACCEPTED_OWNERS.json'
    accepted = {}
    if index_path.exists():
        index_blob = index_path.read_bytes()
        assert sha(index_blob) == DONOR_INDEX_SHA, 'review changed accepted-donor index'
        accepted = json.loads(index_blob)['owners']
    donor_pins = {}

    def donor(module: str) -> dict[str, dict]:
        path = donor_root / (module.replace('.', '/') + '.lean')
        data = path.read_bytes()
        assert sha(data) == RECORDED_DONOR_SOURCES[module], module
        receipt = accepted.get(module)
        if receipt is not None:
            assert sha(data) == receipt['source_sha256'], module
            assert receipt['source_commit'] == DONOR_COMMIT, module
        donor_pins[module] = {'path': str(path), 'sha256': sha(data),
                              'source_commit': DONOR_COMMIT,
                              'validation_member': receipt['validation_member'] if receipt else None,
                              'validation_sha256': receipt['validation_sha256'] if receipt else None,
                              'evidence_note': 'Hash matched the inspected pre-reset batch10 accepted-source record; no new compile credit.'}
        return declarations(data.decode())

    donor_core = donor(OLD_NS + 'Core')
    donor_facade = donor(OLD_NS)
    donor_guards = {}
    for module in [OLD_NS + 'GuardLowBoundary', OLD_NS + 'GuardK6I0']:
        for name, dec in donor(module).items():
            if name.startswith('integratedPower_newton_guard_'):
                assert name not in donor_guards
                donor_guards[name] = dec
    assert len(donor_guards) == 6
    donor_authors = {k: donor(OLD_NS + f'AuthorK{k}')[f'duplicateH_author_guard_{k}'] for k in range(7)}
    helpers = []
    for name in CORE_HELPERS:
        if name == 'ofFn_nine':
            text = ('theorem ofFn_nine {A : Type*} (f : Fin 9 → A) :\n'
                    '    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] := by rfl')
        elif name == 'ofFn_eight':
            text = ('theorem ofFn_eight {A : Type*} (f : Fin 8 → A) :\n'
                    '    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by rfl')
        else:
            text = core_helper_specialize(donor_core[name]['text'])
        helpers.append(text)
    files = {}

    def add(module: str, text: str, source_names: list[str], helper_names: list[str]) -> None:
        assert module not in files
        code = mask_comments(text)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code)
        assert not re.search(r'\bFin [67]\b', code), module
        files[module] = {'text': text, 'source_declarations': source_names,
                         'helper_declarations': helper_names,
                         'imports': re.findall(r'^import (.+)$', text, re.M)}

    core_imports = ['ImbalancedChen.P2OriginalSaving19SimplexMoments',
                    'Mathlib.Data.Nat.Choose.Multinomial', 'Mathlib.Tactic']
    core_text = render(core_imports, NS, [original[n]['text'] for n in CORE_PUBLIC],
                       'Common definitions and coefficient cancellation; no MomentFloorConsumer import.',
                       ['P2OriginalSaving19SimplexMoments'])
    closing = '\nend\nend ' + NS + '\n'
    assert core_text.endswith(closing)
    core_text = (core_text[:-len(closing)] + '\n\nnamespace ProofPieces\n\n'
                 + '\n\n'.join(helpers) + '\n\nend ProofPieces' + closing)
    add(CORE, core_text, CORE_PUBLIC, CORE_HELPERS)

    def guard(k: int, i: int) -> str:
        direct_name = f'integratedPower_newton_guard_{k}_{i}'
        old_name = (direct_name if direct_name in donor_guards else
                    'integratedPower_newton_guard_0_0' if k == 0 else
                    'integratedPower_newton_guard_6_0' if k == 6 else
                    'integratedPower_newton_guard_1_0')
        new_name = f'integratedPower_newton_guard_{k}_{i}'
        text = (f'theorem {new_name} (y : Fin 9 → ℝ) :\n'
                f'    integratedPower y {i} {k} = duplicateH y {i} {k} /\n'
                f'      ((Nat.factorial 9 : ℝ) * ((9 + {k}).choose {k} : ℝ)) :='
                + dimension_specialize(proof_body(donor_guards[old_name]['text'])))
        assert proof_body(text) == dimension_specialize(proof_body(donor_guards[old_name]['text']))
        if (k, i) == (6, 0):
            before = '  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,'
            after = (f'  simp (config := {{ maxSteps := {K6I0_ENUMERATION_MAX_STEPS} }}) '
                     '[Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,')
            assert text.count(before) == 1
            text = text.replace(before, after)
        expected = (f'theorem {new_name} (y : Fin 9 → ℝ) : '
                    f'integratedPower y {i} {k} = duplicateH y {i} {k} / '
                    f'((Nat.factorial 9 : ℝ) * ((9 + {k}).choose {k} : ℝ))')
        assert normalize(text.split(':=', 1)[0]) == normalize(expected), new_name
        return text

    groups = [(NS + 'GuardLowBoundary', LOW_PAIRS)]
    groups += [(NS + f'GuardK{k}I{i}', [(k, i)])
               for k in range(7) for i in range(9) if (k, i) not in LOW_PAIRS]
    for module, pairs in groups:
        names = [f'integratedPower_newton_guard_{k}_{i}' for k, i in pairs]
        add(module, render([CORE], INTERNAL, [guard(k, i) for k, i in pairs],
                           'Universal polynomial guards: ' + ', '.join(names) + '.',
                           ['P2OriginalSaving19SimplexMoments']), [], names)
    for k in range(7):
        name = f'duplicateH_author_guard_{k}'
        text = dimension_specialize(donor_authors[k]['text'])
        expected = (f'theorem {name} (y : Fin 9 → ℚ) (i : Fin 9) : '
                    f'duplicateH y i {k} = ∑ j : Fin ({k} + 1), '
                    f'completeH (List.ofFn y) ({k} - j.val) * y i ^ j.val')
        assert normalize(text.split(':=', 1)[0]) == normalize(expected), name
        add(NS + f'AuthorK{k}', render([CORE], INTERNAL, [text],
                                     'Author/Newton guard for degree ' + str(k) + '; index stays arbitrary.',
                                     ['P2OriginalSaving19SimplexMoments']), [], [name])

    facade_names = [n for n in original if n not in CORE_PUBLIC]
    facade_texts = []
    changed = ['integratedPower_newton_guard', 'duplicateH_author_guard',
               'rationalMoment_cast', 'integerNewtonNumerator_spec']
    for name in facade_names:
        if name == 'integratedPower_newton_guard':
            body = ' by\n  interval_cases k\n'
            for k in range(7):
                body += '  · fin_cases i\n'
                body += ''.join(f'    · exact integratedPower_newton_guard_{k}_{i} y\n' for i in range(9))
            text = with_body(original[name], body.rstrip())
        elif name == 'duplicateH_author_guard':
            body = ' by\n  interval_cases k\n'
            body += ''.join(f'  · exact duplicateH_author_guard_{k} y i\n' for k in range(7))
            text = with_body(original[name], body.rstrip())
        elif name in ['rationalMoment_cast', 'integerNewtonNumerator_spec']:
            text = with_body(original[name], dimension_specialize(proof_body(donor_facade[name]['text'])))
        else:
            text = original[name]['text']
        facade_texts.append(text)
    imports = ['ImbalancedChen.P2OriginalSaving19MomentFloorConsumer', CORE]
    imports += [m for m, _ in groups] + [NS + f'AuthorK{k}' for k in range(7)]
    add(NS, render(imports, NS, facade_texts,
                   'Public facade. Compile only after every provider has passed the parent pipeline.',
                   ['P2OriginalThirdMinorantLogDictionarySourceOnly', 'P2OriginalSaving19SourceMeasure',
                    'P2OriginalSaving19SimplexMoments', 'P2OriginalSaving19MomentFloorConsumer',
                    'P2PositiveAffineSimplexLogJensenSourceOnly', 'P2DegreeSixLogGapSoundnessSourceOnly',
                    'ProofPieces']), facade_names, [])
    assert len(files) == 68
    recovered, owners = {}, {}
    for module, row in files.items():
        ds = declarations(row['text'])
        for name in row['source_declarations']:
            assert name not in recovered
            recovered[name], owners[name] = ds[name], module
    assert set(recovered) == set(original)
    for name, before in original.items():
        after = recovered[name]
        assert header(before) == header(after), 'changed public contract: ' + name
        if before['kind'] in ['def', 'structure'] or name not in changed:
            assert before['text'] == after['text'], 'changed preserved declaration: ' + name
    validation = {
        'status': 'STATIC_SOURCE_CHECKS_ONLY_NO_LEAN_EXECUTION',
        'original_public_declarations': 36,
        'all_original_public_headers_exactly_preserved': True,
        'all_original_definitions_and_structure_fields_byte_equal': True,
        'only_changed_original_proof_bodies': changed,
        'all_63_integrated_guard_headers_checked_against_original_degree_and_fin9_normalization': True,
        'all_7_author_headers_checked_against_original_degree_and_fin9_nodes': True,
        'planned_source_modules': 68, 'forbidden_code_tokens_absent': True,
        'local_execution_patch': {
            'module': K6I0, 'phase': 'Phase 2 tuple-enumeration simp only',
            'maxSteps': K6I0_ENUMERATION_MAX_STEPS,
            'other_guard_bodies_unchanged': True,
            'status': 'PROPOSED_LIMIT_NOT_COMPILED'},
        'original_declaration_owners': owners,
        'scope_classification': {
            'expression_and_kernel_execution': 'Source partition and explicit reduction order.',
            'omitted_derivation': 'Existing donor coefficient cancellation specialized to d=8.',
            'substantive_mathematical_gap': 'None identified by source-only refactoring; compiled closure not claimed.'},
        'manuscript': {'commit': 'a988cba584d803ae2856a0de50efb582f4f3dd6a',
                       'path': 'paper/release-20261106/en/numerical-appendix.tex',
                       'git_blob': '428e5fb4cd92b01b72119d795b8eeb01c67e3ccd',
                       'label': 'num:simplex-moment',
                       'specialization': 'd=8; alpha=e+unitExponent_i; coefficient k!*(e_i+1)/(k+9)!.'}}
    return files, validation, donor_pins


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.tmp')
    temp.write_bytes(data)
    temp.replace(path)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, default=DEFAULT_BASELINE)
    ap.add_argument('--donor-root', type=Path, required=True, help='restored sparse P1 source checkout')
    ap.add_argument('--out', type=Path, default=HERE)
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--module', action='append', default=[])
    ap.add_argument('--only-module', action='append', default=[])
    ap.add_argument('--check-only', action='store_true')
    args = ap.parse_args()
    if args.only_module and (args.all or args.module):
        ap.error('--only-module cannot be combined with --all or --module')
    out = args.out.resolve()
    assert out == HERE or HERE in out.parents, 'write only inside the isolated candidate directory'
    files, validation, pins = build(args.baseline, args.donor_root)
    pilots = [CORE, NS + 'GuardLowBoundary', NS + 'GuardK6I0']
    selected = (set(args.only_module) if args.only_module else
                set(files) if args.all else set(pilots + args.module))
    assert selected <= set(files)
    if args.check_only:
        print(json.dumps({'status': validation['status'], 'planned_modules': 68,
                          'selected_modules': sorted(selected), 'writes': False}))
        return
    manifest = {}
    for module, row in files.items():
        rel = Path(module.replace('.', '/') + '.lean')
        data = row['text'].encode()
        if module in PARENT_ACCEPTED_PILOTS:
            assert sha(data) == PARENT_ACCEPTED_PILOTS[module]['sha256'], module
        if module in selected:
            atomic_write(out / rel, data)
        manifest[module] = {k: v for k, v in row.items() if k != 'text'}
        manifest[module].update({'path': str(rel), 'bytes': len(data), 'sha256': sha(data),
                                 'emitted_this_invocation': module in selected, 'status': 'SOURCE_ONLY_UNCOMPILED'})
        if module in PARENT_ACCEPTED_PILOTS:
            manifest[module].update({
                'status': 'PARENT_REPORTED_NORMAL_KERNEL_FULL_OWNED_ACCEPTED',
                'parent_result': PARENT_ACCEPTED_PILOTS[module],
                'receipt_rechecked_by_generator': False})
    plan = {'status': 'K6I0_LOCAL_STEP_LIMIT_REPAIR_PENDING_PARENT_COMPILATION',
            'recommended_first_order': pilots,
            'recommended_next_order': [K6I0],
            'retain_accepted_parent_sources_without_recompiling': PARENT_ACCEPTED_PILOTS,
            'acceptance_evidence_note': 'Core and LowBoundary gates reported by parent; no receipts independently rechecked here.',
            'first_stage_import_graph': {m: files[m]['imports'] for m in pilots},
            'pilot_leaves': {pilots[1]: LOW_PAIRS, pilots[2]: [(6, 0)]},
            'requires_MomentFloorConsumer_for_first_stage': False,
            'runner': 'Parent existing serialized guarded pipeline; unchanged limits and gates.',
            'parent_reported_failure': K6I0_PARENT_FAILURE,
            'proposed_local_repair': {
                'module': K6I0,
                'preimage_sha256': K6I0_FAILED_SOURCE_SHA,
                'candidate_sha256': manifest[K6I0]['sha256'],
                'classification': 'Expression execution limit; manuscript moment identity unchanged.',
                'tactic_scope': 'Only the Phase 2 finite-tuple enumeration simp invocation.',
                'maxSteps': K6I0_ENUMERATION_MAX_STEPS,
                'global_runtime_changes': False,
                'other_guard_limits_changed': False,
                'theorem_statement_or_data_changes': False,
                'recompiled': False,
                'status': 'PROPOSED_LIMIT_NOT_COMPILED'},
            'no_cold_facade_build': True,
            'after_pilots': 'Retain passed receipts; emit pending providers as needed, compile serially, then facade.',
            'audit_scope': 'Core, all proof providers, and facade; never facade alone.',
            'archive_regeneration': False, 'cloud_or_local_lean_commands_run': False}
    for name, payload in {
        'PARTITION_MANIFEST.json': {'baseline_path': str(args.baseline), 'baseline_sha256': BASELINE_SHA,
                                    'donor_commit': DONOR_COMMIT, 'donor_index_sha256': DONOR_INDEX_SHA,
                                    'donor_sources': pins, 'modules': manifest},
        'STATIC_VALIDATION.json': validation, 'COMPILE_PLAN.json': plan}.items():
        atomic_write(out / name, (json.dumps(payload, ensure_ascii=False, indent=2) + '\n').encode())
    print(json.dumps({'status': 'SOURCE_ONLY_UNCOMPILED', 'emitted_modules': sorted(selected),
                      'planned_modules': 68, 'original_public_contracts_preserved': 36, 'output': str(out)}))


if __name__ == '__main__':
    main()
