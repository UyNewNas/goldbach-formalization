"""Byte/text/JSON receipts only. Does not load Lean, evaluate proofs, or replay data."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
S = ROOT / 'docs/source-only/20261102-resume-30s'
OUT = S / 'S/s27_review_density'

SOURCES = [
    's13_all22_actual_ledger/P4AOriginalFourPositiveEndpoints.lean',
    's13_all22_actual_ledger/P4AOriginalCatalogFiveArchiveSchedule.lean',
    's13_all22_actual_ledger/P4AOriginalCatalogFiveFourteenJointSchedule.lean',
    's14_full_buffered_compiler/P4AFiniteCapTaggedConstructor.lean',
    's14_full_buffered_compiler/P4AFiniteCapTaggedPayment.lean',
    's14_full_buffered_compiler/P4AFiniteCapTaggedSupport.lean',
    's14_full_buffered_compiler/P4AOriginalFull87FiniteCapCandidates.lean',
    's15_actual_density_close/P4AActualRefinableArchivePayment.lean',
    's15_actual_density_close/P4AActualFinitePositiveEndpoint.lean',
    's15_actual_density_close/P4AActualJointDensitySchedule.lean',
]

REFERENCES = [
    'ImbalancedChen/P4AAll22OriginalKLedger.lean',
    'ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean',
    'ImbalancedChen/P4AActualFirstIntegralSelectedK.lean',
    'ImbalancedChen/ActualCompilerDensityReserve.lean',
    'ImbalancedChen/ActualUpperCountingInputs.lean',
    'ImbalancedChen/RealUpperCountingAssembly.lean',
    'ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean',
    'ImbalancedChen/P4BLabelledOuterPPUpperAssembly.lean',
    'ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean',
    'ImbalancedChen/P1OriginalFifthGrid400RefinedFullBoxCover.lean',
    'docs/source-only/20261102-resume-30o/compact_total_endpoint/P2OriginalCompactWholeFunctionalEndpoint.lean',
    'docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactCachedEndpointCandidate.lean',
    'docs/source-only/20261102-resume-30o/actual_two_reserves/P4ACommonPolicyTaggedCompiler.lean',
    'docs/source-only/20261102-resume-30p/actual_two_reserves/P4AUpperTaggedContinuationAccounting.lean',
    'docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdPayment.lean',
    'docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveGlobalLossReduction.lean',
    'docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualCompleteCatalogFiveCapPayment.lean',
    'docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualSmallTailDensityCatalogue.lean',
    'docs/source-only/20261102-resume-30r/compiler_reserve/P4AUpperTaggedFirstPrefixDisagreement.lean',
    'docs/source-only/20261102-resume-30r/compiler_reserve/P4AUpperTaggedFrozenAdmissionCatalogue.lean',
    'docs/source-only/20261102-resume-30r/compiler_reserve/P4AHeldTaggedFiniteAdmissionPayment.lean',
    'docs/source-only/20261102-resume-30r/fifth_reserve64/P5HistoricalActualReserve64Schedule.lean',
    'docs/source-only/20261102-resume-30h/upper_jensen/P5HistoricalGatePaidReserveSchedule.lean',
    'docs/source-only/20261102-resume-30j/all22_suppliers/P4AOriginalSecondPhysicalIntegral.lean',
    'docs/source-only/20261102-resume-30o/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean',
    'docs/source-only/20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean',
    'docs/source-only/20261102-resume-30s/s10_full87_actual_history/P4AOriginalFull87SourceDispatch.lean',
    'docs/source-only/20261102-resume-30s/s08_full_fifth_floor/P5OriginalFullFifthFloorIntegral.lean',
]

DIRECT_OVERRIDES = {
    'ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint': REFERENCES[10],
    'ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment': REFERENCES[16],
    'ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve':
      'docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean',
    'ImbalancedChen.P4AOriginalSecondPhysicalIntegral': REFERENCES[23],
    'ImbalancedChen.P4AHeldTaggedFiniteAdmissionPayment': REFERENCES[20],
    'ImbalancedChen.P4AUpperTaggedContinuationAccounting': REFERENCES[13],
    'ImbalancedChen.P4AOriginalFull87SourceDispatch': REFERENCES[26],
    'ImbalancedChen.P5HistoricalActualReserve64Schedule': REFERENCES[21],
    'ImbalancedChen.P5OriginalFullFifthFloorIntegral': REFERENCES[27],
}
for p in SOURCES:
    DIRECT_OVERRIDES['ImbalancedChen.' + Path(p).stem] = (S / p).relative_to(ROOT).as_posix()

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def receipt(p, role):
    raw = p.read_bytes()
    body = raw.decode('utf-8-sig')
    rows = body.splitlines()
    result = {
        'path': p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else p.as_posix(),
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'bytes': len(raw), 'line_count': len(rows), 'inspection': role,
    }
    if p.suffix == '.lean':
        result['module'] = 'ImbalancedChen.' + p.stem
        result['namespaces'] = re.findall(r'^namespace\s+(\S+)', body, re.M)
        result['imports'] = []
        for number, row in enumerate(rows, 1):
            match = re.match(r'^import\s+(\S+)', row)
            if match:
                module = match[1]
                path = DIRECT_OVERRIDES.get(module)
                if path is None:
                    candidate = ROOT / (module.replace('.', '/') + '.lean')
                    if candidate.exists():
                        path = candidate.relative_to(ROOT).as_posix()
                resolved = {'module': module, 'line': number}
                if path:
                    target = ROOT / path
                    resolved.update({'source_path': path, 'raw_sha256': digest(target)})
                else:
                    resolved['source_resolution'] = 'reference_only_not_resolved_by_this_receipt'
                result['imports'].append(resolved)
        result['declarations'] = [
            {'line': number, 'kind': m[1], 'name': m[2]}
            for number, row in enumerate(rows, 1)
            if (m := re.match(r'^(?:private\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|structure|lemma)\s+(\S+)', row))
        ]
    return result

report_dirs = [S / 's13_all22_actual_ledger', S / 's14_full_buffered_compiler', S / 's15_actual_density_close']
author_files = []
for folder in report_dirs:
    for name in ('REPORT.md', 'REGISTRY.json'):
        p = folder / name
        if p.exists():
            if p.suffix == '.json':
                json.loads(p.read_text(encoding='utf-8-sig'))
            author_files.append(receipt(p, 'author_metadata_snapshot'))

baseline = [
    S / 'BRIEF.md',
    ROOT.parent / 'chen-imbalanced-semiprimes/paper/source/manuscript-body.tex',
    ROOT.parent / 'chen-imbalanced-semiprimes/paper/source/modules/global-positive-upper-completion-20261010.txt',
    ROOT.parent / '1_+_1.748_lean_proofs/main.md',
    ROOT / 'docs/source-only/20261102-resume-30r/reviews/r26_review_reserves_density.md',
    ROOT / 'docs/source-only/20261102-resume-30r/all22_actual_sources/ALL22_SOURCE_MAP.json',
    S / 's13_all22_actual_ledger/ALL22_TERMINAL_MAP.json',
]
for directory in ('all22_actual_sources','catalog5_global_losses','full_buffered_policy','compiler_reserve','actual_density_reserve'):
    for name in ('REPORT.md','REGISTRY.json'):
        baseline.append(ROOT / 'docs/source-only/20261102-resume-30r' / directory / name)

old_map = json.loads((ROOT / 'docs/source-only/20261102-resume-30r/all22_actual_sources/ALL22_SOURCE_MAP.json').read_text(encoding='utf-8-sig'))
new_map = json.loads((S / 's13_all22_actual_ledger/ALL22_TERMINAL_MAP.json').read_text(encoding='utf-8-sig'))
copied_fields = ('slot_one_based', 'id', 'source', 'field', 'value', 'accounting_role')
map_fields_equal = [tuple(row[k] for k in copied_fields) for row in old_map['entries']] == [tuple(row[k] for k in copied_fields) for row in new_map['entries']]

registry = {
    'task': 'S27_independent_review_density',
    'status': 'NARROW_SOURCE_REVIEW_PASS_WHOLE_YELLOW_HOLD',
    'source_only': True, 'compiled': False, 'kernel_verified': False,
    'formal_credit': 0, 'finite_bodies': 'UNEVALUATED',
    'actualterminal': False, 'allpremises': False, 'wholeclosure': False,
    'whole_assigned_yellow_scope_source_complete': False,
    'hdensity_premises_removed': 0, 'green_recommendation': False,
    'toolchain': 'leanprover/lean4:v4.33.0-rc1',
    'mathlib_pin': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    'native_upstream_pin': 'subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958',
    'reviewed_sources': [receipt(S / p, 'complete_current_proof_body_read') for p in SOURCES],
    'reference_sources': [receipt(ROOT / p, 'relevant_definitions_signatures_and_proof_body_read') for p in REFERENCES],
    'author_metadata': author_files,
    'baseline_metadata': [receipt(p, 'original_or_prior_review_read') for p in baseline],
    'all22_map_text_comparison': {'entry_count': len(new_map['entries']),
        'copied_fields': copied_fields, 'exact_string_copy_equal': map_fields_equal,
        'numerical_evaluation': False, 'actual_same_final_policy_instance': False},
    'report': receipt(OUT / 'REPORT.md', 'independent_review_report'),
    'metadata_helper': receipt(Path(__file__).resolve(), 'byte_text_json_only_no_proof_execution'),
    'actual_terminal': {
        'path': 'ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean',
        'declaration': 'ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers.current_realBad_upper_of_actual_density_and_uniform_smooth_PP',
        'parameter': 'hdensity', 'line': 40,
        'quantifiers': 'every delta>0, eventually all even N, same concrete precision-indexed coefficient and moduli',
        'interface_issue': 'attachedUpperCoefficient uses first-exit retain; tagged ALL/ANY compiler is a general coefficient. No equality supplied. Existing general same-rho assembly is available.'
    },
    'removed_local_premises': [
        'All four actual analytic positive endpoint bounds are supplied without endpoint fields.',
        'Actual catalog5 original archive e/chi/mesh conditions are constructed; all later q work.',
        'Slot5 and slot16 ordinary arithmetic endpoints share actual e/q/chi/omega; each costs its own eta.',
        'The explicit finite-cap constructor has derived support/J0, complete changed-set coverage and total u_c payment.',
        'Actual full87 scalar candidates retain original gates and localize rejected actions to explicit collars.',
        'One common actual archive schedule carries the finite-third quarter and sums catalog5+caps and reserve64 below eta; S08 stored-endpoint-minus-reserve also gives the original safe fifth integral on those same witnesses.',
        'Actual finite positive root+third functional fits original four-positive endpoint plus the inherited u_d/4.'
    ],
    'remaining_premises': [
        'Complete original sixth/full87 causal policy and actual buffered finite cap realization.',
        'All22 original endpoints as signed current-parent increments of that one policy, preserving multiplicity and one-time replacement rules.',
        'Full87 finite-candidate rejection-collar mass payment and buffered gain/history transport.',
        'Instantiation of the complete finite-cap compiler at the original actual full87 table, selector, gate and history.',
        'Complete remaining density costs below 3*u_d/4 and independent actual compiler cost below u_c on one common pre-N schedule.',
        'Correct concrete general-compiler-to-final-same-rho API handoff; no assumed first-exit equality.',
        'Same-source remote elaboration/kernel, finite candidate acceptance, exact signatures and transitive axiom audit.'
    ],
    'budget_rules': {
        'existing_third': 'u_d/4 carried once',
        'remaining_density': '3*u_d/4; not closed',
        'compiler': 'separate u_c; fully paid only for explicit finite-cap constructor, original full87 instance pending',
        'R07_R10': 'complete catalog5 including smallOmitted paid; earlier alternative catalogues never added',
        'S15_joint': 'catalog5+caps < eta/2 plus actual reserve64 < eta/2; reserve also lies below the unchanged fifth safe-floor margin and is charged once; oldliteral bound distinct and not included',
        'S13_joint': 'slot5 and slot16 each eta, no claim that their sum is eta',
        'presieve': 'Dplus*Mplus + Dminus*Mminus minus actual correction; old/new correction difference retained'
    },
    'remote_evidence': {
        'reviewer_dispatched_or_ran': False,
        'verified_receipt_in_this_review': None,
        'required': [
            'Reuse identical source/toolchain/dependency receipt if already reliable; root/S02 own this audit.',
            'Exact commit/tree and raw-source closure hashes; original replacement/materialization versions.',
            'Successful remote workflow/job/artifact tied to exact intended exports and kernel replay.',
            'Actual cached 2M compact finite candidate accepted, not merely present as unevaluated rfl.',
            'Printed theorem signatures with all original premises discharged and correct same-rho instance.',
            'Transitive axiom audit without sorryAx, new mathematical axioms, unsafe substitute or target-equivalent hypothesis.',
            'Independent whole-scope source audit as well as CI success.'
        ]
    },
    'difficulty': 'Source/API issues and fillable omitted conversions are distinguished from unresolved full construction/estimates; no manuscript counterexample asserted.',
    'prohibited_actions_performed': [],
}
(OUT / 'REGISTRY.json').write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'sources': len(SOURCES), 'author_metadata': len(author_files),
    'report_sha256': digest(OUT / 'REPORT.md'), 'registry_sha256': digest(OUT / 'REGISTRY.json')}, indent=2))
