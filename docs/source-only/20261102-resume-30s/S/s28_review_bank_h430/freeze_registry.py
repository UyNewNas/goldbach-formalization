"""Review bookkeeping only: read source bytes/text and write this review's JSON.
No Lean, proof guard, numerical certificate, subprocess, network, or Git execution.
"""
from pathlib import Path
import hashlib
import json
import re

BASE = Path('E:/timot/Documents/FilesForGPT/Myath')
REPO = BASE / 'goldbach-proof-continuation'
S = REPO / 'docs/source-only/20261102-resume-30s'
OUT = S / 'S/s28_review_bank_h430'
SCOPES = ['s16_gamma5_and_costs', 's17_causal_bank_licences',
          's18_full_member_441', 's23_adopted_seed_actual_counts']

def pin(p, role):
    p = Path(p)
    raw = p.read_bytes()
    txt = raw.decode('utf-8-sig')
    item = {'path': p.as_posix(), 'sha256': hashlib.sha256(raw).hexdigest(),
            'bytes': len(raw), 'lines': len(txt.splitlines()), 'role': role}
    if p.suffix == '.lean':
        item.update(intended_module='ImbalancedChen.' + p.stem,
                    direct_imports=re.findall(r'^import\s+(\S+)', txt, re.M),
                    namespaces=re.findall(r'^namespace\s+(\S+)', txt, re.M),
                    declarations=[{'kind': m.group(1), 'name': m.group(2),
                                   'line': txt[:m.start()].count('\n') + 1}
                                  for m in re.finditer(r'^(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+(\S+)', txt, re.M)],
                    compiled=False, kernel_verified=False, formal_credit=0)
    return item

reviewed = []
author_records = []
missing_author_records = []
for scope in SCOPES:
    reviewed.extend(pin(p, 'independently read S source; static mathematical review only')
                    for p in sorted((S / scope).glob('*.lean')))
    for name in ['REPORT.md', 'REGISTRY.json']:
        p = S / scope / name
        if p.exists():
            author_records.append(pin(p, 'author frozen scope/pin record; not kernel evidence'))
        else:
            missing_author_records.append(p.as_posix())

primary_paths = [
    S / 'BRIEF.md',
    BASE / '1_+_1.748_lean_proofs/main.md',
    BASE / 'chen-imbalanced-semiprimes/paper/source/manuscript-body.tex',
    BASE / 'chen-imbalanced-semiprimes/paper/source/modules/global-chen-lower-completion-20261010.txt',
    BASE / 'chen-imbalanced-semiprimes/proof-library/source/second-seed-stable-prefix-extension.tex',
    BASE / 'chen-imbalanced-semiprimes/proof-library/source/second-seed-certified-finite-feedback.tex',
] + [BASE / 'goldbach-research' / n for n in [
    'global-selected-numeric-completion-20261010.py',
    'certify_second_seed_first_feedback.py', 'certify_second_seed_finite_iteration.py',
    'certify_second_seed_omega_envelope.py', 'certify_conservative_chen.py',
    'certify_replacement_second_seed.py']]

production_names = [
    'P5OriginalFixedDensitySupplierAssembly', 'P2HistoricSavedOrdinaryDefectAssembly',
    'P2TableActionSoundness', 'RenewalFiniteErrorPropagationP5',
    'P2EnhancedSeedActualFeedbackAssembly', 'P2EnhancedLowerPrimeChildCarriers',
    'P5OriginalActionMassBound', 'P2SeedOmegaFirstThreeKernel',
    'P2SeedOmegaSwitchedKernelFour', 'P2SeedOmegaLiteralFunctional',
    'P2HistoricLogPointInterpreter', 'P2HistoricQ80DefectLookup',
    'P5OriginalPhysicalBufferedU6NativeMain']
read_reuse_paths = [REPO / 'ImbalancedChen' / (n + '.lean') for n in production_names]
read_reuse_paths += [REPO / p for p in [
    'docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalPhysicalOldProfileMass.lean',
    'docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalClosedCellProfileAtoms.lean',
    'docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalHalfOpenProfileCarrier.lean',
    'docs/source-only/20261102-resume-30q/enhanced_nonunit/P2EnhancedNonunitLabelGeometry.lean',
    'docs/source-only/20261102-resume-30j/hstarts/P5OriginalStartsCommonBetaCount.lean',
    'docs/source-only/20261102-resume-30j/h5/P5OriginalU5SameQSeedEntrance.lean',
    'docs/source-only/20261028-resume-30c/certificate_triple/P2Selected430CausalOccurrenceExporter.lean',
    '.lake/proof-continuation/source-reviews/drafts/20261024zzz-DispatchFallback/p2-hbank-licence/P2HistoricHBankZeroPrefix.lean',
    '.lake/proof-continuation/source-reviews/drafts/20261028-Certificate-Sol6-Intervals-Phase3/P2OriginalHBankFirstPositiveSourceBoundary.lean',
    'docs/source-only/20261102-resume-30r/h430_parent_theta_441/Part5OriginalH430ArithmeticAtomRows.lean']]

R = REPO / 'docs/source-only/20261102-resume-30r'
r_records = [R / 'reviews/r27_review_bank.md', R / 'reviews/r28_review_h430.md']
for scope in ['actual_causal_marks', 'gamma_costs_units', 'adopted_seed_count',
              'h430_full_member', 'h430_native_weights', 'h430_parent_theta_441']:
    r_records += [R / scope / 'REPORT.md', R / scope / 'REGISTRY.json']

missing_source_paths = [str(p) for p in primary_paths + read_reuse_paths + r_records if not p.exists()]
registry = {
    'reviewer': 'S28 / independent bank-H430-adopted-count review',
    'status': 'FINAL_CHECKPOINT_WHOLE_SCOPE_HOLD',
    'whole_assigned_yellow_scope_source_complete': False,
    'whole_assigned_yellow_scope_kernel_verified': False,
    'new_green_nodes': 0, 'formal_credit': 0,
    'verification_kind': 'read source/text/JSON and hash raw bytes only',
    'stop_boundary': 'Root checkpoint-only instruction after capacity error; no further mathematical research',
    'reviewed_S_sources': reviewed,
    'author_records': author_records,
    'missing_author_records_at_freeze': missing_author_records,
    'original_sources_read': [pin(p, 'original source/program read; program NOT executed')
                              for p in primary_paths if p.exists()],
    'actual_sources_read': [pin(p, 'actual source inspected in assigned review; full or relevant exact definitions')
                            for p in read_reuse_paths if p.exists()],
    'frozen_R_reuse_records': [pin(p, 'frozen R final scope/pin record; reused independent R27/R28 evidence')
                             for p in r_records if p.exists()],
    'missing_source_paths': missing_source_paths,
    'local_terminal_disposition': {
        'S16': {'terminal': 'ImbalancedChen.P2EnhancedBadAndShortCostAssembly.original_badGamma5_Gamma9_to_19_cost_theta',
                'scope': 'Original inclusive bad Gamma5 + Gamma9-19 ordinary costs, original true alpha and one positive marked Theta; Gamma20/21 existing separate suppliers',
                'review': 'Source-supported ordinary cost candidate; uncompiled. Does not supply PP/K/4 actual-count licence or original bank bases.'},
        'S17': {'terminals': ['W1_childWindow_sum', 'W2_singleton_window_sum', 'W2_pair_window_sum'],
                'scope': 'Exact W1 d*N half-open and W2 N-window strict-child/endpoint/old-prefix-repeat dictionaries',
                'review': 'Source-supported finite dictionaries; original parentWindow and physical ceiling remain primitive, actual ancestral count licence remains.'},
        'S18': {'terminals': ['ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget.immutable430_literal_absoluteCoefficientError',
                             'ImbalancedChen.Part5OriginalH430LiteralAbsoluteBudget.immutable430_literal_feedbackBudget'],
                'scope': 'All106 actions,802 polar atoms,actual430 predecessor arrays; coefficientwise absolute error and literal base difference retained',
                'review': 'Source-supported narrow absolute bank payment; full Member/proper-equality/base/Buchstab/nested441/h34 remain.'},
        'S23': {'terminals': ['ImbalancedChen.P2SeedOmegaOriginalNumerical.actualJ2omega_required_lower_bound',
                             'ImbalancedChen.P2SeedFeedbackOriginalNumerical.actual_lambda_gt_thirteen_hundredths'],
                'scope': 'Literal original real-functionals and Q80 interval certificate source routes',
                'review': 'All finite guards and endpoint decide bodies UNEVALUATED; actual analytic count seed and four rounds not supplied.'}},
    'whole_terminals_remaining': [
        'P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences delta for actual P2TableActionSourceOnly.h / Wu fixed family',
        'P5OriginalCoefficientArithmetic hstarts actual grouped starts count',
        'P5OriginalCoefficientArithmetic h34 actual U3+U4 count with H430 savings',
        'P5OriginalCoefficientArithmetic h5 actual savedL5 count',
        'P5OriginalCoefficientArithmetic h6 actual common selected mask retainedL6 count',
        'actual original enhanced1/50 count entrance, admitted lower-from-old-upper four-round analytic induction, adopted2327/100000',
        'full actual causal history/parent source and all proper/equality/inherit native mass layers',
        'all actual bases and Buchstab arithmetic costs; one nested441 common refinement before N0'],
    'classification': {
        'I': 'uncompiled imports/API/elaboration and finite decide evaluation; no local test performed',
        'II': 'new actual finite dictionaries, cost/atom conversions, coefficientwise estimates and numerical-functional certificate sources',
        'III': 'substantive unsupplied original history/count/family/base/common-realization links in current chain; no manuscript counterexample established'},
    'prohibited_shortcuts_not_accepted': ['target-equivalent licence fields', 'true-alpha reset',
        'discarding arithmetic knots or positive-mass equality/inherit strata', 'N-window replaced by N*oldProduct without repeat lane',
        'signed profile error treated as coefficientwise absolute error', 'current generation reading new array',
        'finite max N threshold treated as nested causal smooth realization'],
    'remote_evidence_required': {
        'lean': 'leanprover/lean4:v4.33.0-rc1',
        'mathlib': 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
        'goldbach': '09b97db5764ade1246bfb77206baa1b124760958',
        'source_binding': 'exact commit/tree and raw file hashes of terminal and transitive closure',
        'kernel': 'successful elaboration/kernel route and actual terminal transitive #print axioms',
        'scope': 'partial local pass gives no full yellow-node green; reuse reliable identical-source artifacts first'},
    'checks': {'local_lean': False, 'lake': False, 'build': False, 'proof_guard': False,
        'numerical_replay': False, 'git_mutation': False, 'remote_mutation': False,
        'author_edits': False, 'child_agents': False, 'quota_inspection': False},
    'report': pin(OUT / 'REPORT.md', 'independent final source review report'),
}
(OUT / 'REGISTRY.json').write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'reviewed_S_sources': len(reviewed), 'author_records': len(author_records),
                  'missing_author_records': missing_author_records, 'missing_source_paths': missing_source_paths}, ensure_ascii=False))
