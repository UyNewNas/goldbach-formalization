#!/usr/bin/env python3
"""Reconstruct the authorized P2.6 source overlay; never invoke Lean or a remote job."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
from fractions import Fraction

BASE = '298670f119d24874b719facb3ef756f1e01223a1'
PRE_RESET_SOURCE = '/workspace/scratch/cba105ac8c38/goldbach-p1'
MOVED = [
    'P4AOriginalCommonArchiveSchedule',
    'P4AOriginalArchiveFourteenPositivePresieve',
    'P4AOriginalCompleteSixthChronology',
    'P4AOriginalFull87SourceDispatch',
    'P4AOriginalFull87ActualCommonHistory',
    'P4AOriginalNewFifthUnion',
]
REFERENCES = [
    'P4AOriginalFull87ArchivedIntegralRows',
    'P4AOriginalFull87UnionActualGain',
    'P4AOriginalFull87SourcePrimeTests',
    'P4AOriginalFull87SourceDictionary',
    'P4AOriginalFull87EighthKernelControl',
    'P2OriginalSaving19OwnedIntegral',
    'P2OriginalSaving19SourceMeasure',
]
NEW_FILES = {
'P4AOriginalCommonArchiveScheduleData': '''import ImbalancedChen.P4AOriginalCausalHistory

/-!
The unchanged finite archive schedule constructor, separated from the
fourteen-family analytic endpoint. The public namespace and definition
are preserved from the original source.

SOURCE CANDIDATE / NOT COMPILED.
-/
namespace ImbalancedChen.P4AOriginalCommonArchiveSchedule
noncomputable section
open P4AOriginalCausalHistory
open P2OriginalFourthCapProducerInterface

/-- No N occurs in these finite fields. All third decisions read the
original first-three label; fourth and fifth rows stay at their own ranks. -/
def fixedSchedule (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  ⟨rows4, licensed4, e, q, (e : ℝ) / 20, omega⟩

end
end ImbalancedChen.P4AOriginalCommonArchiveSchedule
''',
'P4AOriginalArchiveFourteenData': '''import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P4AOriginalCommonArchiveScheduleData

/-!
The unchanged original fourth/fifth archive data used by the common
history and complete-sixth chronology. These declarations keep their
original public namespace and bodies; the fourteen-family numerical
endpoint remains in its original consumer module.

SOURCE CANDIDATE / NOT COMPILED.
-/
namespace ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
noncomputable section
open P5OriginalCommonRefinedConstructor
open P5OriginalFourthFifthSourceInputs
open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule
open P5OriginalCommonFourthFallbackExcision P5OriginalCommonFourthSourceNavigation

/-- The same pre-N archive schedule with the actual fourth bank. -/
def schedule (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  fixedSchedule originalRows4 originalAdmission4 e q omega

def data (e : ℚ) (q : ℕ) (omega : ℝ) : OriginalData :=
  (schedule e q omega).data

theorem data_eq_original_heldData (e : ℚ) (q : ℕ) (omega : ℝ) :
    data e q omega = heldData e q ((e : ℝ) / 20) omega := rfl

/-- Geometry follows from the actual admission test. -/
theorem actual_fourth_geometry (e : ℚ) (q : ℕ) (omega : ℝ) :
    FourthGeometry (data e q omega) := by
  intro r _hr hlicense
  exact originalAdmission4_geometry r hlicense

end
end ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
''',
'P2OriginalSaving19ActualEndpoint': '''import ImbalancedChen.P2OriginalSaving19OwnedIntegral
import ImbalancedChen.P4AOriginalFull87UnionActualGain

/-!
The original thirteen-cell saving on the existing common fifth-bank union.
The original 28,918-row Q96 endpoint is reused through selectedSaving.
The thirteen strict source integrals are identified with their original
ascendingPair entries before inclusion in the nonnegative full source sum.
The ordinary and positive-presieve consumers keep the original policies
and the original order of all pre-target choices.

SOURCE CANDIDATE / NOT COMPILED.
-/
namespace ImbalancedChen.P2OriginalSaving19ActualEndpoint
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory
open VariableEnvelope (mu)
open OriginalAscendingThirteenCellOwnership (cell)
open P2OriginalThirdMinorantLogDictionarySourceOnly (conservativeDensity)
open P2OriginalSaving19SourceMeasure (selectedSaving selectedSaving_eq_sum_cells)
open P2OriginalSaving19OwnedIntegral (original_endpoint_le_selectedSaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87StrictActionTrim (sourceSet sourceSet_measurable)
open P4AOriginalFull87EighthKernelControl (kernel_bounds)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalVariableFifthPhysicalLedger (raw physical)
open P5OriginalCommonPositivePresieve (normalize)

/-- The unchanged replacement endpoint of the original moment archive. -/
abbrev q19 : ℝ := (283388722705335806564439 : ℝ) / (2 : ℝ)^96

private theorem source19 (i : Fin 13) : sourceSet (.ascendingPair i) = cell i := by
  ext t
  exact OriginalAscendingThirteenExportOwnershipJoin.strictExportedRows_iff_StrictRows i t

/-- The original source dictionary uses exactly the thirteen-cell density. -/
theorem original_cell_integral (i : Fin 13) :
    cellIntegral (.ascendingPair i) = ∫ t in cell i, conservativeDensity t := by
  change (∫ t in sourceSet (.ascendingPair i), conservativeDensity t) = _
  rw [source19]

/-- Exact source attribution precedes the comparison with the full sum. -/
theorem selectedSaving_eq_original_cell_sum :
    selectedSaving = ∑ i : Fin 13, cellIntegral (.ascendingPair i) := by
  rw [selectedSaving_eq_sum_cells]
  exact Finset.sum_congr rfl (fun i _ => (original_cell_integral i).symm)

theorem original_q96_le_original_cell_sum :
    q19 ≤ ∑ i : Fin 13, cellIntegral (.ascendingPair i) := by
  rw [← selectedSaving_eq_original_cell_sum]
  exact original_endpoint_le_selectedSaving

/-- Every additional source integral is nonnegative; no other numerical
certificate or saved-gain aggregate enters this comparison. -/
theorem selectedSaving_le_full_source :
    selectedSaving ≤ ∑ c : Cell, cellIntegral c := by
  have hnonneg (c : Cell) : 0 ≤ cellIntegral c := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact (kernel_bounds ht).1
  have hinj : Function.Injective Cell.ascendingPair := by
    intro i j hij
    cases hij
    rfl
  let A : Finset Cell := Finset.univ.image Cell.ascendingPair
  have hA : ∑ c ∈ A, cellIntegral c =
      ∑ i : Fin 13, cellIntegral (.ascendingPair i) :=
    Finset.sum_image (fun i _ j _ hij => hinj hij)
  rw [selectedSaving_eq_original_cell_sum, ← hA]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    (fun c _ _ => hnonneg c)

theorem original_q96_le_full_source : q19 ≤ ∑ c : Cell, cellIntegral c :=
  original_endpoint_le_selectedSaving.trans selectedSaving_le_full_source

/-- Slot 19 in the 2026-11-06 table is rounded down from the Q96 endpoint. -/
theorem paper_saving_le_q19 : (357686854 : ℝ) / (10 : ℝ)^14 ≤ q19 := by
  norm_num [q19]

theorem paper_saving_le_selectedSaving :
    (357686854 : ℝ) / (10 : ℝ)^14 ≤ selectedSaving :=
  paper_saving_le_q19.trans original_endpoint_le_selectedSaving

/-- The original Q96 saving is earned on the existing actual sixth-to-eighth
splice. The trim, finite cap, rational precision and common mesh precede N. -/
theorem exists_ordinary_q96_gain (eps : ℝ) (heps : 0 < eps) :
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      q19 - eps <
        normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
          raw (policy (width r) n e q om (N : ℝ)) N cap 0 z) := by
  obtain ⟨r0,hr⟩ := P4AOriginalFull87UnionActualGain.exists_ordinary_source_gain eps heps
  refine ⟨r0,?_⟩
  intro r hr0
  obtain ⟨n0,hn⟩ := hr r hr0
  refine ⟨n0,?_⟩
  intro n hn0
  obtain ⟨e0,he0,he⟩ := hn n hn0
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨N0,hN0,hN⟩ := hq q hqq om hom
  refine ⟨N0,hN0,?_⟩
  intro N hNN hEven cap z hz hcap
  exact (sub_le_sub_right original_q96_le_full_source eps).trans_lt
    (hN N hNN hEven cap z hz hcap)

/-- A single positive-presieve projection on the same complete new tree,
with its own ordinary sixth parent and the original Q96 replacement. -/
theorem exists_positive_presieve_q96_gain (nu eps betaMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
      beta^2 ≤ (19/96 : ℝ)/nu ∧
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ cap : ℕ, (N : ℝ)^(19/96 : ℝ) ≤ cap →
      let w := (N : ℝ)^(nu * beta^2)
      let z := (N : ℝ)^(19/96 : ℝ)
      let L := (N : ℝ)^(nu * beta)
      1 < w ∧ w ≤ z ∧
      normalize N (physical
        (policy (width r) n e q om (N : ℝ)) N cap w z L) <
        normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z) -
          q19 + eps := by
  obtain ⟨beta,hb,hb8,hbMax,hbr,r0,hr⟩ :=
    P4AOriginalFull87UnionActualGain.exists_positive_presieve_source_gain
      nu eps betaMax hnu heps hMax
  refine ⟨beta,hb,hb8,hbMax,hbr,r0,?_⟩
  intro r hr0
  obtain ⟨n0,hn⟩ := hr r hr0
  refine ⟨n0,?_⟩
  intro n hn0
  obtain ⟨e0,he0,he⟩ := hn n hn0
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨N0,hN0,hN⟩ := hq q hqq om hom
  refine ⟨N0,hN0,?_⟩
  intro N hNN hEven cap hcap
  obtain ⟨hw,hwz,hcost⟩ := hN N hNN hEven cap hcap
  exact ⟨hw,hwz,hcost.trans_le
    (add_le_add_right (sub_le_sub_left original_q96_le_full_source _) _)⟩

end
end ImbalancedChen.P2OriginalSaving19ActualEndpoint
''',
}

PRIOR_COUNTS = {
    'P4AOriginalFull87ActualCommonHistory': [813, 653],
    'P4AOriginalFull87UnionHistory': [953, 737],
    'P4AOriginalFull87UnionActualGain': [955, 739],
    'P4AOriginalFull87ActualSavedEndpoint': [1988, 1794],
    'UnionActualGain + Saving19OwnedIntegral': [959, 757],
    'P2OriginalSaving19ActualEndpoint': [None, 758],
}
EXCLUDED = [
    'P2OriginalSaving16OwnedIntegral', 'P2OriginalSaving16OriginalArchive',
    'P2OriginalSaving17DescendingIntegral', 'P2OriginalFirstIntegralEndpoint',
    'P2OriginalCertificateBudgetAssembly', 'P4AOriginalFull87SavedGain',
    'P4AOriginalFull87ActualSavedEndpoint', 'P4AOriginalFull87ArchivedIntegralRows',
    'P4AOriginalFull87ArchiveSourceIndex',
]

def sha(blob):
    return hashlib.sha256(blob).hexdigest()

def git_blob(blob):
    return hashlib.sha1(('blob '+str(len(blob))+'\0').encode()+blob).hexdigest()

def imports(text):
    return [tok[15:] for line in text.splitlines() if line.startswith('import ')
            for tok in line.split()[1:] if tok.startswith('ImbalancedChen.')]

def closure(roots, graph):
    seen = set()
    todo = list(roots)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(graph.get(name, []))
    return seen

def statement(text, name):
    start = text.index('theorem '+name+' ')
    return text[start:text.index(' := by', start)]

def replace_once(blob, old, new):
    assert blob.count(old) == 1, old
    return blob.replace(old, new, 1)

def without_imports(blob):
    return b''.join(line for line in blob.splitlines(keepends=True)
                    if not line.startswith(b'import '))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    out = args.output
    (out/'ImbalancedChen').mkdir(parents=True, exist_ok=True)
    candidate = {name: text.encode() for name, text in NEW_FILES.items()}
    for name, blob in candidate.items():
        (out/'ImbalancedChen'/(name+'.lean')).write_bytes(blob)
    if args.source_root is None:
        (out/'RECOVERY_STATUS.json').write_text(json.dumps({
            'status': 'three_new_modules_restored; baseline_modules_pending_source_root',
            'base_commit': BASE, 'prior_source_root': PRE_RESET_SOURCE,
            'prior_full_static_audit_passed': True,
            'prior_git_apply_check_exit_code': 0,
            'prior_counts': PRIOR_COUNTS,
            'compiled': False, 'remote_jobs_started': False,
            'resume': 'python recover_history.py --source-root <restored-P1-root>',
        }, indent=2)+'\n')
        print(json.dumps({'new_modules_written': len(candidate), 'output': str(out),
                          'need_source_root': True}, indent=2))
        return
    src = args.source_root.resolve()
    old = {}
    sources = []
    for name in MOVED + REFERENCES:
        rel = Path('ImbalancedChen')/(name+'.lean')
        blob = (src/rel).read_bytes()
        proc = subprocess.run(['git', 'show', BASE+':'+str(rel)], cwd=src,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        commit_verified = proc.returncode == 0
        if commit_verified:
            assert proc.stdout == blob, 'source differs from requested commit: '+str(rel)
        old[name] = blob
        sources.append({'module': name, 'source_path': str(src/rel),
                        'repository_path': str(rel), 'base_commit': BASE,
                        'sha256': sha(blob), 'git_blob': git_blob(blob),
                        'verified_against_git_commit': commit_verified,
                        'bytes': len(blob), 'copied_for_patch': name in MOVED})
    a = old[MOVED[0]]
    fixed = a[a.index(b'/-- No N occurs in these finite fields.'):
              a.index(b'/-- This record is a conclusion, never a common-history premise. -/')]
    b = old[MOVED[1]]
    bank = b[b.index(b'/-- The same pre-N archive schedule with the actual fourth bank. -/'):
             b.index(b'/-- Literal fourteen-family tree on this same actual policy6 parent.')]
    assert fixed in candidate['P4AOriginalCommonArchiveScheduleData']
    assert bank in candidate['P4AOriginalArchiveFourteenData']
    for name in MOVED:
        blob = old[name]
        if name == MOVED[0]:
            blob = replace_once(blob, fixed, b'')
            old_import = b'import ImbalancedChen.P4AOriginalCausalHistory\n'
            blob = replace_once(blob, old_import, old_import+b'import ImbalancedChen.P4AOriginalCommonArchiveScheduleData\n')
        elif name == MOVED[1]:
            blob = replace_once(blob, bank, b'')
            old_import = b'import ImbalancedChen.P5OriginalFourthFifthSourceInputs\n'
            blob = replace_once(blob, old_import, old_import+b'import ImbalancedChen.P4AOriginalArchiveFourteenData\n')
        elif name in MOVED[2:4]:
            blob = replace_once(blob, b'import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve',
                                b'import ImbalancedChen.P4AOriginalArchiveFourteenData')
        elif name == MOVED[4]:
            blob = replace_once(blob, b'import ImbalancedChen.P4AOriginalCommonArchiveSchedule\n', b'')
        elif name == MOVED[5]:
            blob = replace_once(blob, b'import ImbalancedChen.P4AOriginalNewFifthExclusion\n',
                                b'import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs\n')
        candidate[name] = blob
        (out/'ImbalancedChen'/(name+'.lean')).write_bytes(blob)
    checks = []
    rewrites = []
    for name in MOVED:
        expected = old[name]
        if name == MOVED[0]: expected = replace_once(expected, fixed, b'')
        if name == MOVED[1]: expected = replace_once(expected, bank, b'')
        assert without_imports(expected) == without_imports(candidate[name]), name
        checks.append({'module': name, 'non_import_body_preserved': True,
                       'crlf_preserved': old[name].count(b'\r\n') == candidate[name].count(b'\r\n')})
        before = imports(old[name].decode()); after = imports(candidate[name].decode())
        rewrites.append({'module': name, 'removed': [n for n in before if n not in after],
                         'added': [n for n in after if n not in before]})
    archived = old['P4AOriginalFull87ArchivedIntegralRows']
    start = archived.index(b'private theorem source19 ')
    source19 = archived[start:archived.index(b'\ntheorem original19_archived_cell_le_integral', start)]
    glue = candidate['P2OriginalSaving19ActualEndpoint']
    assert source19 in glue
    statement_checks = {}
    for old_name, new_name in [('exists_ordinary_source_gain', 'exists_ordinary_q96_gain'),
                              ('exists_positive_presieve_source_gain', 'exists_positive_presieve_q96_gain')]:
        s = statement(old['P4AOriginalFull87UnionActualGain'].decode(), old_name)
        s = s.replace(old_name, new_name).replace('(∑ c : Cell, cellIntegral c)', 'q19')
        s = s.replace('P4AOriginalVariableFifthPhysicalLedger.physical', 'physical')
        assert ' '.join(s.split()) == ' '.join(statement(glue.decode(), new_name).split())
        statement_checks[new_name] = True
    token_pattern = r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b'
    assert not [(name, m.group()) for name, blob in candidate.items()
                for m in re.finditer(token_pattern, blob.decode())]
    patch = []
    for name in sorted(candidate):
        rel = 'ImbalancedChen/'+name+'.lean'
        before = old.get(name, b'')
        patch.extend(difflib.diff_bytes(difflib.unified_diff,
            before.splitlines(keepends=True), candidate[name].splitlines(keepends=True),
            fromfile=('a/'+rel).encode() if before else b'/dev/null', tofile=('b/'+rel).encode()))
    (out/'candidate.patch').write_bytes(b''.join(patch))
    patch_check = subprocess.run(['git', 'apply', '--check', '--whitespace=error-all',
                                 str(out.resolve()/'candidate.patch')], cwd=src,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    graph0 = {str(f.relative_to(src/'ImbalancedChen').with_suffix('')).replace('/', '.'):
              imports(f.read_text()) for f in (src/'ImbalancedChen').rglob('*.lean')}
    graph1 = dict(graph0)
    graph1.update({name: imports(blob.decode()) for name, blob in candidate.items()})
    roots = [['P4AOriginalFull87ActualCommonHistory'], ['P4AOriginalFull87UnionHistory'],
             ['P4AOriginalFull87UnionActualGain'], ['P4AOriginalFull87ActualSavedEndpoint'],
             ['P4AOriginalFull87UnionActualGain', 'P2OriginalSaving19OwnedIntegral'],
             ['P2OriginalSaving19ActualEndpoint']]
    closures = []
    for group in roots:
        after = closure(group, graph1)
        before = closure(group, graph0) if all(n in graph0 for n in group) else None
        closures.append({'roots': group, 'candidate_modules': len(after),
                         'baseline_modules': None if before is None else len(before),
                         'missing_modules': sorted(n for n in after if n not in graph1)})
    endpoint = closure(['P2OriginalSaving19ActualEndpoint'], graph1)
    assert not endpoint.intersection(EXCLUDED)
    (out/'ENDPOINT_DEPENDENCIES.txt').write_text('\n'.join('ImbalancedChen.'+n for n in sorted(endpoint))+'\n')
    q = Fraction(283388722705335806564439, 2**96)
    paper = Fraction(357686854, 10**14)
    assert paper <= q
    manifest = {'base_commit': BASE, 'source_root': str(src), 'sources': sources}
    (out/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
    audit = {'compiled': False, 'remote_jobs_started': False,
             'moved_blocks_byte_identical': True,
             'moved_block_sha256': {'fixedSchedule': sha(fixed), 'actual_bank': sha(bank)},
             'original_module_checks': checks, 'import_rewrites': rewrites,
             'source19_byte_identical': True, 'source19_sha256': sha(source19),
             'endpoint_statement_checks': statement_checks, 'forbidden_token_hits': [],
             'dependency_closures': closures, 'prior_full_tree_counts': PRIOR_COUNTS,
             'excluded_from_endpoint': EXCLUDED,
             'git_apply_check': {'exit_code': patch_check.returncode,
                                 'stdout': patch_check.stdout, 'stderr': patch_check.stderr},
             'q19': str(q), 'paper_slot_19': str(paper), 'q19_minus_paper': str(q-paper),
             'candidate_files': [{'path': str(out/'ImbalancedChen'/(n+'.lean')),
                                  'sha256': sha(blob), 'bytes': len(blob)}
                                 for n, blob in sorted(candidate.items())]}
    (out/'STATIC_AUDIT.json').write_text(json.dumps(audit, indent=2)+'\n')
    source_rows = '\n'.join('| `'+r['module']+'` | `'+r['sha256']+'` |' for r in sources)
    report = '''# P2.6 history and Q96 endpoint candidate

## Delivery

This is a nine-file Lean source overlay against commit `'''+BASE+'''`:
two new lightweight modules, six original modules with only approved declaration
moves/import changes, and `P2OriginalSaving19ActualEndpoint`.

The first completed overlay and its static audit were created before the executor
reset. This script reconstructs the same candidate from the tool record and the
restored P1 snapshot. No Lean compilation or remote job was started. These are
uncompiled candidates with no kernel acceptance credit.

## Preserved declarations

`P4AOriginalCommonArchiveScheduleData` keeps the original namespace and exact body
of `P4AOriginalCommonArchiveSchedule.fixedSchedule`.

`P4AOriginalArchiveFourteenData` keeps the original namespace and exact bodies of
`schedule`, `data`, `data_eq_original_heldData`, and `actual_fourth_geometry` from
`P4AOriginalArchiveFourteenPositivePresieve`.

The old owner modules import these definitions. `CompleteSixthChronology` and
`Full87SourceDispatch` import the actual-data module. `ActualCommonHistory` drops
its unused direct common-schedule consumer import. `NewFifthUnion` imports the
actual `P1HistoricalFifthCommonPolicyInputs` supplier directly.

Every unchanged declaration and proof body in the six old modules is compared
byte-for-byte after removing import lines and exactly the authorized moved blocks.
Original line endings are preserved.

## Saving19 glue

`q19` is exactly `283388722705335806564439 / 2^96`. The public results are:

- `original_cell_integral`;
- `selectedSaving_eq_original_cell_sum`;
- `original_q96_le_original_cell_sum`;
- `selectedSaving_le_full_source`;
- `original_q96_le_full_source`;
- `paper_saving_le_q19` and `paper_saving_le_selectedSaving`;
- `exists_ordinary_q96_gain`;
- `exists_positive_presieve_q96_gain`.

The private `source19` proof is reused byte-for-byte from `ArchivedIntegralRows`;
that heavy module is not imported. The original 28,918-row theorem supplies the
Q96 value. The thirteen-cell identity comes before inclusion in the nonnegative
full source sum. No other family numerical bound is used.

The ordinary and positive statements match `UnionActualGain` after only replacing
the full integral sum by `q19`, renaming the theorem, and shortening the opened
`physical` identifier. All target-independent choice quantifiers, beta conditions,
cutoffs, and actual policies are unchanged. Positive projection is still on one
complete new tree, with its same actual ordinary sixth parent.

## Dependency result

The pre-reset complete source graph, with no missing modules, gave:

| Root | Baseline | Candidate |
|---|---:|---:|
| ActualCommonHistory | 813 | 653 |
| UnionHistory | 953 | 737 |
| UnionActualGain | 955 | 739 |
| UnionActualGain plus Saving19OwnedIntegral | 959 | 757 |
| New actual endpoint including itself | — | 758 |
| Heavy ActualSavedEndpoint, not used | 1988 | 1794 |

`STATIC_AUDIT.json` separately reports the newly restored source graph and any
missing modules, so sparse-source counts cannot be mistaken for a complete graph.
The complete endpoint excludes Saving16OwnedIntegral/OriginalArchive,
Saving17DescendingIntegral, FirstIntegralEndpoint, CertificateBudgetAssembly,
Full87SavedGain, ActualSavedEndpoint, ArchivedIntegralRows and ArchiveSourceIndex.
The actual common-history and source-geometry suppliers remain.

## Manuscript and remaining gate

The 2026-11-06 manuscript source pin is
`a988cba584d803ae2856a0de50efb582f4f3dd6a`, under `paper/release-20261106/en/`.
`numerical-appendix.tex` label `num:simplex-moment` (line 188) gives the unchanged
moment law; slot 19 (line 270) gives `357686854 / 10^14`.
`argument.tex` label `eq:current-eighth-saving` supplies the unchanged current-parent
density semantics used by the existing analytic supplier.

This is a module-boundary change plus explicit source-index glue. The remaining
gate is actual Lean compilation together with the existing moment/ownership and
actual-history suppliers. Static checks and patch applicability are not kernel
proofs. `candidate.patch` is intended for the specified source snapshot; the main
worktree and all remote queues remain untouched by this script.

## Source SHA-256

Absolute paths and Git blob IDs are in `SOURCE_MANIFEST.json`.

| Source module | SHA-256 |
|---|---|
'''+source_rows+'\n'
    (out/'REPORT.md').write_text(report)
    (out/'RECOVERY_STATUS.json').write_text(json.dumps({'status': 'nine_modules_restored',
        'base_commit': BASE, 'source_root': str(src), 'compiled': False,
        'all_sources_git_verified': all(r['verified_against_git_commit'] for r in sources),
        'patch_check_exit_code': patch_check.returncode}, indent=2)+'\n')
    print(json.dumps({'candidate_modules': len(candidate), 'output': str(out),
                      'patch_check_exit_code': patch_check.returncode,
                      'all_sources_git_verified': all(r['verified_against_git_commit'] for r in sources),
                      'closures': closures}, indent=2))

if __name__ == '__main__':
    main()
