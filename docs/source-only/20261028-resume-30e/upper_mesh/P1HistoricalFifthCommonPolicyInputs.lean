import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P5OriginalCommonRefinedConstructor
import Mathlib

/-!
The full original archive decoder is wired into the independently defined
TRUE common-refined third/fourth/fifth ancestor. SOURCE_ONLY / UNCOMPILED.
No equation with the old policy5 parent, or old B13-to-new-density transfer,
is inferred merely from sharing row names. Changed-parent prefixes remain
an explicit source obligation.
-/
namespace ImbalancedChen.P1HistoricalFifthCommonPolicyInputs
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1HistoricalFifthIndexedOwnerArchive
open P1OriginalFifthRawBoxSelectorEquivalence

/-- The constructor comes from the physical owner, independently of the
archive binding. Only its fifth data fields are now instantiated by the
full independently loaded archive and the actual licensed-owner filters.
The original fourth bank/licence remain explicit unmodified source data. -/
def sourceData (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) : P5OriginalCommonRefinedConstructor.OriginalData :=
  ⟨e, chi, refinedMesh q, omega, rows4, licensed4,
    globalOwners e q chi omega, licensedRows e q chi omega⟩

theorem original_fourth_inputs_preserved (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (sourceData rows4 licensed4 e q chi omega).rows4 = rows4 ∧
      (sourceData rows4 licensed4 e q chi omega).licensed4 = licensed4 := ⟨rfl, rfl⟩

theorem full_archive_licensed_rows_source (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ (sourceData rows4 licensed4 e q chi omega).rows5) :
    ∃ i ∈ licensedIndices, r.cell ∈ licensedOwners i e q chi omega ∧
      r = sourceOwnerRow i q r.cell ∧ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q) :=
  licensedRows_source_index e q chi omega r hr

/-- An actual source-index/mask candidate is eligible on its ORIGINAL
owner cell of the SAME global compiled source input. Both the physical
count and any eventual mean must keep these same data fields. -/
theorem archive_candidate_eligible (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (i : ArchiveIndex) (hi : i ∈ licensedIndices) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    eligible e chi (refinedMesh q) omega
      (sourceData rows4 licensed4 e q chi omega).J5 (sourceOwnerRow i q j) t := by
  have hjGlobal : j ∈ globalOwners e q chi omega := Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
  exact ⟨globalOwner_selected_buffer e q chi omega j hjGlobal,
    licensedOwner_gate_buffer i e q chi omega j hj, ht⟩

/-- The candidate enters the new finite maximum with its TRUE newly
shared fourth ancestor as seed. No old inherited exponent is substituted. -/
theorem archive_candidate_le_common_exponent5
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (i : ArchiveIndex) (hi : i ∈ licensedIndices) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    rawCandidate (e : ℝ) (archiveRow i) (primeHistoryLogCoordinates N 5 pre) ≤
      P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre := by
  have hr : sourceOwnerRow i q j ∈ licensedRows e q chi omega :=
    Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have hel := archive_candidate_eligible rows4 licensed4 i hi e q chi omega j hj _ ht
  have hb := finiteMax_row_le (licensedRows e q chi omega)
    (fun r => eligible e chi (refinedMesh q) omega (globalOwners e q chi omega) r
      (primeHistoryLogCoordinates N 5 pre))
    (fun r => candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre))
    (P5OriginalCommonRefinedConstructor.exponent4 (sourceData rows4 licensed4 e q chi omega)
      N (rosserAncestor 4 pre)) (sourceOwnerRow i q j) hr hel
  simpa only [rawCandidate_eq_candidate, sourceOwnerRow, sourceData,
    P5OriginalCommonRefinedConstructor.exponent5, if_pos hlen] using hb

/-- Sixth/eighth update chronology preserves the TRUE new common fifth
queries. This is deliberately not an equality with the old source policy5. -/
theorem common_policy8_through_sixth (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (positive : Bool) (pre : List ℕ)
    (hlen : pre.length ≤ 6) :
    P5OriginalCommonRefinedConstructor.policy8 (sourceData rows4 licensed4 e q chi omega) N positive pre =
      P5OriginalCommonRefinedConstructor.policy5 (sourceData rows4 licensed4 e q chi omega) N positive pre := by
  have h8 : pre.length ≤ 8 := hlen.trans (by decide)
  simp [P5OriginalCommonRefinedConstructor.policy8,
    P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
    P5OriginalAdoptedEighthPhysicalMasks.parentPolicy,
    P4AOriginalEighthParentPhysicalLedger.parentPolicy,
    P4AActualSixthFrozenEighthAdmission.sixthPolicy,
    firstExitDepthSplicePolicy, hlen, h8]

/-- A physical rank-five query uses THIS archive-bound common maximum,
not a similarly named old policy or a constant saved parent. -/
theorem actual_archive_common_fifth_test (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    P5OriginalCommonRefinedConstructor.policy8 (sourceData rows4 licensed4 e q chi omega) N false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (N ^ P5OriginalCommonRefinedConstructor.exponent5
          (sourceData rows4 licensed4 e q chi omega) N pre) pre) := by
  rw [common_policy8_through_sixth rows4 licensed4 e q chi omega N false pre (by omega)]
  simp [P5OriginalCommonRefinedConstructor.policy5, firstExitDepthSplicePolicy, hlen,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, rosserAncestor, P5OriginalCommonRefinedConstructor.level5]

/-- Prefixes on which the old source inherited fourth exponent differs
from the new actual common ancestor. Their effect is NOT silently zero. -/
def changedParentPrefixes (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) : Set (List ℕ) :=
  {pre | pre.length = 5 ∧
    P5OriginalCommonRefinedConstructor.exponent4 (sourceData rows4 licensed4 e q chi omega)
      N (rosserAncestor 4 pre) ≠
        inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre}

/-- Off the explicit changed-parent remainder the TWO independently
defined finite maxima agree: same original rows/licences/masks and a
proved equal inherited seed. This is not an assumed global policy identity. -/
theorem common_exponent5_eq_old_off_changed_parent
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (hnot : pre ∉ changedParentPrefixes rows4 licensed4 e q chi omega N) :
    P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) pre := by
  have hseed : P5OriginalCommonRefinedConstructor.exponent4
      (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre) =
        inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre := by
    by_contra h
    exact hnot ⟨hlen, h⟩
  simp only [P5OriginalCommonRefinedConstructor.exponent5, sourceData,
    P1OriginalVariableFifthContinuation.exponent5, if_pos hlen]
  rw [hseed]

end
end ImbalancedChen.P1HistoricalFifthCommonPolicyInputs
