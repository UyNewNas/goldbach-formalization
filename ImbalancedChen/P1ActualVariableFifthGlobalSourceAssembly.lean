import ImbalancedChen.P1ActualVariableFifthGlobalSourceDefinitions
import ImbalancedChen.P1ActualVariableFifthProfiles

/-!
Exact global ACTUAL variable-fifth source assembly on original T3.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.
Selected owner cells partition the nonzero variable5-minus-ACTUAL-old4
charge. Outside those owners the fifth finite maximum equals its actual
fourth seed and the two literal own-cube residuals cancel exactly.
No D, stored cap, owned-row premise or old4 substitution is used.
-/

namespace ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1OriginalFifthWeightedSourceReduction
open P1OriginalCoarseFifthContinuation

section Source
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m)) (rows5 : Finset (FifthRow m))

/-- The independently written cell dictionary uses the same literal actual
source. This is definitional identification, not a replacement by a stored
or coarse residual. -/
theorem tupleDifference_eq_profile_literal (N cap : ℕ) (p : Fin 5 → ℕ) :
    tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p =
      P1ActualVariableFifthProfiles.literalTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap p := rfl

theorem tupleDifference_outside (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p = 0 := by
  rw [tupleDifference_eq_profile_literal]
  exact P1ActualVariableFifthProfiles.literalTupleCharge_outside
    e chi m omega rows4 licensed4 J5 rows5 N cap p hout

/-- All nonzero charge is partitioned by its unique half-open original
selected owner. A cell with no eligible fifth row cancels against its seed. -/
theorem tupleDifference_eq_selected_owner_sum (N cap : ℕ) (p : Fin 5 → ℕ) :
    tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0 := by
  by_cases hex : ∃ j ∈ selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [if_pos ht]
    · intro q _hq hqj
      apply if_neg
      intro hq
      exact hqj (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hq ht)
  · have hout : ∀ j ∈ selectedFifthCells e chi m omega J5,
        actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j := by
      simpa only [not_exists, not_and] using hex
    rw [tupleDifference_outside e chi m omega rows4 licensed4 J5 rows5 N cap p hout]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hout j hj))

/-- Finite sum exchange retains ALL original rank-four next candidates,
including those rejected by the actual old4 own-cube test. -/
theorem fullTupleCharge_eq_selected_fullCells (N cap : ℕ) :
    fullTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        fullCellCharge e chi m omega rows4 licensed4 J5 rows5 N cap j := by
  unfold fullTupleCharge fullCellCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [tupleDifference_eq_selected_owner_sum e chi m omega rows4 licensed4 J5 rows5 N cap p,
    Finset.mul_sum]

/-- Exact positive/small partition of one actual signed cell source. -/
theorem fullCellCharge_eq_positive_add_small (a : ℝ) (N cap : ℕ)
    (j : P1OriginalVariableFifthContinuation.Label5 m) :
    fullCellCharge e chi m omega rows4 licensed4 J5 rows5 N cap j =
      positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N cap j +
        smallCellRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap j := by
  unfold fullCellCharge positiveCellCharge smallCellRemainder
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hlarge : ∀ i, a ≤ actualPrimeTupleLog N p i
  · have hsmall : ¬ ∃ i, actualPrimeTupleLog N p i < a := by
      rintro ⟨i, hi⟩
      exact (not_lt_of_ge (hlarge i)) hi
    simp only [if_pos hlarge, if_neg hsmall, add_zero]
  · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
      push_neg at hlarge
      exact hlarge
    simp only [if_neg hlarge, if_pos hsmall, zero_add]

/-- Entire actual variable-fifth saving, with canonical signed small source.
The h45 comparison is structural in the actual finite maximum and no stored
checker or independent desired density identity is assumed. -/
theorem normalizedSaving_eq_positive_add_smallRemainder (a : ℝ) (N cap : ℕ) :
    normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N cap =
      positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N cap +
        smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap := by
  rw [normalizedSaving_eq_fullTupleCharge, fullTupleCharge_eq_selected_fullCells]
  unfold positiveCharge smallRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact fullCellCharge_eq_positive_add_small e chi m omega rows4 licensed4 J5 rows5 a N cap j

/-- Canonical small source with its last-coordinate formulation. -/
def terminalCellRemainder (a : ℝ) (N cap : ℕ) (j : P1OriginalVariableFifthContinuation.Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter (fun p => actualPrimeTupleLog N p (Fin.last 4) < a),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

/-- Same actual signed tuple difference on delta <= t5 < a. -/
def signedShellCell (delta a : ℝ) (N cap : ℕ) (j : P1OriginalVariableFifthContinuation.Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter (fun p =>
      delta ≤ actualPrimeTupleLog N p (Fin.last 4) ∧ actualPrimeTupleLog N p (Fin.last 4) < a),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

def signedShell (delta a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    signedShellCell e chi m omega rows4 licensed4 J5 rows5 delta a N cap j

/-- Strict source order is inherited from the actual descending prime
carrier; it does not require either own-cube gate or an adequate cap. -/
theorem source_log_strictAnti (N cap : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ)
    (hp : p ∈ sourceCarrier e chi m omega N cap) : StrictAnti (actualPrimeTupleLog N p) := by
  have hd := (mem_firstExitFrontierTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeUniverse_prime (hd.2.1 i)).pos
  exact (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr hd.1

theorem smallCellRemainder_eq_terminal (a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (j : P1OriginalVariableFifthContinuation.Label5 m) :
    smallCellRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap j =
      terminalCellRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap j := by
  have hfilters : (sourceCarrier e chi m omega N cap).filter (fun p => ∃ i, actualPrimeTupleLog N p i < a) =
      (sourceCarrier e chi m omega N cap).filter (fun p => actualPrimeTupleLog N p (Fin.last 4) < a) := by
    ext p
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hp
    have hanti := source_log_strictAnti e chi m omega N cap hN p hp
    constructor
    · rintro ⟨i, hi⟩
      exact (hanti.antitone (Fin.le_last i)).trans_lt hi
    · intro hl
      exact ⟨Fin.last 4, hl⟩
  unfold smallCellRemainder terminalCellRemainder
  rw [hfilters]

theorem smallCellRemainder_split (delta a : ℝ) (hda : delta ≤ a)
    (N cap : ℕ) (hN : 1 < N) (j : P1OriginalVariableFifthContinuation.Label5 m) :
    smallCellRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap j =
      smallCellRemainder e chi m omega rows4 licensed4 J5 rows5 delta N cap j +
        signedShellCell e chi m omega rows4 licensed4 J5 rows5 delta a N cap j := by
  rw [smallCellRemainder_eq_terminal e chi m omega rows4 licensed4 J5 rows5 a N cap hN j,
    smallCellRemainder_eq_terminal e chi m omega rows4 licensed4 J5 rows5 delta N cap hN j]
  unfold terminalCellRemainder signedShellCell
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hd : actualPrimeTupleLog N p (Fin.last 4) < delta
  · have ha := hd.trans_le hda
    have hnd : ¬ delta ≤ actualPrimeTupleLog N p (Fin.last 4) := not_le_of_gt hd
    simp only [if_pos hd, if_pos ha, hnd, false_and, if_false, add_zero]
  · have hdl : delta ≤ actualPrimeTupleLog N p (Fin.last 4) := le_of_not_gt hd
    by_cases ha : actualPrimeTupleLog N p (Fin.last 4) < a <;> simp [hd, hdl, ha]

theorem smallRemainder_split (delta a : ℝ) (hda : delta ≤ a) (N cap : ℕ) (hN : 1 < N) :
    smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap =
      smallRemainder e chi m omega rows4 licensed4 J5 rows5 delta N cap +
        signedShell e chi m omega rows4 licensed4 J5 rows5 delta a N cap := by
  unfold smallRemainder signedShell
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact smallCellRemainder_split e chi m omega rows4 licensed4 J5 rows5 delta a hda N cap hN j

end Source
end
end ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
