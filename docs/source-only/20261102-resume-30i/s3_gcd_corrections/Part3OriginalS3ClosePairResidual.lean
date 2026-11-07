import ImbalancedChen.Part3OriginalS3ClosePairPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The remaining sources are independently defined filters of the ORIGINAL
off-diagonal full-indicator sum. The exact source identity, not a supplied
corrected-carrier equality, inserts the new close payment into the unchanged
actualResidualFunctional. Every original Fourier/rough/S2 correction is
displayed. The large-shift complement and the far physical centred packet
are NOT estimated here. In particular the latter still contains the
unperformed close/gcd zero-mode restoration and Fourier disintegration.
-/
namespace ImbalancedChen.Part3.OriginalS3ClosePairResidual20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairPayment20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumDeletedIndicatorShift20261028 MediumGlobalDyadicOwnership20261028
open MediumActualDiagonalDivisorPayment20261028 MediumActualRestorationPayment20261028
open MediumOriginalRestorationLedger20261102 MediumOriginalAllKeyRestorationPayment20261102
open MediumReceiverCutoffArithmetic20261028 MediumActualS3ZeroCentering20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028 OriginalCompleteS123Ledger20261028
open OriginalSamePsiS1OwnedAtlas OriginalS1OuterCauchy20261028
open ActualMediumVarianceAtomBindingSourceOnly OriginalPrincipalVarianceInOuterCauchy20261028
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalActualSingleZeroSource

/-- The exact section-4 large-shift correction BEFORE zero restoration. -/
def largeShiftDeleted (atom : MediumAtom) (z y : ℝ) (k : Key) (H : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ¬ShiftCut atom H t then S3DeletedTerm atom z y k t else 0

/-- The literal cutoff complement. Both exact-product single-zero
branches remain here, and are already subtracted by H's restoration. -/
def largeShiftFull (atom : MediumAtom) (z y : ℝ) (k : Key) (H : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ¬ShiftCut atom H t then S3FullTerm atom z y k t else 0

/-- The literal original far source, with NO clean rough/gcd restriction. -/
def farFull (atom : MediumAtom) (z y : ℝ) (k : Key) (H T : ℝ) : ℂ :=
  ∑ t ∈ offDiagonalCarrier atom k,
    if ShiftCut atom H t ∧ ¬Close T t then S3FullTerm atom z y k t else 0

theorem fullTerm_eq_deleted_of_shiftCut (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H : ℝ) (t : PairIndex) (h : ShiftCut atom H t) :
    S3FullTerm atom z y k t = S3DeletedTerm atom z y k t := by
  have h1 : ((t.2.1.2 * t.1.2.2 : ℕ) : ℤ) ≠ atom.residue := by
    intro hz
    apply h.1
    simp only [shiftAbs, firstMN, hz, sub_self, Int.natAbs_zero]
  have h2 : ((t.2.2.2 * t.1.2.2 : ℕ) : ℤ) ≠ atom.residue := by
    intro hz
    apply h.2.1
    simp only [shiftAbs, secondMN, hz, sub_self, Int.natAbs_zero]
  simp only [S3FullTerm, S3DeletedTerm, firstDeleted, secondDeleted, oldIndex,
    fullIndicator, deletedIndicator, if_neg h1, if_neg h2]

/-- The full cutoff complement is not silently called a pure large-value
correction: these are its exact two already-known single-zero additions. -/
theorem largeShiftFull_eq_deleted_add_singleZeros
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H : ℝ) :
    largeShiftFull atom z y k H = largeShiftDeleted atom z y k H +
      actualFirstZero atom z y k + actualSecondZero atom z y k := by
  unfold largeShiftFull largeShiftDeleted actualFirstZero actualSecondZero
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · have h1 : ((t.2.1.2 * t.1.2.2 : ℕ) : ℤ) ≠ atom.residue := by
      intro hz
      apply hs.1
      simp only [shiftAbs, firstMN, hz, sub_self, Int.natAbs_zero]
    have h2 : ((t.2.2.2 * t.1.2.2 : ℕ) : ℤ) ≠ atom.residue := by
      intro hz
      apply hs.2.1
      simp only [shiftAbs, secondMN, hz, sub_self, Int.natAbs_zero]
    simp [hs, firstZeroTerm, secondZeroTerm, zeroIndicator, oldIndex, h1, h2]
  · simp only [hs, not_false_eq_true, if_true]
    exact offDiagonal_full_eq_deleted_add_single_zeros
      (zero_lt_one.trans_le hAdm.2.1) ht

theorem restoredOffDiagonal_eq_cut_far_close (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H T : ℝ) :
    restoredOffDiagonal atom z y k =
      largeShiftFull atom z y k H + farFull atom z y k H T + closeDeleted atom z y k H T := by
  unfold restoredOffDiagonal largeShiftFull farFull closeDeleted
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  by_cases hs : ShiftCut atom H t
  · by_cases hc : Close T t
    · simp only [hs, hc, not_true_eq_false, true_and, if_true, if_false, zero_add]
      exact fullTerm_eq_deleted_of_shiftCut atom z y k H t hs
    · simp [hs, hc]
  · simp [hs]

/-- Direct original S3 reconstruction; no double-zero diagonal is added. -/
theorem primitiveS3_eq_cut_far_close_restoration
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (primitiveS3 atom z y k : ℂ) =
      largeShiftFull atom z y k H + farFull atom z y k H T +
        closeDeleted atom z y k H T + restorationCorrection atom z y k := by
  have hh := primitiveS3_sub_restoredOffDiagonal_eq_restoration hAdm z y k
  rw [restoredOffDiagonal_eq_cut_far_close atom z y k H T] at hh
  linear_combination hh

/-- Exact bridge to the EXISTING retained Fourier source. The far source
is physical; its zero-mode and omitted-frequency subtractions are displayed,
not asserted to be a new clean retained Poisson kernel. -/
theorem retainedSourceKey_eq_physical_cut_far_close
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    retainedSourceKey atom z y k =
      (farFull atom (strictReceiverCutoff z) y k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) y k -
        offDiagonalOmitted atom z y k + diagonalRetained atom z y k) +
      largeShiftFull atom (strictReceiverCutoff z) y k H +
      closeDeleted atom (strictReceiverCutoff z) y k H T := by
  have hp := primitiveS3_eq_cut_far_close_restoration hAdm (strictReceiverCutoff z) y k H T
  have hf := literalS3_eq_retained_add_corrections hAdm z y k
  rw [sourceCorrectionKey_eq_zero_add_remaining,
    actual_offDiagonalZero_eq_independent_zero,
    remainingCorrectionKey_eq_restoration_omitted_diagonal] at hf
  linear_combination hp - hf

/-- Original unpaid norm ledger, with its original outer multiplier.
The far packet is written out so that the unperformed zero restoration,
omitted-mode and retained-diagonal transformations remain inspectable. -/
def unpaidOriginalCloseLedger (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      (‖farFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
          genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
          offDiagonalOmitted atom z (originalSmoothTrim atom) k +
          diagonalRetained atom z (originalSmoothTrim atom) k‖ +
        ‖largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c)‖ +
        ‖offDiagonalOmitted atom z (originalSmoothTrim atom) k‖ +
        ‖diagonalRetained atom z (originalSmoothTrim atom) k‖ +
        ‖roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
        ‖genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
        2 * (‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖))

theorem actualResidualFunctional_le_close_and_restoration
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z c A : ℝ)
    (hAdm : MediumAdmissible B σ κ c0 atom) :
    actualResidualFunctional atom z ≤ unpaidOriginalCloseLedger B atom z c A +
      actualOuterCloseBudget B atom z c A + actualOuterRestorationBudget atom z := by
  apply (actualResidualFunctional_le_after_restoration atom z hAdm).trans
  apply add_le_add_right
  unfold unpaidOriginalCloseLedger actualOuterCloseBudget
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  have he := retainedSourceKey_eq_physical_cut_far_close hAdm z (originalSmoothTrim atom) k
    (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))
  rw [he]
  have hn := (norm_add_le
    ((farFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
      genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
      offDiagonalOmitted atom z (originalSmoothTrim atom) k +
      diagonalRetained atom z (originalSmoothTrim atom) k) +
      largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k (shiftCutoff atom c))
    (closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)))).trans
      (add_le_add_right (norm_add_le _ _) _)
  linarith

/-- An actual arbitrary-log payment at the UNCHANGED residual consumer.
One threshold pays H's diagonal/two-single-zero packet AND the new original
close correction. No bound on the remaining ledger is a premise. -/
theorem exists_actualResidualFunctional_close_paid (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualResidualFunctional atom z ≤ unpaidOriginalCloseLedger B atom z c A +
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Cc, hCc, xc, hxc, hclose⟩ := exists_actualOuterCloseBudget_payment B σ κ c A hσ hσsmall
  obtain ⟨Cr, hCr, xr, hxr, hrest⟩ := original_all_key_S3_restoration_log_payment B σ κ A hσ hσsmall
  refine ⟨Cc+Cr, add_pos hCc hCr, max xc xr, hxc.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  have hc := hclose c0 atom hAdm hc0 ((le_max_left _ _).trans hx) z hz
  have hr := hrest c0 atom hAdm hc0 ((le_max_right _ _).trans hx) z hz
  have hsource := actualResidualFunctional_le_close_and_restoration atom z c A hAdm
  calc
    _ ≤ unpaidOriginalCloseLedger B atom z c A +
        actualOuterCloseBudget B atom z c A + actualOuterRestorationBudget atom z := hsource
    _ ≤ unpaidOriginalCloseLedger B atom z c A +
        Cc * atom.scale^2 / Real.log atom.scale^A + Cr * atom.scale^2 / Real.log atom.scale^A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3ClosePairResidual20261102
