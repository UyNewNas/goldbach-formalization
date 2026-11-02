import ImbalancedChen.Part3OriginalS3RoughPairGcdPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Insert the actual rough-pair gcd payment into the EXISTING signed source
and residual functional. Every old unpaid Fourier/zero/S2 correction
and the full large-shift complement remains explicit.
-/
namespace ImbalancedChen.Part3.OriginalS3RoughPairGcdResidual20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3RoughPairGcd20261102 OriginalS3RoughPairGcdPayment20261102
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairPayment20261102
open OriginalS3ClosePairResidual20261102
open MediumLiteralS3Stages20261028 MediumLiteralS3Deleted20261028
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open MediumActualS3ZeroCentering20261028 MediumOriginalRestorationLedger20261102
open MediumOriginalAllKeyRestorationPayment20261102
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028 OriginalCompleteS123Ledger20261028
open OriginalSamePsiS1OwnedAtlas OriginalS1OuterCauchy20261028
open ActualMediumVarianceAtomBindingSourceOnly OriginalPrincipalVarianceInOuterCauchy20261028
open ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalActualSingleZeroSource

/-- Original signed S3 ledger with exactly one further gcd exclusion.
The large-shift complement is unchanged and includes its old single zeros;
H's restoration keeps precisely the compensating negative signs. -/
theorem primitiveS3_eq_cut_coprime_bad_close_restoration
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (primitiveS3 atom z y k : ℂ) =
      largeShiftFull atom z y k H + coprimeFarFull atom z y k H T +
        badPairDeleted atom z y k H T + closeDeleted atom z y k H T +
        restorationCorrection atom z y k := by
  rw [primitiveS3_eq_cut_far_close_restoration hAdm z y k H T,
    farFull_eq_coprime_add_bad]
  ring

theorem retainedSourceKey_eq_cut_coprime_bad_close
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    retainedSourceKey atom z y k =
      (coprimeFarFull atom (strictReceiverCutoff z) y k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) y k -
        offDiagonalOmitted atom z y k + diagonalRetained atom z y k) +
      largeShiftFull atom (strictReceiverCutoff z) y k H +
      badPairDeleted atom (strictReceiverCutoff z) y k H T +
      closeDeleted atom (strictReceiverCutoff z) y k H T := by
  rw [retainedSourceKey_eq_physical_cut_far_close hAdm z y k H T,
    farFull_eq_coprime_add_bad]
  ring

/-- The physical far packet only has (r,s)=1 imposed. It is NOT called
clean E2: n1/n2, s/ell, cutoff reinstatement and zero-mode corrections
are all still unpaid. Every original outside weight is copied literally. -/
def unpaidOriginalGcdLedger (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      (‖coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
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
        2*(‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖))

theorem unpaidOriginalCloseLedger_le_gcd_split (B : ℕ) (atom : MediumAtom) (z c A : ℝ) :
    unpaidOriginalCloseLedger B atom z c A ≤
      unpaidOriginalGcdLedger B atom z c A + actualOuterGcdBudget B atom z c A := by
  unfold unpaidOriginalCloseLedger unpaidOriginalGcdLedger actualOuterGcdBudget
  rw [← mul_add,← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  rw [farFull_eq_coprime_add_bad]
  have he :
      coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) +
        badPairDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k =
      (coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k) +
        badPairDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) := by ring
  rw [he]
  have hn := norm_add_le
    (coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
      genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
      offDiagonalOmitted atom z (originalSmoothTrim atom) k +
      diagonalRetained atom z (originalSmoothTrim atom) k)
    (badPairDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)))
  linarith

/-- One actual additional correction is paid at the unchanged residual
functional, after original outside weights. The literal physical rough
cutoff is an instance; the remaining ledger has no assumed estimate. -/
theorem exists_actualResidualFunctional_gcd_paid (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, roughZ atom.scale ≤ z →
          actualResidualFunctional atom z ≤ unpaidOriginalGcdLedger B atom z c A +
            C*atom.scale^2/Real.log atom.scale^A := by
  obtain ⟨Ci,hCi,xi,hxi,hI⟩ := exists_actualResidualFunctional_close_paid B σ κ c A hσ hσsmall
  obtain ⟨Cg,hCg,xg,hxg,hG⟩ := exists_actualOuterGcdBudget_payment B σ κ c A hσ hσsmall
  refine ⟨Ci+Cg,add_pos hCi hCg,max xi xg,hxi.trans_le (le_max_left _ _),?_⟩
  intro c0 atom hAdm hc0 hx z hzr
  have hscale : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.1,hAdm.2.1]
  have hz : 0 ≤ z := ((Real.rpow_pos_of_pos hscale _).trans_le hzr).le
  have hi := hI c0 atom hAdm hc0 ((le_max_left _ _).trans hx) z hz
  have hg := hG c0 atom hAdm hc0 ((le_max_right _ _).trans hx) z hzr
  have hs := unpaidOriginalCloseLedger_le_gcd_split B atom z c A
  calc
    _ ≤ unpaidOriginalCloseLedger B atom z c A + Ci*atom.scale^2/Real.log atom.scale^A := hi
    _ ≤ unpaidOriginalGcdLedger B atom z c A +
        Cg*atom.scale^2/Real.log atom.scale^A + Ci*atom.scale^2/Real.log atom.scale^A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3RoughPairGcdResidual20261102
