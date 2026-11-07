import ImbalancedChen.Part3OriginalS3AlphaGcdPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The n1/n2 payment is inserted into the existing original residual norm
ledger. The s/ell exclusion, cutoff complement/reinstatement, zero-mode
restoration and every previously unpaid term remain explicit.
-/
namespace ImbalancedChen.Part3.OriginalS3AlphaGcdResidual20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3AlphaGcdCount20261102 OriginalS3AlphaGcdPayment20261102
open OriginalS3RoughPairGcd20261102 OriginalS3RoughPairGcdPayment20261102
open OriginalS3RoughPairGcdResidual20261102
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

theorem primitiveS3_eq_cut_double_bad_close_restoration
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (primitiveS3 atom z y k : ℂ) =
      largeShiftFull atom z y k H + doubleCoprimeFarFull atom z y k H T +
        alphaBadDeleted atom z y k H T + badPairDeleted atom z y k H T +
        closeDeleted atom z y k H T + restorationCorrection atom z y k := by
  rw [primitiveS3_eq_cut_coprime_bad_close_restoration hAdm z y k H T,
    coprimeFarFull_eq_double_add_bad]
  ring

theorem retainedSourceKey_eq_cut_double_bad_close
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    retainedSourceKey atom z y k =
      (doubleCoprimeFarFull atom (strictReceiverCutoff z) y k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) y k -
        offDiagonalOmitted atom z y k + diagonalRetained atom z y k) +
      largeShiftFull atom (strictReceiverCutoff z) y k H +
      alphaBadDeleted atom (strictReceiverCutoff z) y k H T +
      badPairDeleted atom (strictReceiverCutoff z) y k H T +
      closeDeleted atom (strictReceiverCutoff z) y k H T := by
  rw [retainedSourceKey_eq_cut_coprime_bad_close hAdm z y k H T,
    coprimeFarFull_eq_double_add_bad]
  ring

/-- Both r/s and n1/n2 are coprime. This is still not the clean E2
packet: s/ell and all Fourier/restoration obligations remain unpaid. -/
def unpaidOriginalAlphaGcdLedger (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      (‖doubleCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
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

theorem unpaidOriginalGcdLedger_le_alpha_split (B : ℕ) (atom : MediumAtom) (z c A : ℝ) :
    unpaidOriginalGcdLedger B atom z c A ≤
      unpaidOriginalAlphaGcdLedger B atom z c A + actualOuterAlphaGcdBudget B atom z c A := by
  unfold unpaidOriginalGcdLedger unpaidOriginalAlphaGcdLedger actualOuterAlphaGcdBudget
  rw [← mul_add,← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  rw [coprimeFarFull_eq_double_add_bad]
  have he :
      doubleCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) +
        alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k =
      (doubleCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k) +
        alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) := by ring
  rw [he]
  have hn := norm_add_le
    (doubleCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
      genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
      offDiagonalOmitted atom z (originalSmoothTrim atom) k +
      diagonalRetained atom z (originalSmoothTrim atom) k)
    (alphaBadDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)))
  linarith

/-- One actual additional correction is paid at the unchanged residual
functional, after original outside weights. The literal physical rough
cutoff is an instance; the remaining ledger has no assumed estimate. -/
theorem exists_actualResidualFunctional_alpha_gcd_paid (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, roughZ atom.scale ≤ z →
          actualResidualFunctional atom z ≤ unpaidOriginalAlphaGcdLedger B atom z c A +
            C*atom.scale^2/Real.log atom.scale^A := by
  obtain ⟨Ci,hCi,xi,hxi,hI⟩ := exists_actualResidualFunctional_gcd_paid B σ κ c A hσ hσsmall
  obtain ⟨Cg,hCg,xg,hxg,hG⟩ := exists_actualOuterAlphaGcdBudget_payment B σ κ c A hσ hσsmall
  refine ⟨Ci+Cg,add_pos hCi hCg,max xi xg,hxi.trans_le (le_max_left _ _),?_⟩
  intro c0 atom hAdm hc0 hx z hzr
  have hscale : 0 < atom.scale := by unfold MediumAtom.scale; nlinarith [hAdm.1,hAdm.2.1]
  have hz : 0 ≤ z := ((Real.rpow_pos_of_pos hscale _).trans_le hzr).le
  have hi := hI c0 atom hAdm hc0 ((le_max_left _ _).trans hx) z hzr
  have hg := hG c0 atom hAdm hc0 ((le_max_right _ _).trans hx) z hzr
  have hs := unpaidOriginalGcdLedger_le_alpha_split B atom z c A
  calc
    _ ≤ unpaidOriginalGcdLedger B atom z c A + Ci*atom.scale^2/Real.log atom.scale^A := hi
    _ ≤ unpaidOriginalAlphaGcdLedger B atom z c A +
        Cg*atom.scale^2/Real.log atom.scale^A + Ci*atom.scale^2/Real.log atom.scale^A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3AlphaGcdResidual20261102
