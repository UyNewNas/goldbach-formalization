import ImbalancedChen.Part3OriginalS3RoughLevelGcdPayment
import ImbalancedChen.Part3OriginalS3RoughPairGcdResidual
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay (s,ell)>1 in J's actual r/s-coprime far packet, after original
outside weights. The n1/n2 gate and every old unpaid source remain.
-/
namespace ImbalancedChen.Part3.OriginalS3RoughLevelGcdResidual20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS3RoughLevelGcd20261102 OriginalS3RoughLevelGcdPayment20261102
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

theorem primitiveS3_eq_cut_level_bad_close_restoration
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    (primitiveS3 atom z y k : ℂ) =
      largeShiftFull atom z y k H + levelCoprimeFarFull atom z y k H T +
        badLevelDeleted atom z y k H T + badPairDeleted atom z y k H T +
        closeDeleted atom z y k H T + restorationCorrection atom z y k := by
  rw [primitiveS3_eq_cut_coprime_bad_close_restoration hAdm z y k H T,
    coprimeFarFull_eq_level_add_bad]
  ring

theorem retainedSourceKey_eq_cut_level_bad_close
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    retainedSourceKey atom z y k =
      (levelCoprimeFarFull atom (strictReceiverCutoff z) y k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) y k -
        offDiagonalOmitted atom z y k + diagonalRetained atom z y k) +
      largeShiftFull atom (strictReceiverCutoff z) y k H +
      badLevelDeleted atom (strictReceiverCutoff z) y k H T +
      badPairDeleted atom (strictReceiverCutoff z) y k H T +
      closeDeleted atom (strictReceiverCutoff z) y k H T := by
  rw [retainedSourceKey_eq_cut_coprime_bad_close hAdm z y k H T,
    coprimeFarFull_eq_level_add_bad]
  ring

/-- The retained packet has (r,s)=1 AND (s,ell)=1, but n1/n2 remains
unrestricted. It is not identified with the clean Fourier E2 source.
The original largeShiftFull, zero subtraction, omitted and diagonal
modes, rough replacement and all four S2 norms are copied literally. -/
def unpaidOriginalLevelLedger (B : ℕ) (atom : MediumAtom) (z c A : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      (‖levelCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
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

theorem unpaidOriginalGcdLedger_le_level_split (B : ℕ) (atom : MediumAtom) (z c A : ℝ) :
    unpaidOriginalGcdLedger B atom z c A ≤
      unpaidOriginalLevelLedger B atom z c A + actualOuterLevelBudget B atom z c A := by
  unfold unpaidOriginalGcdLedger unpaidOriginalLevelLedger actualOuterLevelBudget
  rw [← mul_add,← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  rw [coprimeFarFull_eq_level_add_bad]
  have he :
      levelCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) +
        badLevelDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k =
      (levelCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
        offDiagonalOmitted atom z (originalSmoothTrim atom) k +
        diagonalRetained atom z (originalSmoothTrim atom) k) +
        badLevelDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) := by ring
  rw [he]
  have hn := norm_add_le
    (levelCoprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
        (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)) -
      genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k -
      offDiagonalOmitted atom z (originalSmoothTrim atom) k +
      diagonalRetained atom z (originalSmoothTrim atom) k)
    (badLevelDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
      (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)))
  linarith

/-- The existing residual functional now pays the actual (s,ell)>1
branch in addition to J's r/s and I's close-pair corrections. All
fixed exponents precede one threshold for every atom, key and receiver. -/
theorem exists_actualResidualFunctional_level_paid (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, roughZ atom.scale ≤ z →
          actualResidualFunctional atom z ≤ unpaidOriginalLevelLedger B atom z c A +
            C*atom.scale^2/Real.log atom.scale^A := by
  obtain ⟨Cj,hCj,xj,hxj,hJ⟩ := exists_actualResidualFunctional_gcd_paid B σ κ c A hσ hσsmall
  obtain ⟨Cl,hCl,xl,hxl,hL⟩ := exists_actualOuterLevelBudget_payment B σ κ c A hσ hσsmall
  refine ⟨Cj+Cl,add_pos hCj hCl,max xj xl,hxj.trans_le (le_max_left _ _),?_⟩
  intro c0 atom hAdm hc0 hx z hzr
  have hj := hJ c0 atom hAdm hc0 ((le_max_left _ _).trans hx) z hzr
  have hl := hL c0 atom hAdm hc0 ((le_max_right _ _).trans hx) z hzr
  have hs := unpaidOriginalGcdLedger_le_level_split B atom z c A
  calc
    _ ≤ unpaidOriginalGcdLedger B atom z c A + Cj*atom.scale^2/Real.log atom.scale^A := hj
    _ ≤ unpaidOriginalLevelLedger B atom z c A +
        Cl*atom.scale^2/Real.log atom.scale^A + Cj*atom.scale^2/Real.log atom.scale^A := by linarith
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalS3RoughLevelGcdResidual20261102
