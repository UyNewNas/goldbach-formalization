import ImbalancedChen.Part3OriginalGeneralBetaS123ClosePaid
import ImbalancedChen.Part3OriginalAllKeyS2OtherRoughPayment
import ImbalancedChen.Part3OriginalS3RoughPairGcdPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Insert the actual J S2 other-rough and cutoff-qualified S3 (r,s)>1
payments into the unchanged arbitrary-B signed S123 entrance. Only
these two real parts are replaced by norms. All other sources stay
signed; the physical far packet is not identified with clean E2.
-/

namespace ImbalancedChen.Part3.OriginalGeneralBetaS123RoughGcdPaid20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalGeneralBetaS123ClosePaid20261102
open OriginalAllKeyS2OtherRoughPayment20261102
open OriginalS3RoughPairGcd20261102 OriginalS3RoughPairGcdPayment20261102
open OriginalS3ClosePairCount20261102 OriginalS3ClosePairPayment20261102
open OriginalS3ClosePairResidual20261102
open ActualRoughContourParameters20261026b
open ActualMediumVarianceAtomBindingSourceOnly OriginalS1OuterCauchy20261028
open MediumReceiverCutoffArithmetic20261028 MediumGlobalDyadicOwnership20261028
open MediumActualPreliminaryCauchy20261028 MediumActualS3ZeroCentering20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2ShiftedTwelve
open MediumPrimitiveShiuWindow20261028

/-- Apply the exact farFull split before taking a norm, and keep all
other real parts signed. The original S2 minus-two bracket contributes
PLUS twice otherRough, hence the second budget has factor two. -/
theorem original_signed_close_packets_le_rough_gcd_split
    (B : ℕ) (atom : MediumAtom) (z c A : ℝ) :
    ((originalNumericKeys atom z).card : ℝ) *
      (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((farFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
            (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))).re -
          (genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
          (largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
            (shiftCutoff atom c)).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) ≤
    ((originalNumericKeys atom z).card : ℝ) *
      (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
            (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))).re -
          (genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
          (largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
            (shiftCutoff atom c)).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * (actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re)) +
      actualOuterGcdBudget B atom z c A + 2 * actualOuterS2OtherRoughBudget atom z := by
  calc
    _ ≤ ((originalNumericKeys atom z).card : ℝ) *
        (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
          (((coprimeFarFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))).re -
            (genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
            (largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c)).re +
            (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            2 * (actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re) +
            ‖badPairDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))‖ +
            2 * ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
      rw [farFull_eq_coprime_add_bad, Complex.add_re]
      linarith [Complex.re_le_norm
          (badPairDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
            (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))),
        Complex.re_le_norm
          (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k)]
    _ = _ := by
      have htwo :
          (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
            (2 * ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)) =
          2 * ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
            ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro k hk
        ring
      unfold actualOuterGcdBudget actualOuterS2OtherRoughBudget
      simp only [mul_add, Finset.sum_add_distrib, htwo]
      ring

/-- Pay precisely the two new budgets at their actual original receiver.
The S3 source uses the same c, D and close width as J's signed entrance.
No bound on any remaining signed packet is used. -/
theorem original_all_key_rough_gcd_log_payment
    (hShiu : S2PrimitiveShiu) (B : ℕ) (σ κ c A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ σ / 100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
          actualOuterGcdBudget B atom (roughZ atom.scale) c A +
            2 * actualOuterS2OtherRoughBudget atom (roughZ atom.scale) ≤
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Cg, hCg, Xg, hXg, hgcd⟩ :=
    exists_actualOuterGcdBudget_payment B σ κ c A hσ hσsmall
  obtain ⟨Cr, hCr, Xr, hXr, hrough⟩ :=
    original_all_key_S2_otherRough_log_payment hShiu B σ κ A hσ hσsmall hκ0 hκ hA
  refine ⟨Cg + 2 * Cr, by positivity, max Xg Xr,
    hXg.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hAdm hc0 hx
  have hg := hgcd c0 atom hAdm hc0 ((le_max_left _ _).trans hx) (roughZ atom.scale) le_rfl
  have hr := hrough c0 atom hAdm hc0 ((le_max_right _ _).trans hx)
  calc
    _ ≤ Cg * atom.scale ^ 2 / Real.log atom.scale ^ A +
        2 * (Cr * atom.scale ^ 2 / Real.log atom.scale ^ A) := by linarith
    _ = _ := by ring

/-- Original arbitrary-B signed entrance, with one uniform threshold for
the inherited LINEAR/Gram/product/restoration/single-zero/close payments
and the newly paid S2 other-rough and S3 rough-pair gcd sources.
The only retained far restriction added here is (r,s)=1. Its other gcd
gates, full off-diagonal zero, full largeShift complement, genuine zero
diagonal, rough replacement and complete nonzero S2 source stay literal.
This is not the full restricted-medium estimate. -/
theorem uniformAuxiliarySW_general_beta_original_signed_source_rough_gcd_paid
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 c : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hc0 : 0 < c0) (hκ0 : 0 ≤ κ) (hκ : κ ≤ σ / 100)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hS2Shiu : S2PrimitiveShiu) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      let atom := F i
      let z := roughZ atom.scale
      let receiver := strictReceiverCutoff z
      let y := originalSmoothTrim atom
      let K := originalNumericKeys atom z
      ‖atom.signedError‖ ^ 2 ≤ 3 * (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        ((coprimeFarFull atom receiver y k (shiftCutoff atom c)
            (closeWidth atom c (outerPrecision B A))).re -
          (genuineOffDiagonalZero atom receiver y k).re +
          (largeShiftFull atom receiver y k (shiftCutoff atom c)).re +
          (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * (actualS2NonzeroModes atom receiver y k).re) +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Ce, hCe, Xe, hXe, hentrance⟩ :=
    uniformAuxiliarySW_general_beta_original_signed_source_close_paid
      F B C0 σ κ c0 c hadmissible hSW hσ hσsmall hc0 hShiu A hA
  obtain ⟨Cc, hCc, Xc, hXc, hcorrections⟩ :=
    original_all_key_rough_gcd_log_payment hS2Shiu B σ κ c A hσ hσsmall hκ0 hκ hA
  refine ⟨Ce + 3 * Cc, by positivity, max Xe Xc,
    hXe.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  dsimp only
  let atom := F i
  let z := roughZ atom.scale
  have he := hentrance i ((le_max_left _ _).trans hx)
  have hc := hcorrections c0 atom (hadmissible i) hc0 ((le_max_right _ _).trans hx)
  have hs := original_signed_close_packets_le_rough_gcd_split B atom z c A
  nlinarith

end
end ImbalancedChen.Part3.OriginalGeneralBetaS123RoughGcdPaid20261102
