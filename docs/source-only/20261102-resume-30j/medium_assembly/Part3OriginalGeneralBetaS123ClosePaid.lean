import ImbalancedChen.Part3OriginalGeneralBetaS123ArithmeticPaid
import ImbalancedChen.Part3OriginalS3ClosePairResidual
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Insert the frozen I physical close-pair payment into the signed arbitrary-B
entrance. The original omitted-frequency and retained-diagonal terms cancel
algebraically against the exact physical-source dictionary before any norm
is taken. The remaining physical sources are not called clean Fourier E2.
-/

namespace ImbalancedChen.Part3.OriginalGeneralBetaS123ClosePaid20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalGeneralBetaS123ArithmeticPaid20261102
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
open MediumPrimitiveShiuWindow20261028

/-- The exact retained source plus its original signed Fourier corrections
is the original physical cut/far/close source, centred by the same genuine
off-diagonal zero. No equality with the clean E2 kernel is assumed. -/
theorem retained_with_Fourier_corrections_eq_original_cut_far_close
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) (H T : ℝ) :
    retainedSourceKey atom z y k + offDiagonalOmitted atom z y k -
      diagonalRetained atom z y k =
      farFull atom (strictReceiverCutoff z) y k H T -
        genuineOffDiagonalZero atom (strictReceiverCutoff z) y k +
        largeShiftFull atom (strictReceiverCutoff z) y k H +
        closeDeleted atom (strictReceiverCutoff z) y k H T := by
  have hsource := retainedSourceKey_eq_physical_cut_far_close hAdm z y k H T
  linear_combination hsource

/-- Preserve every unpaid real part while replacing only the actual
close packet by its norm. Both owner-bank multiplicities and outerL2
are the same ones used in I's actualOuterCloseBudget payment. -/
theorem original_signed_arithmetic_packets_le_close_split
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z c A : ℝ)
    (hAdm : MediumAdmissible B σ κ c0 atom) :
    ((originalNumericKeys atom z).card : ℝ) *
      (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
          (offDiagonalOmitted atom z (originalSmoothTrim atom) k).re -
          (diagonalRetained atom z (originalSmoothTrim atom) k).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) ≤
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
            (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) +
      actualOuterCloseBudget B atom z c A := by
  calc
    _ ≤ ((originalNumericKeys atom z).card : ℝ) *
        (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
          (((farFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))).re -
            (genuineOffDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
            (largeShiftFull atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c)).re +
            (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
              (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re)) +
            ‖closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
              (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A))‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
      have hs := congrArg Complex.re
        (retained_with_Fourier_corrections_eq_original_cut_far_close hAdm z
          (originalSmoothTrim atom) k (shiftCutoff atom c)
          (closeWidth atom c (outerPrecision B A)))
      simp only [Complex.add_re, Complex.sub_re] at hs
      linarith [Complex.re_le_norm
        (closeDeleted atom (strictReceiverCutoff z) (originalSmoothTrim atom) k
          (shiftCutoff atom c) (closeWidth atom c (outerPrecision B A)))]
    _ = _ := by
      unfold actualOuterCloseBudget
      simp only [mul_add, Finset.sum_add_distrib]

/-- One threshold pays the frozen original LINEAR, S2 single-zero,
S3 restoration and close-pair suppliers for every fixed original B.
Ccut=c is fixed before separation precision A+betaMomentOrder(B)+12+6c
and before every family atom. The full cutoff complement and far centred
physical source stay signed and unestimated. -/
theorem uniformAuxiliarySW_general_beta_original_signed_source_close_paid
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 c : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      let atom := F i
      let z := roughZ atom.scale
      let receiver := strictReceiverCutoff z
      let y := originalSmoothTrim atom
      let K := originalNumericKeys atom z
      ‖atom.signedError‖ ^ 2 ≤ 3 * (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        ((farFull atom receiver y k (shiftCutoff atom c)
            (closeWidth atom c (outerPrecision B A))).re -
          (genuineOffDiagonalZero atom receiver y k).re +
          (largeShiftFull atom receiver y k (shiftCutoff atom c)).re +
          (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * ((actualS2NonzeroModes atom receiver y k).re -
            (otherRoughCorrection atom receiver y k).re)) +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Ce, hCe, Xe, hXe, hentrance⟩ :=
    uniformAuxiliarySW_general_beta_original_signed_source_arithmetic_paid
      F B C0 σ κ c0 hadmissible hSW hσ hσsmall hc0 hShiu A hA
  obtain ⟨Cc, hCc, Xc, hXc, hclose⟩ :=
    exists_actualOuterCloseBudget_payment B σ κ c A hσ hσsmall
  refine ⟨Ce + 3 * Cc, by positivity, max Xe Xc,
    hXe.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  dsimp only
  let atom := F i
  let z := roughZ atom.scale
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le
    (TransposedPrimitiveUPayment.one_le_scale (hadmissible i))
  have hz : 0 ≤ z := Real.rpow_nonneg hxpos.le _
  have he := hentrance i ((le_max_left _ _).trans hx)
  have hc := hclose c0 atom (hadmissible i) hc0
    ((le_max_right _ _).trans hx) z hz
  have hs := original_signed_arithmetic_packets_le_close_split atom z c A (hadmissible i)
  nlinarith

end
end ImbalancedChen.Part3.OriginalGeneralBetaS123ClosePaid20261102
