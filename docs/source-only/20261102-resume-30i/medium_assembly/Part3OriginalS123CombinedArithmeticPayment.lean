import ImbalancedChen.Part3OriginalAllKeyS2SingleZeroPayment
import ImbalancedChen.Part3OriginalS123PaidLinearEntrance
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Combine the genuine H entrance, S2 mean-weighted single zero and S3
restoration on the independently defined original sources. The signed
retained/nonzero/rough/Fourier remainder is left literal. In particular
this file does not assume or prove a final residual or medium bound.
The general-beta LINEAR entrance remains a separate dependency.
-/

namespace ImbalancedChen.Part3.OriginalS123CombinedArithmeticPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalAllKeyS2SingleZeroPayment20261102
open OriginalS123PaidLinearEntrance20261102
open MediumOriginalAllKeyRestorationPayment20261102
open MediumOriginalRestorationLedger20261102 MediumActualRestorationPayment20261028
open ActualMediumVarianceAtomBindingSourceOnly OriginalS1OuterCauchy20261028
open OriginalPrincipalVarianceInOuterCauchy20261028 OriginalCompleteS123Ledger20261028
open MediumReceiverCutoffArithmetic20261028 MediumGlobalDyadicOwnership20261028
open MediumActualPreliminaryCauchy20261028 MediumActualS3ZeroCentering20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open MediumPrimitiveShiuWindow20261028

/-- Exact original packet algebra followed only by re<=norm on the
two genuinely paid corrections. g carries the unchanged zero-Gram term
when this lemma is applied to actualResidualFunctional, and is zero
when the independently paid H entrance has already removed that term.
No alternate residual functional is introduced. -/
theorem original_signed_packets_le_after_S2_S3_split
    (atom : MediumAtom) (z : ℝ) (g : Key → ℝ) :
    ((originalNumericKeys atom z).card : ℝ) *
      (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
          (remainingCorrectionKey atom z (originalSmoothTrim atom) k).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
            g k - (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) ≤
    ((originalNumericKeys atom z).card : ℝ) *
      (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
          (offDiagonalOmitted atom z (originalSmoothTrim atom) k).re -
          (diagonalRetained atom z (originalSmoothTrim atom) k).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
            g k - (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) +
      actualOuterRestorationBudget atom z + 2 * actualOuterS2SingleZeroBudget atom z := by
  calc
    _ ≤ ((originalNumericKeys atom z).card : ℝ) *
        (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
          (((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
            (offDiagonalOmitted atom z (originalSmoothTrim atom) k).re -
            (diagonalRetained atom z (originalSmoothTrim atom) k).re +
            (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
              g k - (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re)) +
            ‖restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            2 * ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
      rw [remainingCorrectionKey_eq_restoration_omitted_diagonal]
      simp only [Complex.add_re, Complex.sub_re]
      linarith [Complex.re_le_norm
          (restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
        Complex.re_le_norm
          (singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k)]
    _ = _ := by
      have htwo :
          (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
            (2 * ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)) =
          2 * ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
            ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro k hk
        ring
      unfold actualOuterRestorationBudget actualOuterS2SingleZeroBudget
      simp only [mul_add, Finset.sum_add_distrib, htwo]
      ring

/-- A single requested precision and a single threshold pay the S3
restoration and TWICE the distinct S2 single zero. Both owner-bank
multiplicities and the original beta divisor moment are already paid.
This theorem has no SW or final-residual premise. -/
theorem original_all_key_S2_S3_correction_log_payment
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualOuterRestorationBudget atom z + 2 * actualOuterS2SingleZeroBudget atom z ≤
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Cr, hCr, Xr, hXr, hrest⟩ :=
    original_all_key_S3_restoration_log_payment B σ κ A hσ hσsmall
  obtain ⟨Cs, hCs, Xs, hXs, hsingle⟩ :=
    original_all_key_S2_singleZero_log_payment B κ A
  refine ⟨Cr + 2 * Cs, by positivity, max Xr Xs,
    hXr.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  have hr := hrest c0 atom hAdm hc0 ((le_max_left _ _).trans hx) z hz
  have hs := hsingle σ c0 atom hAdm hσ.le hc0 ((le_max_right _ _).trans hx) z hz
  calc
    _ ≤ Cr * atom.scale ^ 2 / Real.log atom.scale ^ A +
        2 * (Cs * atom.scale ^ 2 / Real.log atom.scale ^ A) := by linarith
    _ = _ := by ring

/-- Consumer in the EXISTING actualResidualFunctional, for arbitrary B.
Its zero-Gram, actual retained source, nonzero E1, other-rough and all
Fourier/rough/zero-diagonal terms remain with their original signs.
No general-beta linear entrance is needed for this independent step. -/
theorem exists_actualResidualFunctional_S2_S3_arithmetic_paid
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualResidualFunctional atom z ≤
            ((originalNumericKeys atom z).card : ℝ) *
              (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
                ((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
                  (offDiagonalOmitted atom z (originalSmoothTrim atom) k).re -
                  (diagonalRetained atom z (originalSmoothTrim atom) k).re +
                  (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
                  (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
                  2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
                    (actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
                    (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re))) +
              C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hpay⟩ :=
    original_all_key_S2_S3_correction_log_payment B σ κ A hσ hσsmall
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  rw [actualResidualFunctional_eq_complete_original_packets atom z hAdm]
  have hsplit := original_signed_packets_le_after_S2_S3_split atom z
    (fun k => (actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re)
  have hp := hpay c0 atom hAdm hc0 hx z hz
  linarith

/-- The initial one-bounded-beta branch now has ONE uniform threshold
for S1/P, S2 zero-Gram, exact-product entrance, LINEAR smooth discard,
S2 single zero, and S3 restoration. The full unpaid signed source is
still displayed; no spectral/rough/nonzero/Fourier estimate is assumed.
The general-B entrance is a distinct pending internal dependency. -/
theorem uniformAuxiliarySW_one_bounded_original_signed_source_arithmetic_paid
    {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible 0 σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      let atom := F i
      let z := roughZ atom.scale
      let receiver := strictReceiverCutoff z
      let y := originalSmoothTrim atom
      let K := originalNumericKeys atom z
      ‖atom.signedError‖ ^ 2 ≤ 3 * (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        ((retainedSourceKey atom z y k).re + (offDiagonalOmitted atom z y k).re -
          (diagonalRetained atom z y k).re + (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * ((actualS2NonzeroModes atom receiver y k).re -
            (otherRoughCorrection atom receiver y k).re)) +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Ce, hCe, Xe, hXe, hentrance⟩ :=
    uniformAuxiliarySW_one_bounded_original_signed_source_paid_linear_entrance
      F C0 σ κ c0 hadmissible hSW hσ hc0 hShiu A hA
  obtain ⟨Cc, hCc, Xc, hXc, hcorrections⟩ :=
    original_all_key_S2_S3_correction_log_payment 0 σ κ A hσ hσsmall
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
  have hc := hcorrections c0 atom (hadmissible i) hc0
    ((le_max_right _ _).trans hx) z hz
  have hs := original_signed_packets_le_after_S2_S3_split atom z (fun _ => 0)
  simp only [add_zero] at hs
  nlinarith

end
end ImbalancedChen.Part3.OriginalS123CombinedArithmeticPayment20261102
