import ImbalancedChen.Part3MediumOriginalRestorationLedger
import ImbalancedChen.Part3OriginalCompleteS123Ledger
import ImbalancedChen.Part3ActualOuterPrincipalScalePayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the actual S3 restoration packet after the original outside L2
multiplier and BOTH owner-bank multiplicities. Insert this payment in
the independently defined actualResidualFunctional, leaving every other
S2/S3 packet explicit. No auxiliary SW, variance or spectral estimate
is needed for this restoration payment.
-/

namespace ImbalancedChen.Part3.MediumOriginalAllKeyRestorationPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumOriginalRestorationLogPayment20261102 MediumOriginalRestorationLedger20261102
open MediumActualDiagonalDivisorPayment20261028 MediumActualRestorationPayment20261028
open MediumReceiverCutoffArithmetic20261028 MediumGlobalDyadicOwnership20261028
open MediumActualS3ZeroCentering20261028
open OriginalSamePsiS1OwnedAtlas OriginalS1KeyMultiplicityPayment
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open OriginalPrincipalVarianceInOuterCauchy20261028 OriginalCompleteS123Ledger20261028
open OriginalWholePoissonCarrierReindex20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

/-- This is precisely the original outside weight on the paid source,
not a replacement for actualResidualFunctional. -/
def actualOuterRestorationBudget (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ‖restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖

/-- Request precision A+betaMomentOrder(B)+12 ONCE, before every atom
and occupied key. The Y from outerL2 cancels the actual V(D) denominator;
the ordinary beta mean supplies the second M, giving the original x^2. -/
theorem original_all_key_S3_restoration_log_payment
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualOuterRestorationBudget atom z ≤
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let e : ℕ := p + 12
  let D : ℝ := A + (e : ℝ)
  obtain ⟨x1, hx1, hrest⟩ := exists_original_S3_restoration_log_payment σ κ D hσ hσsmall
  let Cout : ℝ := 36 * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]
    positivity
  refine ⟨Cout, hCout, max x1 (Real.exp 1), hx1.trans_le (le_max_left _ _), ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  have hx1' : x1 ≤ atom.scale := (le_max_left _ _).trans hx
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx)
  let t := Real.log atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hQ : 0 < atom.Q1 := zero_lt_one.trans_le hAdm.2.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ.le z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 18 * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K,
      outerL2 atom k *
        ‖restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤ E := by
    intro k hk
    have hY := keyY_positive hAdm k
    have hk' : k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) := by
      simpa only [K, originalNumericKeys, originalSmoothTrim, roughY] using hk
    have hr := hrest B c0 atom hAdm hc0 hx1' z k hz hk'
    have hr' : ‖restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤
        3 * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hr using 1 <;>
        simp only [originalSmoothTrim, roughY, actualVScale, t, div_eq_mul_inv,
          mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (3 * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hr'
          (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterRestorationBudget atom z ≤ (K.card : ℝ) ^ 2 * E := by
      unfold actualOuterRestorationBudget
      change (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (18 * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D) := by
      have hEupper : E ≤
          18 * (2 * atom.V * betaLogConstant ^ p * t ^ p) * atom.V * atom.U ^ 2 / t ^ D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 18 * atom.V * atom.U ^ 2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout * atom.scale ^ 2 / t ^ A := by
      dsimp only [Cout, D, e]
      rw [Real.rpow_add ht A ((p + 12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

/-- The exact existing aggregate is retained. The correction norm is
split by an actual source identity; no unestimated packet disappears. -/
theorem actualResidualFunctional_le_after_restoration
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z : ℝ)
    (hAdm : MediumAdmissible B σ κ c0 atom) :
    actualResidualFunctional atom z ≤
      ((originalNumericKeys atom z).card : ℝ) *
        (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
          (‖retainedSourceKey atom z (originalSmoothTrim atom) k‖ +
            ‖offDiagonalOmitted atom z (originalSmoothTrim atom) k‖ +
            ‖diagonalRetained atom z (originalSmoothTrim atom) k‖ +
            ‖roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            ‖genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            2 * (‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
              ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
              ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
              ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖))) +
        actualOuterRestorationBudget atom z := by
  apply (actualResidualFunctional_le_original_packet_norms atom z hAdm).trans
  unfold actualOuterRestorationBudget
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  have hrem : ‖remainingCorrectionKey atom z (originalSmoothTrim atom) k‖ ≤
      ‖restorationCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
      ‖offDiagonalOmitted atom z (originalSmoothTrim atom) k‖ +
      ‖diagonalRetained atom z (originalSmoothTrim atom) k‖ := by
    rw [remainingCorrectionKey_eq_restoration_omitted_diagonal]
    exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
  linarith

/-- Final original aggregate consumer of the new payment. This theorem
does NOT claim the remaining displayed source norms are small. -/
theorem exists_actualResidualFunctional_restoration_paid
    (B : ℕ) (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
        ∀ z : ℝ, 0 ≤ z →
          actualResidualFunctional atom z ≤
            ((originalNumericKeys atom z).card : ℝ) *
              (∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
                (‖retainedSourceKey atom z (originalSmoothTrim atom) k‖ +
                  ‖offDiagonalOmitted atom z (originalSmoothTrim atom) k‖ +
                  ‖diagonalRetained atom z (originalSmoothTrim atom) k‖ +
                  ‖roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
                  ‖genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
                  2 * (‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
                    ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
                    ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
                    ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖))) +
              C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hpay⟩ := original_all_key_S3_restoration_log_payment B σ κ A hσ hσsmall
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro c0 atom hAdm hc0 hx z hz
  exact (actualResidualFunctional_le_after_restoration atom z hAdm).trans
    (add_le_add_left (hpay c0 atom hAdm hc0 hx z hz) _)

end
end ImbalancedChen.Part3.MediumOriginalAllKeyRestorationPayment20261102
