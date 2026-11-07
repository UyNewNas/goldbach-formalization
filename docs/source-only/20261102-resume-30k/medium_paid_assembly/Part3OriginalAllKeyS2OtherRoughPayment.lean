import ImbalancedChen.Part3OriginalS2OtherRoughLogPayment
import ImbalancedChen.Part3OriginalAllKeyS2SingleZeroPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual J otherRough source is now paid after the original outerL2,
the true arbitrary-B beta square mean and BOTH occupied-key factors.
No correction estimate or final medium estimate is supplied as a premise.
-/

namespace ImbalancedChen.Part3.OriginalAllKeyS2OtherRoughPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalSamePsiS1OwnedAtlas OriginalS1KeyMultiplicityPayment
open OriginalS1OuterCauchy20261028 OriginalS1OuterScalePayment20261028
open ActualMediumVarianceAtomBindingSourceOnly ActualOuterPrincipalScalePayment20261028
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalS2OtherRoughLogPayment
open ImbalancedChen.Part3OriginalS2ShiftedTwelve
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

/-- Only an outside norm budget is named. The original signed residual
and the independently defined otherRoughCorrection are unchanged. -/
def actualOuterS2OtherRoughBudget (atom : MediumAtom) (z : ℝ) : ℝ :=
  ((originalNumericKeys atom z).card : ℝ) *
    ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
      ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖

/-- Local precision A+betaMomentOrder(B)+12 pays the actual beta square
mean and the square of the original key count. The actual roughZ is
essential: no arbitrary-receiver payment is asserted. Constants and one
threshold precede c0, atom, moving residue and occupied key. -/
theorem original_all_key_S2_otherRough_log_payment
    (hShiu : S2PrimitiveShiu) (B : ℕ) (σ κ A : ℝ)
    (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ σ / 100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (c0 : ℝ) (atom : MediumAtom),
        MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
          actualOuterS2OtherRoughBudget atom (roughZ atom.scale) ≤
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p : ℕ := betaMomentOrder B
  let D : ℝ := A + ((p + 12 : ℕ) : ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨Cr, Xr, hCr, hXr, hrough⟩ :=
    exists_actual_S2_otherRough_original_ranges hShiu D hD
  let Cout : ℝ := 12 * Cr * betaLogConstant ^ p * (2 * keyLogConstant) ^ 12
  have hCout : 0 < Cout := by
    have := betaLogConstant_pos
    have := keyLogConstant_pos
    dsimp only [Cout]
    positivity
  refine ⟨Cout, hCout, max Xr (Real.exp 1 + 1), ?_, ?_⟩
  · have he := Real.exp_pos 1
    exact (by linarith : 1 < Real.exp 1 + 1).trans_le (le_max_right _ _)
  intro c0 atom hAdm hc0 hx
  have hxr : Xr ≤ atom.scale := (le_max_left _ _).trans hx
  have hexp : Real.exp 1 ≤ atom.scale := by
    have hh := (le_max_right _ _).trans hx
    linarith
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hexp
  let t := Real.log atom.scale
  let z := roughZ atom.scale
  let K := originalNumericKeys atom z
  have ht : 0 < t := by dsimp only [t]; linarith
  have hV : 0 ≤ atom.V := zero_le_one.trans hAdm.2.1
  have hbeta0 := betaL2_nonneg atom
  have hbeta := actual_betaL2_le_scale_log atom hAdm hlog
  have hcard := originalNumericKeys_card_sq_le_scale_log hAdm hσ.le z hlog
  have hkeyC := keyLogConstant_pos
  have hbetaC := betaLogConstant_pos
  let E : ℝ := 6 * Cr * betaL2 atom * atom.V * atom.U ^ 2 / t ^ D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ K, outerL2 atom k *
      ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ ≤ E := by
    intro k hk
    have hY := keyY_positive hAdm k
    have hr := hrough B σ κ c0 atom k hAdm hσ hσsmall hc0 hκ0 hκ hk hxr
    have hr' : ‖otherRoughCorrection atom (strictReceiverCutoff z)
        (originalSmoothTrim atom) k‖ ≤
        Cr * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D) := by
      convert hr using 1 <;>
        simp only [z, originalSmoothTrim, roughY, fixedDScale, keyY, keyD, t,
          Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg ht.le, div_eq_mul_inv,
          mul_inv_rev] <;> ring
    calc
      _ ≤ (6 * keyY atom k * betaL2 atom) *
          (Cr * atom.V * atom.U ^ 2 / (keyY atom k * t ^ D)) :=
        mul_le_mul (outerL2_le_actual_Y_betaL2 atom k hAdm) hr'
          (norm_nonneg _) (by positivity)
      _ = E := by
        dsimp only [E]
        field_simp [hY.ne', (Real.rpow_pos_of_pos ht D).ne'] <;> ring
  calc
    actualOuterS2OtherRoughBudget atom (roughZ atom.scale) ≤ (K.card : ℝ) ^ 2 * E := by
      unfold actualOuterS2OtherRoughBudget
      change (K.card : ℝ) * (∑ k ∈ K, _) ≤ _
      calc
        _ ≤ (K.card : ℝ) * (∑ _k ∈ K, E) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hterm) (Nat.cast_nonneg _)
        _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((2 * keyLogConstant) ^ 12 * t ^ 12) *
        (6 * Cr * (2 * atom.V * betaLogConstant ^ p * t ^ p) *
          atom.V * atom.U ^ 2 / t ^ D) := by
      have hEupper : E ≤
          6 * Cr * (2 * atom.V * betaLogConstant ^ p * t ^ p) *
            atom.V * atom.U ^ 2 / t ^ D := by
        dsimp only [E]
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg ht.le D)
        have hh := mul_le_mul_of_nonneg_left hbeta
          (show 0 ≤ 6 * Cr * atom.V * atom.U ^ 2 by positivity)
        convert hh using 1 <;> ring
      exact mul_le_mul hcard hEupper hE (by positivity)
    _ = Cout * atom.scale ^ 2 / t ^ A := by
      dsimp only [Cout, D]
      rw [Real.rpow_add ht A ((p + 12 : ℕ) : ℝ), Real.rpow_natCast, pow_add]
      unfold MediumAtom.scale
      field_simp [ht.ne', (Real.rpow_pos_of_pos ht A).ne', pow_ne_zero p ht.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalAllKeyS2OtherRoughPayment20261102
