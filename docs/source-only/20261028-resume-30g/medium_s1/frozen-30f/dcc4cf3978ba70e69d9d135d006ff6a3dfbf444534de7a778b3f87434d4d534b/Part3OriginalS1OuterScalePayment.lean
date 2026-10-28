import ImbalancedChen.Part3OriginalS1OuterCauchy
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the actual beta L2 and the complete all-key outer Cauchy S1 error.
The beta divisor order is fixed before requested logarithmic precision.
No truncation or beta one-bound is used, and no principal variance
estimate is assumed. The resulting scale is the original x^2 square.
-/

namespace ImbalancedChen.Part3.OriginalS1OuterScalePayment20261028
noncomputable section
open Classical Finset Filter Topology
open scoped BigOperators
open OriginalS1OuterCauchy20261028 OriginalS1KeyMultiplicityPayment
open MediumActualPreliminaryCauchy20261028 MediumGlobalDyadicOwnership20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumReceiverCutoffArithmetic20261028

def betaMomentOrder (b : ℕ) : ℕ := (2 ^ b) ^ 2 - 1

def betaLogConstant : ℝ := 2 + Real.log 2

theorem betaLogConstant_pos : 0 < betaLogConstant := by
  dsimp [betaLogConstant]
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem actual_betaL2_le_scale_log {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (hA : MediumAdmissible b σ κ c0 atom)
    (hlog : 1 ≤ Real.log atom.scale) :
    betaL2 atom ≤ 2 * atom.V * betaLogConstant ^ betaMomentOrder b *
      Real.log atom.scale ^ betaMomentOrder b := by
  have hV : 0 < atom.V := lt_of_lt_of_le zero_lt_one hA.2.1
  have hx : 0 < atom.scale := lt_of_lt_of_le zero_lt_one
    (TransposedPrimitiveUPayment.one_le_scale hA)
  have hlogV : 0 ≤ 1 + Real.log (2 * atom.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * atom.V by linarith [hA.2.1])]
  have hcomp := Real.log_le_log hV (TransposedPrimitiveUPayment.V_le_scale hA)
  have hbase : 1 + Real.log (2 * atom.V) ≤ betaLogConstant * Real.log atom.scale := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hV.ne']
    dsimp [betaLogConstant]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg hlog2 (sub_nonneg.mpr hlog)]
  calc
    _ ≤ 2 * atom.V * (1 + Real.log (2 * atom.V)) ^ betaMomentOrder b :=
      mediumAdmissible_beta_norm_sq_sum_le hA
    _ ≤ 2 * atom.V * (betaLogConstant * Real.log atom.scale) ^ betaMomentOrder b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogV hbase _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The actual outside coefficient energy and the actual twice-counted
owner bank have both been included before this logarithmic payment.
Constants and threshold precede all atoms, numeric receivers and trims. -/
theorem actual_outer_S1Error_log_payment (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 < σ → x0 ≤ atom.scale →
        actualOuterS1Error atom z y hA ≤ C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  let p := betaMomentOrder b
  obtain ⟨x1, hx1, hpay⟩ := actual_outerKeyS1Error_log_payment (A + p)
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  have hD := betaLogConstant_pos
  refine ⟨12 * betaLogConstant ^ p, by positivity,
    max x1 x2, hx1.trans_le (le_max_left _ _), ?_⟩
  intro σ κ c0 atom z y hA hσ hx
  have hV : 0 ≤ atom.V := zero_le_one.trans hA.2.1
  have hlog : 1 ≤ Real.log atom.scale := hx2 atom.scale ((le_max_right x1 x2).trans hx)
  have hlog0 : 0 < Real.log atom.scale := by linarith
  have herr0 : 0 ≤ outerKeyS1Error atom z y hA := by
    unfold outerKeyS1Error weightedS1Error
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sum_nonneg (fun k hk => mul_nonneg (by
      dsimp [OriginalSamePsiS1OwnedAtlas.keyY, OriginalSamePsiS1OwnedAtlas.keyD]
      have := hA.2.2.1
      positivity) (norm_nonneg _))
  calc
    _ ≤ 6 * betaL2 atom * outerKeyS1Error atom z y hA :=
      actualOuterS1Error_le_betaL2_outerKeyError atom z y hA
    _ ≤ 6 * (2 * atom.V * betaLogConstant ^ p * Real.log atom.scale ^ p) *
        (atom.V * atom.U ^ 2 / Real.log atom.scale ^ (A + p)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (actual_betaL2_le_scale_log atom hA hlog) (by norm_num))
        (hpay b σ κ c0 atom z y hA hσ ((le_max_left x1 x2).trans hx))
        herr0 (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_natCast]
      unfold MediumAtom.scale
      field_simp [hlog0.ne', (Real.rpow_pos_of_pos hlog0 A).ne']
      ring

/-- This is the original preliminary Cauchy with S1 actually replaced
by its main term and its complete original scale error paid. It is not
a final medium bound: the same-source S2 and S3 still occur literally. -/
theorem retainedSource_norm_sq_le_main_add_log_error (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 < σ → x0 ≤ atom.scale →
        ‖retainedSource atom z y‖ ^ 2 ≤ atlasPrincipalFunctional atom z y hA +
          C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hpay⟩ := actual_outer_S1Error_log_payment b A
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro σ κ c0 atom z y hA hσ hx
  exact (retainedSource_norm_sq_le_main_add_actual_S1Error atom z y hA).trans
    (add_le_add_left (hpay σ κ c0 atom z y hA hσ hx) _)

/-- The source in the manuscript uses p<=z on the smooth side. Its
exact receiver translation is applied to the whole Cauchy, including
its original owner bank and all outside weights. -/
theorem original_numeric_source_norm_sq_le_main_add_log_error (b : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom) (z y : ℝ)
        (hA : MediumAdmissible b σ κ c0 atom),
        0 ≤ z → 0 < σ → x0 ≤ atom.scale →
        ‖originalRetainedSource atom z y‖ ^ 2 ≤
          atlasPrincipalFunctional atom (strictReceiverCutoff z) y hA +
            C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hpay⟩ := retainedSource_norm_sq_le_main_add_log_error b A
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro σ κ c0 atom z y hA hz hσ hx
  have heq : originalRetainedSource atom z y = retainedSource atom (strictReceiverCutoff z) y := by
    unfold originalRetainedSource retainedSource
    rw [originalRetainedRows_eq_receiver atom z y hz]
  rw [heq]
  exact hpay σ κ c0 atom _ y hA hσ hx

end
end ImbalancedChen.Part3.OriginalS1OuterScalePayment20261028
