import ImbalancedChen.Part3TransposedPrimitiveVMoment
import ImbalancedChen.Part3TransposedPrimitiveUPayment

/-!
# Actual power and logarithmic payment for the transposed mixed residual

The honest mixed-term error contains both original-alpha masses and costs
U squared times the complete physical cap. After the actual original-beta
L2 moment its scale is V U squared cap = X (U cap). The owned medium
geometry bounds U cap by 8 X^(1-9 sigma). Absorbing all fixed logarithms
by X^sigma leaves the proved power saving X^(2-8 sigma).

The resulting threshold precedes every actual atom. Only the sigma>0 gate
already in RestrictedMediumObligation is used. No missing residual budget,
extra alpha cancellation, smaller carrier or mass normalization is assumed.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Topology
open scoped BigOperators
open TransposedZeroCovariance TransposedPrimitiveVMoment TransposedPrimitiveUPayment

namespace TransposedPrimitiveVPayment

theorem actual_betaL2_mul_V_error_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
            C * d.scale ^ (2 - 8 * sigma) := by
  obtain ⟨C, hC, hbound⟩ := actual_betaL2_mul_V_error_bound
  obtain ⟨x0, hx0, hcost⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 14 sigma hsigma hsigma
  refine ⟨8 * C, by positivity, x0, hx0, fun d hd hx ↦ ?_⟩
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlogV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hlogCap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ C * d.V * d.U ^ 2 * d.physicalFactorCap *
        (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 14 := hbound B sigma kappa c0 d hd
    _ = C * d.scale * (d.U * d.physicalFactorCap) *
        ((1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 14) := by
      unfold MediumAtom.scale
      ring
    _ ≤ (C * d.scale * (8 * d.scale ^ (1 - 9 * sigma))) * d.scale ^ sigma :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (d.U_mul_physicalFactorCap_le hd) (by positivity))
        (hcost B kappa c0 d hd hx) (by positivity) (by positivity)
    _ = (8 * C) * (d.scale ^ (1 : ℝ) * d.scale ^ (1 - 9 * sigma) *
        d.scale ^ sigma) := by rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      congr 2
      ring

theorem actual_betaL2_mul_V_error_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
            d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hbound⟩ :=
    actual_betaL2_mul_V_error_power_bound B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (by linarith : 0 < 8 * sigma))
  refine ⟨max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), fun d hd hx ↦ ?_⟩
  exact (hbound d hd ((le_max_left _ _).trans hx)).trans
    (hx2 ((le_max_right _ _).trans hx))

/-- Both literal primitive-center remainders are genuinely paid after the
actual original-beta moment. The full centered identity can use this bound
without a new remaining-budget premise. -/
theorem actual_betaL2_mul_UV_error_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ +
          2 * ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖) ≤
              3 * (d.scale ^ 2 / (Real.log d.scale) ^ A) := by
  obtain ⟨xU, hxU, hU⟩ :=
    actual_betaL2_mul_U_error_log_payment B sigma kappa c0 A hsigma
  obtain ⟨xV, _hxV, hV⟩ :=
    actual_betaL2_mul_V_error_log_payment B sigma kappa c0 A hsigma
  refine ⟨max xU xV, lt_of_lt_of_le hxU (le_max_left _ _), fun d hd hx ↦ ?_⟩
  have hu := hU d hd ((le_max_left _ _).trans hx)
  have hv := hV d hd ((le_max_right _ _).trans hx)
  calc
    _ = (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ +
          2 * ((∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
            ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
              d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖) := by ring
    _ ≤ d.scale ^ 2 / (Real.log d.scale) ^ A +
        2 * (d.scale ^ 2 / (Real.log d.scale) ^ A) :=
      add_le_add hu (mul_le_mul_of_nonneg_left hv (by norm_num))
    _ = _ := by ring

end TransposedPrimitiveVPayment

end

end ImbalancedChen.Part3
