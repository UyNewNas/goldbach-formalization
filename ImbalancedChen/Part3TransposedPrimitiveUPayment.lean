import ImbalancedChen.Part3TransposedPrimitiveUMoment
import ImbalancedChen.Part3SignedDivisorDeletion

/-!
# Actual power and logarithmic payment for the transposed U residual

The logarithms of the original beta length and the complete physical cap
are bounded by one fixed multiple of log X. Their fixed natural powers are
then absorbed by Mathlib's proved logarithm-versus-positive-power limit.
The original medium monomial gives U squared < X^(1-8 sigma), hence U at
most X^(1/2). Together with X=UV this pays the actual original-beta L2 times
the literal U-P0 error with an X^(7/4) bound, then every requested log power.

Only sigma>0 is added at payment, exactly a gate of the final obligation.
No small-sigma strengthening, remaining error budget or coefficient premise
is used. The signed residue, original scales and local cutoff mass persist.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Topology
open scoped BigOperators
open TransposedZeroCovariance TransposedPrimitiveUMoment

namespace TransposedPrimitiveUPayment

theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ _ := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

theorem V_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : d.V ≤ d.scale := by
  change d.V ≤ d.U * d.V
  exact le_mul_of_one_le_left (by linarith [hd.2.1]) hd.1

theorem physicalFactorCap_le_eight_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.physicalFactorCap ≤ 8 * d.scale := by
  calc
    _ ≤ d.U * d.physicalFactorCap :=
      le_mul_of_one_le_left (by linarith [d.one_le_physicalFactorCap hd]) hd.1
    _ ≤ 8 * d.scale ^ (1 - 9 * sigma) := d.U_mul_physicalFactorCap_le hd
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (one_le_scale hd)
          (show 1 - 9 * sigma ≤ 1 by linarith)) (by norm_num)

theorem U_le_scale_half
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.U ≤ d.scale ^ (1 / 2 : ℝ) := by
  have hx : 0 ≤ d.scale := zero_le_one.trans (one_le_scale hd)
  have hsq : d.U ^ 2 ≤ d.scale := by
    apply (U_sq_lt_scale_rpow hd).le.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (one_le_scale hd)
        (show 1 - 8 * sigma ≤ 1 by linarith)
  have hp : (d.scale ^ (1 / 2 : ℝ)) ^ 2 = d.scale := by
    simpa using Real.rpow_inv_natCast_pow (n := 2) hx (by norm_num : (2 : ℕ) ≠ 0)
  exact (sq_le_sq₀ (by linarith [hd.1] : 0 ≤ d.U)
    (Real.rpow_nonneg hx (1 / 2 : ℝ))).mp (by rw [hp]; exact hsq)

theorem eventually_const_log_rpow_le_rpow (C A : ℝ) (hC : 0 ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ A ≤ x ^ epsilon := by
  have hb := ((isLittleO_log_rpow_rpow_atTop A hepsilon).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (by positivity :
    0 ≤ C * Real.log x ^ A), abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)]
      using hx

/-- One threshold pays both actual logarithm costs, uniformly before atoms. -/
theorem eventually_actual_log_cost_le_rpow (p s : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (1 + Real.log (2 * d.V)) ^ p *
        (1 + Real.log d.physicalFactorCap) ^ s ≤ d.scale ^ epsilon := by
  let D : ℝ := 2 + Real.log 8
  have hD : 0 < D := by
    dsimp [D]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  obtain ⟨x1, hx1⟩ := eventually_atTop.mp
    (eventually_const_log_rpow_le_rpow (D ^ (p + s)) (p + s) (by positivity) hepsilon)
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  refine ⟨max 2 (max x1 x2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro B kappa c0 d hd hx
  have hx0 : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlog : 1 ≤ Real.log d.scale :=
    hx2 ((le_max_right x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))
  have hbase (y : ℝ) (hy : 0 < y) (hyX : y ≤ 8 * d.scale) :
      1 + Real.log y ≤ D * Real.log d.scale := by
    have hh := Real.log_le_log hy hyX
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx0.ne'] at hh
    dsimp [D]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hlogV : 1 + Real.log (2 * d.V) ≤ D * Real.log d.scale := by
    apply hbase _ (by linarith [hd.2.1])
    calc
      2 * d.V ≤ 2 * d.scale := mul_le_mul_of_nonneg_left (V_le_scale hd) (by norm_num)
      _ ≤ _ := by nlinarith [hx0]
  have hlogCap : 1 + Real.log d.physicalFactorCap ≤ D * Real.log d.scale :=
    hbase _ (zero_lt_one.trans_le (d.one_le_physicalFactorCap hd))
      (physicalFactorCap_le_eight_scale hsigma hd)
  have hV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hcap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ (D * Real.log d.scale) ^ p * (D * Real.log d.scale) ^ s :=
      mul_le_mul (pow_le_pow_left₀ hV0 hlogV p) (pow_le_pow_left₀ hcap0 hlogCap s)
        (pow_nonneg hcap0 s) (by positivity)
    _ = D ^ (p + s) * Real.log d.scale ^ ((p + s : ℕ) : ℝ) := by
      rw [← pow_add, mul_pow, Real.rpow_natCast]
    _ ≤ _ := hx1 ((le_max_left x1 x2).trans ((le_max_right 2 (max x1 x2)).trans hx))

theorem eventually_const_rpow_two_le_logBudget (C A : ℝ) (hC : 0 ≤ C)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, C * x ^ (2 - delta) ≤ x ^ 2 / (Real.log x) ^ A := by
  filter_upwards [eventually_const_log_rpow_le_rpow C A hC hdelta,
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hpay hx1 hlog
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < Real.log x) A)).mpr
  calc
    _ = (C * (Real.log x) ^ A) * x ^ (2 - delta) := by ring
    _ ≤ x ^ delta * x ^ (2 - delta) :=
      mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hx0.le _)
    _ = x ^ (2 : ℝ) := by
      rw [← Real.rpow_add hx0, show delta + (2 - delta) = 2 by ring]
    _ = _ := Real.rpow_natCast _ 2

/-- Genuine power saving after multiplication by the actual beta L2 cost. -/
theorem actual_betaL2_mul_U_error_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
            C * d.scale ^ (7 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := actual_betaL2_mul_U_error_bound
  obtain ⟨x0, hx0, hcost⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 24 sigma hsigma (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨C, hC, x0, hx0, fun d hd hx ↦ ?_⟩
  have hxpos : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hlogV0 : 0 ≤ 1 + Real.log (2 * d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  have hlogCap0 : 0 ≤ 1 + Real.log d.physicalFactorCap := by
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  calc
    _ ≤ C * d.V * d.U ^ 2 *
        (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 24 := hbound B sigma kappa c0 d hd
    _ = C * d.scale * d.U *
        ((1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
          (1 + Real.log d.physicalFactorCap) ^ 24) := by
      unfold MediumAtom.scale
      ring
    _ ≤ C * d.scale * (d.scale ^ (1 / 2 : ℝ)) * d.scale ^ (1 / 4 : ℝ) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (U_le_scale_half hsigma hd) (by positivity))
        (hcost B kappa c0 d hd hx) (by positivity) (by positivity)
    _ = C * (d.scale ^ (1 : ℝ) * d.scale ^ (1 / 2 : ℝ) *
        d.scale ^ (1 / 4 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]; norm_num

/-- Every requested logarithmic decay is paid, before the actual atom. -/
theorem actual_betaL2_mul_U_error_log_payment (B : ℕ) (sigma kappa c0 A : ℝ)
    (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
            d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hbound⟩ :=
    actual_betaL2_mul_U_error_power_bound B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le
      (by norm_num : (0 : ℝ) < 1 / 4))
  refine ⟨max x1 x2, lt_of_lt_of_le hx1 (le_max_left _ _), fun d hd hx ↦ ?_⟩
  apply (hbound d hd ((le_max_left _ _).trans hx)).trans
  convert hx2 ((le_max_right _ _).trans hx) using 1 <;> norm_num

end TransposedPrimitiveUPayment

end

end ImbalancedChen.Part3
