import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact fixed logarithmic loss of the preceding ORIGINAL profiles. The
threshold precedes U,V, labels, frequencies and divisor pairs. The final
theorem pays the last E4 POWER MONOMIAL under its original scale gates;
it does not assume or assert a physical rho modulus-moment supplier.
-/
namespace ImbalancedChen.Part3.TwoLongMellinLogBudget
noncomputable section
open Classical Filter Topology
open ImbalancedChen.Part3.TwoLongTransitionMellinN2
open ImbalancedChen.Part3.TwoLongHBMellinBrunProfiles
open ImbalancedChen.Part3.TwoLongNaturalInternalP2

def logExponent (B K : ℕ) : ℕ := 2+K*4+B*4
def logConstant : ℝ := 256*internalP2Constant*profileConstant^2

theorem logConstant_nonneg : 0 ≤ logConstant := by
  have h := internalP2Constant_pos.le
  unfold logConstant
  positivity

theorem logSize_le {x U : ℝ} (hx : 1 ≤ Real.log x) (hU : 1 ≤ U) (hUx : U ≤ x) :
    logSize U ≤ 4*Real.log x := by
  have hlogU := Real.log_nonneg hU
  have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hU) hUx
  unfold logSize
  rw [abs_of_nonneg hlogU]
  linarith

/-- delta=log(x)^(-B), H=log(x)^K. The four derivative powers and
four frequency powers are explicit; original log slots add at most two. -/
theorem pairCost_log_bound (B K : ℕ) {x U V : ℝ}
    (hx : 1 ≤ Real.log x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ x) (hVx : V ≤ x) :
    pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) ≤
      logConstant*(Real.log x)^(logExponent B K) := by
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hx
  have hpow : 1 ≤ (Real.log x)^K := one_le_pow₀ hx
  have hUL := logSize_le hx hU hUx
  have hVL := logSize_le hx hV hVx
  have hUn := zero_le_one.trans (logSize_one_le U)
  have hVn := zero_le_one.trans (logSize_one_le V)
  have hP := internalP2Constant_pos.le
  have hfreq : (1+(Real.log x)^K)^4 ≤ (2*(Real.log x)^K)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  unfold pairCost
  calc
    _ ≤ internalP2Constant*profileConstant^2*(4*Real.log x)*(4*Real.log x)*
        (2*(Real.log x)^K)^4 / (((Real.log x)^B)⁻¹)^4 := by gcongr
    _ = logConstant*(Real.log x)^(logExponent B K) := by
      unfold logConstant logExponent
      rw [inv_pow, div_inv_eq_mul]
      simp only [pow_add, pow_mul, mul_pow]
      ring

def scaledLogConstant (c : ℝ) : ℝ :=
  16*(4+|Real.log c|)^2*internalP2Constant*profileConstant^2

theorem scaledLogConstant_nonneg (c : ℝ) : 0 ≤ scaledLogConstant c := by
  have h := internalP2Constant_pos.le
  unfold scaledLogConstant
  positivity

/-- Fixed comparability constants in x ~ MUV are preserved. No original
scale condition U<=c*x is silently strengthened to U<=x. -/
theorem logSize_le_scaled {c x U : ℝ} (hc : 0 < c) (hx0 : 0 < x)
    (hx : 1 ≤ Real.log x) (hU : 1 ≤ U) (hUx : U ≤ c*x) :
    logSize U ≤ (4+|Real.log c|)*Real.log x := by
  have hlogU := Real.log_nonneg hU
  have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one hU) hUx
  rw [Real.log_mul hc.ne' hx0.ne'] at hh
  have hp := mul_le_mul_of_nonneg_left hx (abs_nonneg (Real.log c))
  unfold logSize
  rw [abs_of_nonneg hlogU]
  nlinarith [le_abs_self (Real.log c)]

theorem pairCost_scaled_log_bound (B K : ℕ) {c x U V : ℝ}
    (hc : 0 < c) (hx0 : 0 < x) (hx : 1 ≤ Real.log x)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUx : U ≤ c*x) (hVx : V ≤ c*x) :
    pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) ≤
      scaledLogConstant c*(Real.log x)^(logExponent B K) := by
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hx
  have hpow : 1 ≤ (Real.log x)^K := one_le_pow₀ hx
  have hUL := logSize_le_scaled hc hx0 hx hU hUx
  have hVL := logSize_le_scaled hc hx0 hx hV hVx
  have hUn := zero_le_one.trans (logSize_one_le U)
  have hVn := zero_le_one.trans (logSize_one_le V)
  have hP := internalP2Constant_pos.le
  unfold pairCost
  calc
    _ ≤ internalP2Constant*profileConstant^2*
        ((4+|Real.log c|)*Real.log x)*((4+|Real.log c|)*Real.log x)*
        (2*(Real.log x)^K)^4 / (((Real.log x)^B)⁻¹)^4 := by
      gcongr <;> first | assumption | linarith
    _ = scaledLogConstant c*(Real.log x)^(logExponent B K) := by
      unfold scaledLogConstant logExponent
      rw [inv_pow, div_inv_eq_mul]
      simp only [pow_add, pow_mul, mul_pow]
      ring

theorem eventually_schedule (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      0 < ((Real.log x)^B)⁻¹ ∧ ((Real.log x)^B)⁻¹ ≤ 1/4 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)] with x hx
  have hlog : 0 < Real.log x := by linarith
  have hp : 4 ≤ (Real.log x)^B := by
    calc
      4 ≤ Real.log x := hx
      _ = (Real.log x)^1 := by rw [pow_one]
      _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ Real.log x) hB
  refine ⟨by linarith, inv_pos.mpr (pow_pos hlog _), ?_⟩
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp

/-- A primary proved Mathlib logarithm/power limit; no distribution
estimate or final E4 bound is an input. -/
theorem eventually_fixed_log_le_power (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, C*(Real.log x)^k ≤ x^eta := by
  have hb := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) heta).const_mul_left C).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (by positivity : 0 ≤ C*(Real.log x)^k),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) eta)] using hx

/-- Uniform absorption of the profile cost with any fixed positive power
reserve. B and K are fixed BEFORE this threshold; U,V stay quantified
AFTER it. This has the original required quantifier order. -/
theorem eventually_pairCost_power_payment (B K E A : ℕ)
    (c : ℝ) (hc : 0 < c) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧ ∀ U V : ℝ,
      1 ≤ U → 1 ≤ V → U ≤ c*x → V ≤ c*x →
      pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)*
        x^(1-eta)*(Real.log x)^E ≤ x/(Real.log x)^A := by
  filter_upwards [eventually_fixed_log_le_power (scaledLogConstant c) (scaledLogConstant_nonneg c)
    (logExponent B K+E+A) heta,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
      with x hpay hx hlog
  refine ⟨hx, hlog, ?_⟩
  intro U V hU hV hUx hVx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hlog
  apply (le_div_iff₀ (pow_pos hl0 A)).2
  calc
    _ ≤ (scaledLogConstant c*(Real.log x)^(logExponent B K))*x^(1-eta)*
        (Real.log x)^E*(Real.log x)^A := by
      gcongr
      exact pairCost_scaled_log_bound B K hc hx0 hlog hU hV hUx hVx
    _ = (scaledLogConstant c*(Real.log x)^(logExponent B K+E+A))*x^(1-eta) := by
      simp only [pow_add]
      ring
    _ ≤ x^eta*x^(1-eta) := mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hx0.le _)
    _ = x := by rw [← Real.rpow_add hx0, show eta+(1-eta)=1 by ring, Real.rpow_one]

/-- The exact final E4 monomial M*y^2*D^(3/2), with the original strict
two-long reserve. epsilon is the chosen fixed allowance in y=x^o(1).
No hidden desired discrepancy bound, profile norm or modulus moment is
assumed. Supplying the actual physical rho moment is still necessary. -/
theorem eventually_twoLong_E4_monomial (B K E A : ℕ)
    (c : ℝ) (hc : 0 < c) (zeta theta epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hmargin : 40*zeta+2*epsilon+3*theta/2 < 1) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧
      ∀ M y D U V : ℝ, 0 ≤ M → 0 ≤ y → 0 ≤ D →
        M ≤ x^(40*zeta) → y ≤ x^epsilon → D ≤ x^theta →
        1 ≤ U → 1 ≤ V → U ≤ c*x → V ≤ c*x →
        pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)*
          (M*y^2*D^(3/2 : ℝ))*(Real.log x)^E ≤ x/(Real.log x)^A := by
  let eta := 1-(40*zeta+2*epsilon+3*theta/2)
  have heta : 0 < eta := by dsimp [eta]; linarith
  filter_upwards [eventually_pairCost_power_payment B K E A c hc heta] with x hx
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro M y D U V hM hy hD hMx hyx hDx hU hV hUx hVx
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hmon : M*y^2*D^(3/2 : ℝ) ≤ x^(1-eta) := by
    calc
      _ ≤ x^(40*zeta)*(x^epsilon)^2*(x^theta)^(3/2 : ℝ) := by
        gcongr
      _ = x^(1-eta) := by
        rw [← Real.rpow_natCast (x^epsilon) 2,
          ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le,
          ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1
        dsimp [eta]
        ring
  calc
    _ ≤ pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)*
        x^(1-eta)*(Real.log x)^E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmon (pairCost_nonneg _ _ _ _))
        (pow_nonneg (by linarith [hx.2.1]) _)
    _ ≤ _ := hx.2.2 U V hU hV hUx hVx

end
end ImbalancedChen.Part3.TwoLongMellinLogBudget
