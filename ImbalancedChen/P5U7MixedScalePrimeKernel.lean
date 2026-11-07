import ImbalancedChen.P5U7MixedScaleLogTransport

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native normalized scalar prime-main comparison at mixed scales. The error
is explicitly paid by |m/n-beta| and 1/log n, uniformly in a. Arithmetic
marked-pair summation and source-CDF reconstruction are separate consumers.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology

def p5U7MixedScaleKernelConstant (alpha beta0 : ℝ) : ℝ :=
  max (1/alpha) ((-Real.log beta0)/alpha^2)

/-- Exact native normalization, with the cutoff ratio m/n kept literal. -/
theorem p5U7MixedScale_prime_main_error (n m a alpha beta0 beta : ℝ)
    (hn : 1 < n) (ha : 0 < a) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) (hx : n^alpha ≤ m/a) :
    |(Real.log n/n)*((m/a)/Real.log (m/a))-
      beta*(1/a)*(Real.log n/Real.log (n/a))| ≤
      (1/a)*(|m/n-beta|/alpha+(-Real.log beta0)/(alpha^2*Real.log n)) := by
  obtain ⟨_hm,hln,hlx,hly,_hlow,_hhigh,_hs,_h0,_hB⟩ :=
    p5U7MixedScale_log_geometry n m a alpha beta0 hn ha halpha hbeta0 hrho0 hrho1 hx
  obtain ⟨_hLm0,_hLmB,hLn0,hLnB⟩ :=
    p5U7MixedScale_log_kernel_bounds n m a alpha beta0 hn ha halpha hbeta0 hrho0 hrho1 hx
  have hdiff := p5U7MixedScale_reciprocal_log_error n m a alpha beta0
    hn ha halpha hbeta0 hrho0 hrho1 hx
  let rho : ℝ := m/n
  let Rm : ℝ := Real.log n/Real.log (m/a)
  let Rn : ℝ := Real.log n/Real.log (n/a)
  let E : ℝ := (-Real.log beta0)/(alpha^2*Real.log n)
  have hrho : 0 ≤ rho := (hbeta0.trans_le hrho0).le
  have hbeta1 : beta0 ≤ 1 := hrho0.trans hrho1
  have hE : 0 ≤ E := div_nonneg
    (neg_nonneg.mpr (Real.log_nonpos hbeta0.le hbeta1))
    (mul_nonneg (sq_nonneg alpha) hln.le)
  have hleft : |(rho-beta)*Rn| ≤ |rho-beta|/alpha := by
    rw [abs_mul,abs_of_nonneg hLn0]
    have hh := mul_le_mul_of_nonneg_left hLnB (abs_nonneg (rho-beta))
    exact hh.trans_eq (by ring)
  have hright : |rho*(Rm-Rn)| ≤ E := by
    rw [abs_mul,abs_of_nonneg hrho]
    exact (mul_le_mul_of_nonneg_left hdiff hrho).trans
      ((mul_le_mul_of_nonneg_right hrho1 hE).trans_eq (one_mul E))
  have hsum : |(rho-beta)*Rn+rho*(Rm-Rn)| ≤ |rho-beta|/alpha+E :=
    (abs_add_le _ _).trans (add_le_add hleft hright)
  have hn0 : 0 < n := zero_lt_one.trans hn
  have hid : (Real.log n/n)*((m/a)/Real.log (m/a))-
      beta*(1/a)*(Real.log n/Real.log (n/a)) =
      (1/a)*((rho-beta)*Rn+rho*(Rm-Rn)) := by
    dsimp only [rho,Rn,Rm]
    field_simp [hn0.ne',ha.ne',hlx.ne',hly.ne']
    <;> ring
  rw [hid,abs_mul,abs_of_nonneg (one_div_nonneg.mpr ha.le)]
  exact mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr ha.le)

/-- Explicit coefficient form in the native rate |m/n-beta|+1/log n. -/
theorem p5U7MixedScale_prime_main_rate_bound (n m a alpha beta0 beta : ℝ)
    (hn : 1 < n) (ha : 0 < a) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1) (hx : n^alpha ≤ m/a) :
    |(Real.log n/n)*((m/a)/Real.log (m/a))-
      beta*(1/a)*(Real.log n/Real.log (n/a))| ≤
      (1/a)*p5U7MixedScaleKernelConstant alpha beta0*(|m/n-beta|+1/Real.log n) := by
  have hln : 0 < Real.log n := Real.log_pos hn
  have h1 := mul_le_mul_of_nonneg_right
    (le_max_left (1/alpha) ((-Real.log beta0)/alpha^2)) (abs_nonneg (m/n-beta))
  have h2 := mul_le_mul_of_nonneg_right
    (le_max_right (1/alpha) ((-Real.log beta0)/alpha^2))
    (one_div_nonneg.mpr hln.le)
  have heq : |m/n-beta|/alpha+(-Real.log beta0)/(alpha^2*Real.log n) =
      (1/alpha)*|m/n-beta|+((-Real.log beta0)/alpha^2)*(1/Real.log n) := by
    field_simp [halpha.ne',hln.ne']
    <;> ring
  have hrate : |m/n-beta|/alpha+(-Real.log beta0)/(alpha^2*Real.log n) ≤
      p5U7MixedScaleKernelConstant alpha beta0*(|m/n-beta|+1/Real.log n) := by
    rw [heq]
    exact (add_le_add h1 h2).trans_eq (by dsimp only [p5U7MixedScaleKernelConstant]; ring)
  have hbound := p5U7MixedScale_prime_main_error n m a alpha beta0 beta
    hn ha halpha hbeta0 hrho0 hrho1 hx
  exact hbound.trans ((mul_le_mul_of_nonneg_left hrate (one_div_nonneg.mpr ha.le)).trans_eq (by ring))
end
end ImbalancedChen
