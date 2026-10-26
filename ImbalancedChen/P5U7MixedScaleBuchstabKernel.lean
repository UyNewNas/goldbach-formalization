import ImbalancedChen.P5U7MixedScaleBuchstabArgument

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Required native normalized Buchstab row comparison at mixed cutoffs.
The coefficient is exactly one in both explicit error terms. Target n
normalization and original-row reference remain fixed; only the cutoff
m changes. Actual range hypotheses exclude every below-one extension.
-/
namespace ImbalancedChen
noncomputable section
open LiLiuPrereqBuchstab

/-- Pure scalar native row transport. The range is the exact original
[1,132/59], and the log denominator lower exponent is the SOURCE d.
No marked-pair sum, arithmetic source/CDF limit or density is an input. -/
theorem p5U7MixedScale_buchstab_main_error (n m a z d beta0 beta : ℝ)
    (hn : 1 < n) (ha : 0 < a) (hz : 1 < z) (hd : 0 < d) (hzpow : n^d ≤ z)
    (hbeta0 : 0 < beta0) (hrho0 : beta0 ≤ m/n) (hrho1 : m/n ≤ 1)
    (hsM : 1 ≤ Real.log (m/a)/Real.log z)
    (horder : Real.log (m/a)/Real.log z ≤ Real.log (n/a)/Real.log z)
    (hsN : Real.log (n/a)/Real.log z ≤ (132/59 : ℝ)) :
    |(Real.log n/n)*((m/a)*buchstab (Real.log (m/a)/Real.log z)/Real.log z)-
      beta*((Real.log n/n)*((n/a)*buchstab (Real.log (n/a)/Real.log z)/Real.log z))| ≤
      (1/a)*(|m/n-beta|/d+(-Real.log beta0)/(d^2*Real.log n)) := by
  obtain ⟨_hm,hln,hlz,_hlow,hL0,_hLbound,_hshift,_hgap0,_hgap⟩ :=
    p5U7MixedScale_buchstab_log_geometry n m a z d beta0
      hn ha hz hd hzpow hbeta0 hrho0 hrho1
  obtain ⟨_hW0,_hW1,hsize,hscaled⟩ :=
    p5U7MixedScale_buchstab_scalar_bounds n m a z d beta0
      hn ha hz hd hzpow hbeta0 hrho0 hrho1 hsM horder hsN
  let rho : ℝ := m/n
  let L : ℝ := Real.log n/Real.log z
  let Wm : ℝ := buchstab (Real.log (m/a)/Real.log z)
  let Wn : ℝ := buchstab (Real.log (n/a)/Real.log z)
  let E : ℝ := (-Real.log beta0)/(d^2*Real.log n)
  have hrho : 0 ≤ rho := (hbeta0.trans_le hrho0).le
  have hE : 0 ≤ E := div_nonneg
    (neg_nonneg.mpr (Real.log_nonpos hbeta0.le (hrho0.trans hrho1)))
    (mul_nonneg (sq_nonneg d) hln.le)
  have hleft : |(rho-beta)*(L*Wn)| ≤ |rho-beta|/d := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left hsize (abs_nonneg (rho-beta))
    exact hh.trans_eq (by ring)
  have hright : |rho*(L*(Wm-Wn))| ≤ E := by
    rw [abs_mul,abs_of_nonneg hrho,abs_mul,abs_of_nonneg hL0]
    exact (mul_le_mul_of_nonneg_left hscaled hrho).trans
      ((mul_le_mul_of_nonneg_right hrho1 hE).trans_eq (one_mul E))
  have hsum : |(rho-beta)*(L*Wn)+rho*(L*(Wm-Wn))| ≤ |rho-beta|/d+E :=
    (abs_add_le _ _).trans (add_le_add hleft hright)
  have hn0 : 0 < n := zero_lt_one.trans hn
  have hid : (Real.log n/n)*((m/a)*buchstab (Real.log (m/a)/Real.log z)/Real.log z)-
      beta*((Real.log n/n)*((n/a)*buchstab (Real.log (n/a)/Real.log z)/Real.log z)) =
      (1/a)*((rho-beta)*(L*Wn)+rho*(L*(Wm-Wn))) := by
    dsimp only [rho,L,Wm,Wn]
    field_simp [hn0.ne',ha.ne',hlz.ne']
    <;> ring
  rw [hid,abs_mul,abs_of_nonneg (one_div_nonneg.mpr ha.le)]
  exact mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr ha.le)
end
end ImbalancedChen
