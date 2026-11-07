import ImbalancedChen.Part3ComplexOrderKEntire

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Explicit exponential bounds uniform in the full closed order strip
|Re nu|<=R and q>=q0>0. Constants are selected before nu and q.
The proof splits the actual Laplace factor at q/2 and uses cosh u>=1.
The actual order derivative is bounded through its proved integral formula;
no fixed-order asymptotic or normal-convergence assumption is used.
-/

namespace ImbalancedChen.Part3.ComplexOrderKUniformStripDecay20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKHolomorphicSourceOnly
open ComplexOrderKEntire20261025a

def stripDecayConstant (k : ℕ) (q0 R : ℝ) : ℝ :=
  2 * (k.factorial : ℝ) * 2 ^ k * Real.exp (4 * (R + 1) ^ 2 / q0)

theorem stripDecayConstant_pos (k : ℕ) (q0 R : ℝ) : 0 < stripDecayConstant k q0 R := by
  unfold stripDecayConstant
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  positivity

private theorem exp_half_split (q u : ℝ) :
    Real.exp (-q * Real.cosh u) =
      Real.exp (-(q / 2) * Real.cosh u) * Real.exp (-(q / 2) * Real.cosh u) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem exp_half_le {q : ℝ} (hq : 0 ≤ q) (u : ℝ) :
    Real.exp (-(q / 2) * Real.cosh u) ≤ Real.exp (-(q / 2)) := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Real.one_le_cosh u) (show 0 ≤ q / 2 by positivity)
  nlinarith only [hh]

theorem complexOrderMoment_uniform_integrand_bound (k : ℕ)
    {q0 q R u : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q)
    (hν : |ν.re| ≤ R) (hu : 0 ≤ u) :
    ‖(u : ℂ) ^ k * complexOrderIntegrand ν q u‖ ≤
      Real.exp (-(q / 2)) * orderMomentEnvelope k (q0 / 2) R u := by
  have hqpos : 0 < q := hq0.trans_le hq
  have hhalf : q0 / 2 ≤ q / 2 := by linarith only [hq]
  have hsplit : (u : ℂ) ^ k * complexOrderIntegrand ν q u =
      (Real.exp (-(q / 2) * Real.cosh u) : ℂ) *
        ((u : ℂ) ^ k * complexOrderIntegrand ν (q / 2) u) := by
    unfold complexOrderIntegrand
    rw [exp_half_split, Complex.ofReal_mul]
    ring
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (exp_half_le hqpos.le u)
    (complexOrderMoment_norm_le k (half_pos hq0) hhalf hν hu)
    (norm_nonneg _) (Real.exp_pos _).le

theorem complexOrderDeriv_uniform_integrand_bound
    {q0 q R u : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q)
    (hν : |ν.re| ≤ R) (hu : 0 ≤ u) :
    ‖complexOrderDerivIntegrand ν q u‖ ≤
      Real.exp (-(q / 2)) * orderMomentEnvelope 1 (q0 / 2) R u := by
  have hqpos : 0 < q := hq0.trans_le hq
  have hhalf : q0 / 2 ≤ q / 2 := by linarith only [hq]
  have hsplit : complexOrderDerivIntegrand ν q u =
      (Real.exp (-(q / 2) * Real.cosh u) : ℂ) * complexOrderDerivIntegrand ν (q / 2) u := by
    unfold complexOrderDerivIntegrand
    rw [exp_half_split, Complex.ofReal_mul]
    ring
  rw [hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (exp_half_le hqpos.le u)
    (complexOrderDeriv_norm_le (half_pos hq0) hhalf hν hu)
    (norm_nonneg _) (Real.exp_pos _).le

theorem orderMomentEnvelope_half_integral (k : ℕ) {q0 : ℝ} (hq0 : 0 < q0) (R : ℝ) :
    (∫ u in Ioi (0 : ℝ), orderMomentEnvelope k (q0 / 2) R u) = stripDecayConstant k q0 R := by
  have hexp : (∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2))) = 2 := by
    have he : (fun u : ℝ => Real.exp (-(u / 2))) =
        (fun u : ℝ => Real.exp ((-(1 / 2) : ℝ) * u)) := by
      funext u
      congr 1
      ring
    rw [he, integral_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0]
    norm_num
  have harg : 2 * (R + 1) ^ 2 / (q0 / 2) = 4 * (R + 1) ^ 2 / q0 := by
    field_simp [hq0.ne'] <;> ring
  unfold orderMomentEnvelope stripDecayConstant
  rw [integral_const_mul, hexp, harg]
  ring

/-- All literal cosh order moments have one explicit uniform exponential bound. -/
theorem complexOrderMoment_uniform_exp_bound (k : ℕ)
    {q0 q R : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q) (hν : |ν.re| ≤ R) :
    ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ k * complexOrderIntegrand ν q u‖ ≤
      stripDecayConstant k q0 R * Real.exp (-(q / 2)) := by
  have hb : IntegrableOn (fun u : ℝ => Real.exp (-(q / 2)) *
      orderMomentEnvelope k (q0 / 2) R u) (Ioi 0) :=
    (orderMomentEnvelope_integrable k (q0 / 2) R).const_mul _
  have hle : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖(u : ℂ) ^ k * complexOrderIntegrand ν q u‖ ≤
        Real.exp (-(q / 2)) * orderMomentEnvelope k (q0 / 2) R u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact complexOrderMoment_uniform_integrand_bound k hq0 hq hν hu.le
  have hh := norm_integral_le_of_norm_le hb hle
  rw [integral_const_mul, orderMomentEnvelope_half_integral k hq0 R] at hh
  simpa only [mul_comm] using hh

theorem complexOrderK_uniform_exp_bound
    {q0 q R : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q) (hν : |ν.re| ≤ R) :
    ‖complexOrderK ν q‖ ≤ stripDecayConstant 0 q0 R * Real.exp (-(q / 2)) := by
  simpa only [pow_zero, one_mul, complexOrderK] using
    complexOrderMoment_uniform_exp_bound 0 hq0 hq hν

theorem complexOrderDerivIntegral_uniform_exp_bound
    {q0 q R : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q) (hν : |ν.re| ≤ R) :
    ‖∫ u in Ioi (0 : ℝ), complexOrderDerivIntegrand ν q u‖ ≤
      stripDecayConstant 1 q0 R * Real.exp (-(q / 2)) := by
  have hb : IntegrableOn (fun u : ℝ => Real.exp (-(q / 2)) *
      orderMomentEnvelope 1 (q0 / 2) R u) (Ioi 0) :=
    (orderMomentEnvelope_integrable 1 (q0 / 2) R).const_mul _
  have hle : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖complexOrderDerivIntegrand ν q u‖ ≤
        Real.exp (-(q / 2)) * orderMomentEnvelope 1 (q0 / 2) R u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact complexOrderDeriv_uniform_integrand_bound hq0 hq hν hu.le
  have hh := norm_integral_le_of_norm_le hb hle
  rw [integral_const_mul, orderMomentEnvelope_half_integral 1 hq0 R] at hh
  simpa only [mul_comm] using hh

/-- Bound for the actual complex derivative, not just a candidate integrand. -/
theorem complexOrderK_orderDeriv_uniform_exp_bound
    {q0 q R : ℝ} {ν : ℂ} (hq0 : 0 < q0) (hq : q0 ≤ q) (hν : |ν.re| ≤ R) :
    ‖deriv (fun z : ℂ => complexOrderK z q) ν‖ ≤
      stripDecayConstant 1 q0 R * Real.exp (-(q / 2)) := by
  rw [(complexOrderK_hasDerivAt_all ν (hq0.trans_le hq)).deriv]
  exact complexOrderDerivIntegral_uniform_exp_bound hq0 hq hν

end
end ImbalancedChen.Part3.ComplexOrderKUniformStripDecay20261025a
