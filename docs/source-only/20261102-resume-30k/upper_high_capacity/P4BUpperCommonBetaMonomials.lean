import ImbalancedChen.P4BOriginalFifthUpperMonomials
import ImbalancedChen.ActualSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the common small beta in group3, and replace the allocation capacity
A by the Medium length U=A*x^(d/4). All three positive-power monomials
receive their actual beta cost. The numerical input is supplied by the
companion original-upper fifth theorem; it is not an assumed PP bound.
This is at the source scale x. Complete-product local-scale conversion,
the full W branches, and the uniform smooth family remain separate.
-/
namespace ImbalancedChen.P4BUpperCommonBetaMonomials
noncomputable section

/-- The original sign selects beta-plus or beta-minus. Either nonzero
choice has the same strict physical small-factor level. -/
theorem actual_signed_beta_level (c : ℕ → ℝ) (N cap a b : ℕ) (w L : ℝ)
    (ha : smallRoughPairCoefficient c (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) (a,b) ≠ 0) :
    (a : ℝ) < L := by
  unfold smallRoughPairCoefficient signAttachedCoefficient at ha
  have hb := (mul_ne_zero_iff.mp ha).2
  by_cases hs : 0 ≤ c b
  · rw [if_pos hs] at hb
    exact (actualSmallRosserPlus_active hb).2.1
  · rw [if_neg hs] at hb
    exact (actualSmallRosserMinus_active hb).2.1

/-- Exact endpoint costs: 2*ell in the first two monomials and
39*ell/16 in the third. The third expression is written in the original
positive-power Medium form, with spectral exponent theta=7/32.
sigma=d/100 is fixed before the arithmetic input. -/
theorem pay_common_beta_and_length
    {x d ell alpha A a b c : ℝ} (hx : 1 < x) (hd : 0 < d)
    (hell : ell ≤ d/16) (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haa : a ≤ A)
    (h1 : A^2*b*c^2 ≤ x^(1-3*d))
    (h2 : x^(7*alpha/32)*A*a*b^5*c^2 ≤ x^(2-4*d))
    (h3 : (A*c/b)^(7/16 : ℝ)*A*a*b^5*c^2 ≤ x^(2-39*d/8)) :
    let U := A*x^(d/4)
    let Q3 := c*x^ell
    a < U*x^(-d/100) ∧
      U^2*b*Q3^2 < x^(1-8*(d/100)) ∧
      x^(7*alpha/32)*U*a*b^5*Q3^2 < x^(2-15*(d/100)) ∧
      U^(23/16 : ℝ)*a*b^(73/16 : ℝ)*Q3^(39/16 : ℝ) < x^(2-15*(d/100)) := by
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hdl : 0 < d*Real.log x := mul_pos hd hlog
  have hellL := mul_le_mul_of_nonneg_right hell hlog.le
  have hlog1 := (Real.le_rpow_iff_log_le (by positivity : 0<A^2*b*c^2) hx0).mp h1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hb.ne',Real.log_pow,Real.log_pow] at hlog1
  have hlog2 := (Real.le_rpow_iff_log_le
    (by positivity : 0<x^(7*alpha/32)*A*a*b^5*c^2) hx0).mp h2
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hA.ne',
    Real.log_rpow hx0,Real.log_pow,Real.log_pow] at hlog2
  have hlog3 := (Real.le_rpow_iff_log_le
    (by positivity : 0<(A*c/b)^(7/16 : ℝ)*A*a*b^5*c^2) hx0).mp h3
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) hA.ne',
    Real.log_rpow (div_pos (mul_pos hA hc) hb),
    Real.log_div (mul_ne_zero hA.ne' hc.ne') hb.ne',
    Real.log_mul hA.ne' hc.ne',Real.log_pow,Real.log_pow] at hlog3
  refine ⟨?_,?_,?_,?_⟩
  · calc
      a ≤ A := haa
      _ < A*x^(d/4-d/100) := by
        have hh : 1 < x^(d/4-d/100) := Real.one_lt_rpow hx (by linarith)
        nlinarith
      _ = A*x^(d/4)*x^(-d/100) := by
        rw [sub_eq_add_neg,Real.rpow_add hx0]
        ring
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hb.ne',Real.log_pow,Real.log_pow,
      Real.log_mul hA.ne' (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0,Real.log_rpow hx0]
    nlinarith
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',Real.log_mul (by positivity) (by positivity),
      Real.log_mul hA.ne' (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_rpow hx0,Real.log_rpow hx0,Real.log_pow,Real.log_pow,
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0]
    nlinarith
  · apply (Real.lt_rpow_iff_log_lt (by positivity) hx0).mpr
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne',
      Real.log_rpow (mul_pos hA (Real.rpow_pos_of_pos hx0 _)),
      Real.log_rpow hb,Real.log_rpow (mul_pos hc (Real.rpow_pos_of_pos hx0 _)),
      Real.log_mul hA.ne' (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0,Real.log_rpow hx0]
    nlinarith

/-- An active actual sign-sensitive beta fits the group3 endpoint used
above. Its strict level is derived; beta-plus is not forced on negative
rough coefficients. This applies to the original fixedRoughCoefficient. -/
theorem actual_signed_beta_group_three
    (coeff : ℕ → ℝ) (N cap small rough : ℕ) (w ell C : ℝ) (hC : 0 ≤ C)
    (hactive : smallRoughPairCoefficient coeff
      (actualSmallRosserMinus N cap w ((N : ℝ)^ell))
      (actualSmallRosserPlus N cap w ((N : ℝ)^ell)) (small,rough) ≠ 0) :
    C*(small : ℝ) ≤ C*(N : ℝ)^ell :=
  mul_le_mul_of_nonneg_left
    (actual_signed_beta_level coeff N cap small rough w ((N : ℝ)^ell) hactive).le hC

end
end ImbalancedChen.P4BUpperCommonBetaMonomials
