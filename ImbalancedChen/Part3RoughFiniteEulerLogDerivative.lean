import ImbalancedChen.Part3RoughFiniteEulerBounds
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite Euler correction: exact logarithmic derivative and explicit
height-uniform magnitude/derivative bounds in Re(s)>=1. The principal
character and p|q branches are not excluded. No bound for L'/L or 1/L at
or left of the line one is inferred from these finite-factor estimates.
-/

namespace ImbalancedChen.Part3.RoughFiniteEulerLogDerivative20261026b
noncomputable section
open Classical Finset Complex
open scoped BigOperators
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughFiniteEulerBounds20261026b

def logDerivativeCost (z : ℝ) : ℝ :=
  ∑ p ∈ smallPrimes z, Real.log (p : ℝ)/((p : ℝ)-1)

theorem factor_hasDerivAt {q p : ℕ} (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun w : ℂ => 1-chi p*(p : ℂ)^(-w))
      (chi p*(p : ℂ)^(-s)*Complex.log (p : ℂ)) s := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hd : HasDerivAt (fun w : ℂ => (p : ℂ)^(-w))
      ((p : ℂ)^(-s)*Complex.log (p : ℂ)*(-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl hpC)
  convert (hd.const_mul (chi p)).const_sub 1 using 1 <;> ring

/-- Finite product differentiation is applied to the original correction,
not to an assumed infinite Euler product derivative. -/
theorem finiteCorrection_logDeriv {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    logDeriv (finiteCorrection chi z) s =
      ∑ p ∈ smallPrimes z,
        (chi p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-chi p*(p : ℂ)^(-s)) := by
  have hfun : finiteCorrection chi z =
      ∏ p ∈ smallPrimes z, (fun w : ℂ => 1-chi p*(p : ℂ)^(-w)) := by
    funext w
    simp only [finiteCorrection,Finset.prod_apply]
  rw [hfun,logDeriv_prod
    (fun p hp => (prime_factor_bounds chi (smallPrimes_prime hp) hs).1)
    (fun p hp => (factor_hasDerivAt chi (smallPrimes_prime hp) s).differentiableAt)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logDeriv_apply,(factor_hasDerivAt chi (smallPrimes_prime hp) s).deriv]

private theorem factor_logDeriv_norm_le {q p : ℕ} (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(chi p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-chi p*(p : ℂ)^(-s))‖ ≤
      Real.log (p : ℝ)/((p : ℝ)-1) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpR1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpR1.le
  have hnormlog : ‖Complex.log (p : ℂ)‖ = Real.log (p : ℝ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  have hrec : 1/(p : ℝ) < 1 := (div_lt_one hpR).mpr hpR1
  have hdelta : 0 < 1-1/(p : ℝ) := by linarith
  rw [div_eq_mul_inv,norm_mul,norm_mul,hnormlog]
  calc
    _ ≤ (1/(p : ℝ)*Real.log (p : ℝ))*(1-1/(p : ℝ))⁻¹ := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (prime_twist_norm_le_inv chi hp hs) hlog)
        (prime_factor_bounds chi hp hs).2.2.2 (norm_nonneg _)
        (mul_nonneg (one_div_pos.mpr hpR).le hlog)
    _ = _ := by field_simp [hpR.ne',hdelta.ne',(sub_pos.mpr hpR1).ne'] <;> ring

theorem finiteCorrection_logDeriv_norm_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (finiteCorrection chi z) s‖ ≤ logDerivativeCost z := by
  rw [finiteCorrection_logDeriv chi z hs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  exact factor_logDeriv_norm_le chi (smallPrimes_prime hp) hs

theorem finiteCorrection_deriv_norm_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖deriv (finiteCorrection chi z) s‖ ≤ logDerivativeCost z*plusEnvelope z := by
  have hcost : 0 ≤ logDerivativeCost z := by
    apply Finset.sum_nonneg
    intro p hp
    have hprime := smallPrimes_prime hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le))
      (sub_pos.mpr hp1).le
  have hC := finiteCorrection_bounds chi z hs
  have he : deriv (finiteCorrection chi z) s =
      logDeriv (finiteCorrection chi z) s*finiteCorrection chi z s := by
    rw [logDeriv_apply,div_mul_cancel₀ _ hC.1]
  rw [he,norm_mul]
  exact mul_le_mul (finiteCorrection_logDeriv_norm_le chi z hs) hC.2.1
    (norm_nonneg _) hcost

end
end ImbalancedChen.Part3.RoughFiniteEulerLogDerivative20261026b
