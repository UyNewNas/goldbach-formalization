import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterInduction
import ImbalancedChen.Part3RoughThinEulerFactors
import Mathlib.Data.Nat.Factorization.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Quantitative complex-strip bounds for the ACTUAL induction Euler product
over primes dividing the original modulus. The existing primary induction
definition is reused. For Re(s)>=3/4 the original modulus Q pays at most
Q in norm, Q^2 in reciprocal norm, and 3 log Q in logarithmic derivative.
No primitive L-function estimate or desired left-strip norm is assumed.
-/

namespace ImbalancedChen.Part3.PrimitiveInductionEulerThin20261026b
noncomputable section
open Classical Finset Complex DirichletCharacter
open scoped BigOperators
open RoughThinEulerFactors20261026b RoughFiniteEulerLogDerivative20261026b

theorem primeRadius_le_three_quarters : primeRadius ≤ 3/4 := by
  have hsqrt : (4/3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4/3) hsqrt
  norm_num at hinv
  calc
    primeRadius ≤ (2 : ℝ)^(-(1/2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = (Real.sqrt 2)⁻¹ := by
      rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    _ ≤ 3/4 := by simpa only [one_div] using hinv

theorem primeFactor_thin_bounds {m p : ℕ} (χ : DirichletCharacter ℂ m)
    (hp : p.Prime) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    (1-χ p*(p : ℂ)^(-s)) ≠ 0 ∧
      ‖1-χ p*(p : ℂ)^(-s)‖ ≤ (p : ℝ) ∧
      ‖(1-χ p*(p : ℂ)^(-s))⁻¹‖ ≤ 4 ∧
      ‖(1-χ p*(p : ℂ)^(-s))⁻¹‖ ≤ (p : ℝ)^2 := by
  have hf := thin_prime_factor χ hp (δ := 1/4) (by norm_num) (by linarith)
  have ht := prime_twist_norm_le_radius χ hp (δ := 1/4) (by norm_num) (by linarith)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hmargin : (1/4 : ℝ) ≤ 1-primeRadius := by
    linarith [primeRadius_le_three_quarters]
  have hinv : ‖(1-χ p*(p : ℂ)^(-s))⁻¹‖ ≤ 4 := by
    refine hf.2.2.2.trans ?_
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/4) hmargin
    norm_num at h
    simpa only [one_div] using h
  refine ⟨hf.2.1, ?_, hinv, hinv.trans ?_⟩
  · have h := norm_sub_le (1 : ℂ) (χ p*(p : ℂ)^(-s))
    rw [norm_one] at h
    linarith [primeRadius_le_three_quarters]
  · nlinarith

theorem primeFactors_product_le (Q : ℕ) [NeZero Q] :
    (∏ p ∈ Q.primeFactors, (p : ℝ)) ≤ (Q : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (NeZero.pos Q) (Nat.prod_primeFactors_dvd Q)

theorem primeFactors_log_sum_le (Q : ℕ) [NeZero Q] :
    (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (Q : ℝ) := by
  rw [← Real.log_prod (fun p hp =>
    (show (0 : ℝ) < p from by exact_mod_cast Nat.pos_of_mem_primeFactors hp).ne')]
  apply Real.log_le_log
  · exact Finset.prod_pos (fun p hp => by exact_mod_cast Nat.pos_of_mem_primeFactors hp)
  · exact primeFactors_product_le Q

/-- Literal complex finite Euler product over p|Q. The estimate is valid
also when χ(p)=0; all such factors stay equal to one. -/
theorem inductionEulerProduct_bounds {m : ℕ} (χ : DirichletCharacter ℂ m)
    (Q : ℕ) [NeZero Q] {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    inductionEulerProduct χ Q s ≠ 0 ∧
      ‖inductionEulerProduct χ Q s‖ ≤ (Q : ℝ) ∧
      ‖(inductionEulerProduct χ Q s)⁻¹‖ ≤ (Q : ℝ)^2 := by
  have hfactor := fun p hp => primeFactor_thin_bounds χ
    (Nat.prime_of_mem_primeFactors (n := Q) hp) hs
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hfactor p hp).1)
  · calc
      _ = ∏ p ∈ Q.primeFactors, ‖1-χ p*(p : ℂ)^(-s)‖ := by
        rw [inductionEulerProduct,norm_prod]
      _ ≤ ∏ p ∈ Q.primeFactors, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => (hfactor p hp).2.1)
      _ ≤ (Q : ℝ) := primeFactors_product_le Q
  · calc
      _ = ∏ p ∈ Q.primeFactors, ‖(1-χ p*(p : ℂ)^(-s))⁻¹‖ := by
        rw [inductionEulerProduct,← Finset.prod_inv_distrib,norm_prod]
      _ ≤ ∏ p ∈ Q.primeFactors, (p : ℝ)^2 :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => (hfactor p hp).2.2.2)
      _ = (∏ p ∈ Q.primeFactors, (p : ℝ))^2 := by rw [Finset.prod_pow]
      _ ≤ (Q : ℝ)^2 := pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (primeFactors_product_le Q) 2

theorem inductionEulerProduct_differentiable {m : ℕ}
    (χ : DirichletCharacter ℂ m) (Q : ℕ) :
    Differentiable ℂ (inductionEulerProduct χ Q) := by
  intro s
  exact DifferentiableAt.fun_finsetProd (fun p hp =>
    (factor_hasDerivAt χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt)

theorem induction_primeFactor_eq_one_of_dvd_level {m p : ℕ}
    (χ : DirichletCharacter ℂ m) (hp : p.Prime) (hpm : p ∣ m) (s : ℂ) :
    1-χ p*(p : ℂ)^(-s) = 1 := by
  have hu : ¬ IsUnit (p : ZMod m) := by
    rw [ZMod.isUnit_iff_coprime,hp.coprime_iff_not_dvd]
    exact fun h => h hpm
  simp only [χ.map_nonunit hu,zero_mul,sub_zero]

theorem inductionEulerProduct_logDeriv {m : ℕ} (χ : DirichletCharacter ℂ m)
    (Q : ℕ) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    logDeriv (inductionEulerProduct χ Q) s =
      ∑ p ∈ Q.primeFactors,
        (χ p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-χ p*(p : ℂ)^(-s)) := by
  have hfun : inductionEulerProduct χ Q =
      ∏ p ∈ Q.primeFactors, (fun w : ℂ => 1-χ p*(p : ℂ)^(-w)) := by
    funext w
    simp only [inductionEulerProduct,Finset.prod_apply]
  rw [hfun,logDeriv_prod
    (fun p hp => (primeFactor_thin_bounds χ (Nat.prime_of_mem_primeFactors hp) hs).1)
    (fun p hp => (factor_hasDerivAt χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logDeriv_apply,(factor_hasDerivAt χ (Nat.prime_of_mem_primeFactors hp) s).deriv]

/-- No prime-counting or Mertens estimate is needed: the squarefree
prime product divides Q, so the actual sum of its logarithms is <=log Q. -/
theorem inductionEulerProduct_logDeriv_norm_le {m : ℕ} (χ : DirichletCharacter ℂ m)
    (Q : ℕ) [NeZero Q] {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    ‖logDeriv (inductionEulerProduct χ Q) s‖ ≤ 3*Real.log (Q : ℝ) := by
  rw [inductionEulerProduct_logDeriv χ Q hs]
  calc
    _ ≤ ∑ p ∈ Q.primeFactors,
        ‖(χ p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-χ p*(p : ℂ)^(-s))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Q.primeFactors, 3*Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      have hnormlog : ‖Complex.log (p : ℂ)‖ = Real.log (p : ℝ) := by
        rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg p),
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
      have ht : ‖χ p*(p : ℂ)^(-s)‖ ≤ (3/4 : ℝ) :=
        (prime_twist_norm_le_radius χ hprime (δ := 1/4) (by norm_num) (by linarith)).trans
          primeRadius_le_three_quarters
      have hi := (primeFactor_thin_bounds χ hprime hs).2.2.1
      rw [div_eq_mul_inv,norm_mul,norm_mul,hnormlog]
      calc
        _ ≤ ((3/4 : ℝ)*Real.log (p : ℝ))*4 :=
          mul_le_mul (mul_le_mul_of_nonneg_right ht hlog) hi (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = 3*∑ p ∈ Q.primeFactors, Real.log (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 3*Real.log (Q : ℝ) := mul_le_mul_of_nonneg_left (primeFactors_log_sum_le Q) (by norm_num)

end
end ImbalancedChen.Part3.PrimitiveInductionEulerThin20261026b
