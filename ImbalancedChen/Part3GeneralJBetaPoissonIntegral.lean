import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Actual compact Beta-coordinate Poisson integral for general complex J.
The variable x is the square of the usual symmetric Poisson variable t.
The weight is x^(-1/2) (1-x)^(nu-1/2), with principal powers of nonnegative
real bases. Endpoint integrability requires and uses Re nu > -1/2.
The integral is evaluated by actual dominated termwise cosine integration.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory intervalIntegral

namespace ImbalancedChen.Part3.GeneralJBetaPoissonIntegralSourceOnly

open GeneralComplexISeriesSourceOnly ActualGeneralJBesselSourceOnly

def jPoissonWeight (nu : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - (x : ℂ)) ^ ((nu + 1 / 2) - 1)

def jPoissonCosCoeff (q : ℝ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * (q : ℂ) ^ (2 * n) / ((2 * n).factorial : ℂ)

def jBetaPoissonIntegral (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    Complex.cos ((q : ℂ) * (Real.sqrt x : ℂ)) * jPoissonWeight nu x

theorem jPoissonWeight_intervalIntegrable {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) :
    IntervalIntegrable (jPoissonWeight nu) volume 0 1 := by
  apply Complex.betaIntegral_convergent
  · norm_num
  · simp only [Complex.add_re, Complex.div_re, Complex.one_re,
      Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith

theorem jBetaPoisson_integrable {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) (q : ℝ) :
    IntervalIntegrable (fun x => Complex.cos ((q : ℂ) * (Real.sqrt x : ℂ)) *
      jPoissonWeight nu x) volume 0 1 :=
  (jPoissonWeight_intervalIntegrable hnu).continuousOn_mul (by fun_prop)

theorem jPoisson_moment (nu : ℂ) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, (x : ℂ) ^ n * jPoissonWeight nu x) =
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (nu + 1 / 2) := by
  unfold Complex.betaIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have he : ((n : ℂ) + 1 / 2) - 1 = (n : ℂ) + ((1 / 2 : ℂ) - 1) := by ring
  rw [he, Complex.cpow_add _ _ hxC, Complex.cpow_natCast]
  dsimp [jPoissonWeight]
  ring

/-- The even-factorial/Gamma-half identity needed for the exact normalizing
constant, derived from the genuine Gamma duplication formula. -/
theorem gamma_half_factorial_identity (n : ℕ) :
    Complex.Gamma ((n : ℂ) + 1 / 2) * ((4 : ℂ) ^ n * (n.factorial : ℂ)) =
      ((2 * n).factorial : ℂ) * (Real.sqrt Real.pi : ℂ) := by
  have hd := Complex.Gamma_mul_Gamma_add_half ((n : ℂ) + 1 / 2)
  have h1 : ((n : ℂ) + 1 / 2) + 1 / 2 = (n : ℂ) + 1 := by ring
  have h2 : 2 * ((n : ℂ) + 1 / 2) = ((2 * n : ℕ) : ℂ) + 1 := by push_cast; ring
  have h3 : 1 - 2 * ((n : ℂ) + 1 / 2) = -((2 * n : ℕ) : ℂ) := by push_cast; ring
  rw [h1, h2, h3, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, Complex.cpow_natCast] at hd
  have hp : (2 : ℂ) ^ (2 * n) = (4 : ℂ) ^ n := by rw [pow_mul]; norm_num
  rw [hp] at hd
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = (Complex.Gamma ((n : ℂ) + 1 / 2) * (n.factorial : ℂ)) * (4 : ℂ) ^ n := by ring
    _ = (((2 * n).factorial : ℂ) * ((4 : ℂ) ^ n)⁻¹ *
        (Real.sqrt Real.pi : ℂ)) * (4 : ℂ) ^ n := by rw [hd]
    _ = _ := by field_simp [h4] <;> ring

theorem jPoisson_moment_coefficient {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    (q : ℝ) (n : ℕ) :
    jPoissonCosCoeff q n * Complex.betaIntegral ((n : ℂ) + 1 / 2) (nu + 1 / 2) =
      ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) *
        (generalICoeff nu n * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n) := by
  have hs : 0 < (((n : ℂ) + 1 / 2).re) := by
    simp only [Complex.add_re, Complex.natCast_re]
    norm_num
    positivity
  have ht : 0 < (nu + 1 / 2).re := by
    simp only [Complex.add_re]
    norm_num
    linarith
  have harg : ((n : ℂ) + 1 / 2) + (nu + 1 / 2) = (n : ℂ) + nu + 1 := by ring
  have hg : Complex.Gamma ((n : ℂ) + nu + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf2 : ((2 * n).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hh := gamma_half_factorial_identity n
  have hhalf : Complex.Gamma ((n : ℂ) + 1 / 2) =
      (((2 * n).factorial : ℂ) * (Real.sqrt Real.pi : ℂ)) /
        ((4 : ℂ) ^ n * (n.factorial : ℂ)) :=
    (eq_div_iff (mul_ne_zero h4 hf)).mpr hh
  have hz : (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n =
      (-1 : ℂ) ^ n * (q : ℂ) ^ (2 * n) / (4 : ℂ) ^ n := by
    have hbase : (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) = (q : ℂ) ^ (2 : ℕ) / 4 := by
      push_cast
      ring
    rw [neg_pow, hbase, div_pow, ← pow_mul]
    ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hs ht, harg, hhalf]
  dsimp [jPoissonCosCoeff, generalICoeff]
  rw [hz]
  field_simp [hg, hf, hf2, h4]
  <;> ring

theorem jPoisson_cosine_series_integral {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    {q : ℝ} (hq : 0 < q) :
    HasSum (fun n => jPoissonCosCoeff q n *
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (nu + 1 / 2)) (jBetaPoissonIntegral nu q) := by
  let a : ℕ → ℝ := fun n => q ^ (2 * n) / ((2 * n).factorial : ℝ)
  let F : ℕ → ℝ → ℂ := fun n x => jPoissonCosCoeff q n * (x : ℂ) ^ n * jPoissonWeight nu x
  have ha : Summable a := (Real.hasSum_cosh q).summable
  have hw := jPoissonWeight_intervalIntegrable hnu
  have hcoeff (n : ℕ) : ‖jPoissonCosCoeff q n‖ = a n := by
    simp [jPoissonCosCoeff, a, norm_div, norm_mul, norm_pow,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hFint (n : ℕ) : IntervalIntegrable (F n) volume 0 1 :=
    hw.continuousOn_mul (by fun_prop)
  have hbound (n : ℕ) (x : ℝ) (hx : x ∈ Set.uIoc (0 : ℝ) 1) :
      ‖F n x‖ ≤ a n * ‖jPoissonWeight nu x‖ := by
    rw [uIoc_of_le (by norm_num)] at hx
    have hp : ‖(x : ℂ) ^ n‖ ≤ 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1.le]
      exact pow_le_one₀ hx.1.le hx.2
    have hn : 0 ≤ a n := by dsimp [a]; positivity
    dsimp [F]
    rw [norm_mul, norm_mul, hcoeff]
    calc
      _ ≤ (a n * 1) * ‖jPoissonWeight nu x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hn) (norm_nonneg _)
      _ = _ := by ring
  have hbi : IntervalIntegrable
      (fun x => ∑' n, a n * ‖jPoissonWeight nu x‖) volume 0 1 := by
    have heq : (fun x => ∑' n, a n * ‖jPoissonWeight nu x‖) =
        (fun x => (∑' n, a n) * ‖jPoissonWeight nu x‖) :=
      funext fun x => ha.tsum_mul_right _
    rw [heq]
    exact hw.norm.const_mul _
  have hlim (x : ℝ) (hx : x ∈ Set.uIoc (0 : ℝ) 1) :
      HasSum (fun n => F n x)
        (Complex.cos ((q : ℂ) * (Real.sqrt x : ℂ)) * jPoissonWeight nu x) := by
    rw [uIoc_of_le (by norm_num)] at hx
    have hpow (n : ℕ) : ((q : ℂ) * (Real.sqrt x : ℂ)) ^ (2 * n) =
        (q : ℂ) ^ (2 * n) * (x : ℂ) ^ n := by
      rw [mul_pow, pow_mul, pow_mul]
      congr 1
      rw [← Complex.ofReal_pow, Real.sq_sqrt hx.1.le]
    have h := (Complex.hasSum_cos ((q : ℂ) * (Real.sqrt x : ℂ))).mul_right
      (jPoissonWeight nu x)
    convert h using 1
    funext n
    rw [hpow]
    dsimp [F, jPoissonCosCoeff]
    ring
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n x => a n * ‖jPoissonWeight nu x‖)
    (fun n => (hFint n).aestronglyMeasurable_restrict_uIoc)
    (fun n => Filter.Eventually.of_forall (fun x hx => hbound n x hx))
    (Filter.Eventually.of_forall (fun x _ => ha.mul_right ‖jPoissonWeight nu x‖))
    hbi (Filter.Eventually.of_forall hlim)
  have heq (n : ℕ) : (∫ x in (0 : ℝ)..1, F n x) =
      jPoissonCosCoeff q n * Complex.betaIntegral ((n : ℂ) + 1 / 2) (nu + 1 / 2) := by
    dsimp [F]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, jPoisson_moment]
  simpa only [heq, jBetaPoissonIntegral] using h

/-- Exact evaluation of the compact Beta-coordinate cosine integral. -/
theorem jBetaPoissonIntegral_eq_core {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    {q : ℝ} (hq : 0 < q) :
    jBetaPoissonIntegral nu q =
      ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) *
        generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hs := jPoisson_cosine_series_integral hnu hq
  have hc := (generalICore_hasSum (by linarith : -1 < nu.re)
    (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))).mul_left
      ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2))
  have heq : (fun n => jPoissonCosCoeff q n *
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (nu + 1 / 2)) =
      (fun n => ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) *
        (generalICoeff nu n * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) ^ n)) :=
    funext (jPoisson_moment_coefficient hnu q)
  rw [heq] at hs
  exact hs.unique hc

/-- The genuine normalized compact Poisson integral for general complex J,
in the Beta coordinate x=t². No integral representation is an assumption. -/
theorem generalJ_eq_betaPoissonIntegral {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJ nu q = (((q / 2 : ℝ) : ℂ) ^ nu) /
      ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) *
        jBetaPoissonIntegral nu q := by
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hg : Complex.Gamma (nu + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.add_re]
      norm_num
      linarith)
  rw [jBetaPoissonIntegral_eq_core hnu hq]
  dsimp [generalJ]
  field_simp [hp, hg]

end ImbalancedChen.Part3.GeneralJBetaPoissonIntegralSourceOnly
