import ImbalancedChen.Part3CuspCylinderMeasure
import ImbalancedChen.Part3PositiveMultiplicativeLog
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24. No acceptance credit.

The constant horizontal Fourier mode has radial operator `-y² ∂²_y`.
The exact unitary coordinate on the positive height axis is
`F(y) = sqrt y * g(log y)`, because hyperbolic area is `dy/y²`.
This computes the local differential expression and the scalar L² energy.
It asserts no domain, self-adjointness, boundary condition, automorphic
quotient eigenfunction, or quotient spectral gap.
-/

namespace ImbalancedChen.Part3.CuspConstantModeLogOperatorSourceOnly

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.CuspCylinderMeasure20261024z
open ImbalancedChen.Part3.PositiveMultiplicativeLogSourceOnly

/-- Conjugation from the additive logarithmic coordinate to a physical
constant cusp mode. -/
def constantMode (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.sqrt y * g (Real.log y)

def constantModeFirst (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ (-(1 / 2 : ℝ)) *
    (deriv g (Real.log y) + (1 / 2 : ℝ) * g (Real.log y))

def constantModeSecond (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ (-(3 / 2 : ℝ)) *
    (deriv (deriv g) (Real.log y) - (1 / 4 : ℝ) * g (Real.log y))

theorem constantMode_hasDerivAt (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (constantMode g) (constantModeFirst g y) y := by
  have hs : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) y := by
    convert Real.hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ))
      (Or.inl hy.ne') using 1 <;> norm_num
  have hl : HasDerivAt (fun x : ℝ => g (Real.log x))
      (deriv g (Real.log y) * y⁻¹) y := by
    simpa only [Function.comp_def] using
      (hg (Real.log y)).hasDerivAt.comp y (Real.hasDerivAt_log hy.ne')
  have h := hs.mul hl
  convert h using 1
  · funext x
    simp only [constantMode, Real.sqrt_eq_rpow]
  · simp only [constantModeFirst]
    have hp : y ^ (1 / 2 : ℝ) * y⁻¹ = y ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hy]
      norm_num
    nlinarith [congrArg (fun z : ℝ => z * deriv g (Real.log y)) hp]

private theorem constantModeFirst_hasDerivAt (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (constantModeFirst g) (constantModeSecond g y) y := by
  have hp : HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ))) y := by
    convert Real.hasDerivAt_rpow_const (x := y) (p := (-(1 / 2 : ℝ)))
      (Or.inl hy.ne') using 1 <;> norm_num
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy.ne'
  have h1 : HasDerivAt (fun x : ℝ => deriv g (Real.log x))
      (deriv (deriv g) (Real.log y) * y⁻¹) y := by
    simpa only [Function.comp_def] using
      (hg' (Real.log y)).hasDerivAt.comp y hlog
  have h2 : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * g (Real.log x))
      ((1 / 2 : ℝ) * (deriv g (Real.log y) * y⁻¹)) y := by
    simpa only [Function.comp_def] using
      ((hg (Real.log y)).hasDerivAt.comp y hlog).const_mul (1 / 2 : ℝ)
  have h := hp.mul (h1.add h2)
  convert h using 1
  · funext x
    rfl
  · simp only [constantModeSecond]
    have hpow : y ^ (-(1 / 2 : ℝ)) * y⁻¹ =
        y ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hy]
      norm_num
    nlinarith [congrArg (fun z : ℝ => z *
      (deriv (deriv g) (Real.log y) +
        (1 / 2 : ℝ) * deriv g (Real.log y))) hpow]

theorem constantMode_second_deriv (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    {y : ℝ} (hy : 0 < y) :
    deriv (deriv (constantMode g)) y = constantModeSecond g y := by
  have hevent : (fun x => deriv (constantMode g) x) =ᶠ[𝓝 y]
      constantModeFirst g := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact (constantMode_hasDerivAt g hg hx).deriv
  exact ((constantModeFirst_hasDerivAt g hg hg' hy).congr_of_eventuallyEq
    hevent.symm).deriv

/-- The literal constant-mode radial operator is conjugate to
`-∂²_r + 1/4` at `y = exp r`. The quarter is the exact cusp threshold
constant, with no claim that it is a quotient spectral lower bound. -/
theorem constantMode_radial_conjugation (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (constantMode g)) (Real.exp r) =
        Real.sqrt (Real.exp r) *
          (-deriv (deriv g) r + (1 / 4 : ℝ) * g r) := by
  have hy : 0 < Real.exp r := Real.exp_pos r
  rw [constantMode_second_deriv g hg hg' hy]
  simp only [constantModeSecond, Real.log_exp, Real.sqrt_eq_rpow]
  have hp : (Real.exp r) ^ 2 * (Real.exp r) ^ (-(3 / 2 : ℝ)) =
      (Real.exp r) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    norm_num
  rw [hp]
  ring

/-- The norm-square density in cusp height becomes `g(log y)^2/y`.
This is the pointwise Jacobian that permits use of the repository's
existing positive multiplicative measure. -/
theorem constantMode_energy_density (g : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    (1 / y) ^ 2 * (constantMode g y) ^ 2 =
      y⁻¹ * (g (Real.log y)) ^ 2 := by
  simp only [constantMode, mul_pow, Real.sq_sqrt hy.le]
  field_simp [hy.ne']
  ring

/-- Exact scalar L² isometry on the physical hyperbolic height measure.
The statement uses the same `heightMeasure` as the cusp cylinder and the
same logarithmic Jacobian as `Part3PositiveMultiplicativeLog`. -/
theorem constantMode_height_energy (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ y : PositiveHeight, (constantMode g (y : ℝ)) ^ 2 ∂heightMeasure) =
      ∫ r : ℝ, (g r) ^ 2 := by
  rw [height_integral_eq_weighted_volume]
  have hsub :
      (∫ y : PositiveHeight,
        (1 / (y : ℝ)) ^ 2 * (constantMode g (y : ℝ)) ^ 2) =
      ∫ y in Ioi (0 : ℝ), y⁻¹ * (g (Real.log y)) ^ 2 := by
    calc
      (∫ y : PositiveHeight,
          (1 / (y : ℝ)) ^ 2 * (constantMode g (y : ℝ)) ^ 2) =
          ∫ y in Ioi (0 : ℝ),
            (1 / y) ^ 2 * (constantMode g y) ^ 2 := by
        exact integral_subtype_comap measurableSet_Ioi _
      _ = ∫ y in Ioi (0 : ℝ), y⁻¹ * (g (Real.log y)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact constantMode_energy_density g hy
  rw [hsub]
  have hden :
      (∫ y in Ioi (0 : ℝ), y⁻¹ * (g (Real.log y)) ^ 2) =
      ∫ y : ℝ, (g (Real.log y)) ^ 2 ∂positiveMultiplicativeMeasure := by
    have hwd := integral_withDensity_eq_integral_toReal_smul
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (y⁻¹)))
      (Filter.Eventually.of_forall (fun y : ℝ => ENNReal.ofReal_lt_top))
      (fun y : ℝ => (g (Real.log y)) ^ 2)
    rw [positiveMultiplicativeMeasure, hwd]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hy.le)]
    simp only [smul_eq_mul]
  rw [hden, ← map_exp_volume]
  have hm : AEStronglyMeasurable
      (fun y : ℝ => (g (Real.log y)) ^ 2)
      positiveMultiplicativeMeasure := by
    exact ((hg.measurable.comp Real.measurable_log).pow_const 2).aestronglyMeasurable
  rw [integral_map (by fun_prop) hm]
  simp only [Real.log_exp]

/-- The inverse chart on real-valued height profiles. -/
def logarithmicInverse (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp (-r / 2) * F (Real.exp r)

private theorem sqrt_exp_half (r : ℝ) :
    Real.sqrt (Real.exp r) = Real.exp (r / 2) := by
  have he : Real.exp r = (Real.exp (r / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.sq_sqrt (Real.exp_pos r).le,
    Real.sqrt_nonneg (Real.exp r), Real.exp_pos (r / 2)]

theorem logarithmicInverse_constantMode (g : ℝ → ℝ) (r : ℝ) :
    logarithmicInverse (constantMode g) r = g r := by
  simp only [logarithmicInverse, constantMode, Real.log_exp,
    sqrt_exp_half]
  rw [← mul_assoc, ← Real.exp_add]
  have h : -r / 2 + r / 2 = 0 := by ring
  rw [h, Real.exp_zero, one_mul]

theorem constantMode_logarithmicInverse (F : ℝ → ℝ)
    {y : ℝ} (hy : 0 < y) :
    constantMode (logarithmicInverse F) y = F y := by
  have hs := sqrt_exp_half (Real.log y)
  rw [Real.exp_log hy] at hs
  simp only [constantMode, logarithmicInverse, Real.exp_log hy]
  rw [hs, ← mul_assoc, ← Real.exp_add]
  have h : Real.log y / 2 + -(Real.log y) / 2 = 0 := by ring
  rw [h, Real.exp_zero, one_mul]

/-- The inverse direction of the scalar L² identity; the physical profile
is sampled only at positive height. -/
theorem logarithmicInverse_height_energy (F : ℝ → ℝ)
    (hF : Continuous F) :
    (∫ r : ℝ, (logarithmicInverse F r) ^ 2) =
      ∫ y : PositiveHeight, (F (y : ℝ)) ^ 2 ∂heightMeasure := by
  have hg : Continuous (logarithmicInverse F) := by
    unfold logarithmicInverse
    fun_prop
  rw [← constantMode_height_energy (logarithmicInverse F) hg]
  apply integral_congr_ae
  filter_upwards with y
  rw [constantMode_logarithmicInverse F y.property]

/-- Cosine and sine are the real and imaginary logarithmic waves in the
Euler expression for the positive-real powers `y^(1/2 ± i t)`. -/
def cosineLogProfile (t r : ℝ) : ℝ := Real.cos (t * r)
def sineLogProfile (t r : ℝ) : ℝ := Real.sin (t * r)

private theorem cosineLogProfile_first (t r : ℝ) :
    deriv (cosineLogProfile t) r = -t * Real.sin (t * r) := by
  have h := (((hasDerivAt_id r).const_mul t).cos)
  convert h.deriv using 1 <;> simp [cosineLogProfile] <;> ring

private theorem sineLogProfile_first (t r : ℝ) :
    deriv (sineLogProfile t) r = t * Real.cos (t * r) := by
  have h := (((hasDerivAt_id r).const_mul t).sin)
  convert h.deriv using 1 <;> simp [sineLogProfile] <;> ring

theorem cosineLogProfile_second (t r : ℝ) :
    deriv (deriv (cosineLogProfile t)) r =
      -(t ^ 2) * cosineLogProfile t r := by
  have hfirst : deriv (cosineLogProfile t) =
      (fun x : ℝ => -t * Real.sin (t * x)) := by
    funext x
    exact cosineLogProfile_first t x
  rw [hfirst]
  have h := ((((hasDerivAt_id r).const_mul t).sin).const_mul (-t))
  convert h.deriv using 1 <;> simp [cosineLogProfile] <;> ring

theorem sineLogProfile_second (t r : ℝ) :
    deriv (deriv (sineLogProfile t)) r =
      -(t ^ 2) * sineLogProfile t r := by
  have hfirst : deriv (sineLogProfile t) =
      (fun x : ℝ => t * Real.cos (t * x)) := by
    funext x
    exact sineLogProfile_first t x
  rw [hfirst]
  have h := ((((hasDerivAt_id r).const_mul t).cos).const_mul t)
  convert h.deriv using 1 <;> simp [sineLogProfile] <;> ring

private theorem cosineLogProfile_differentiable (t : ℝ) :
    Differentiable ℝ (cosineLogProfile t) := by
  unfold cosineLogProfile
  fun_prop

private theorem cosineLogProfile_deriv_differentiable (t : ℝ) :
    Differentiable ℝ (deriv (cosineLogProfile t)) := by
  have hfirst : deriv (cosineLogProfile t) =
      (fun x : ℝ => -t * Real.sin (t * x)) := by
    funext x
    exact cosineLogProfile_first t x
  rw [hfirst]
  fun_prop

private theorem sineLogProfile_differentiable (t : ℝ) :
    Differentiable ℝ (sineLogProfile t) := by
  unfold sineLogProfile
  fun_prop

private theorem sineLogProfile_deriv_differentiable (t : ℝ) :
    Differentiable ℝ (deriv (sineLogProfile t)) := by
  have hfirst : deriv (sineLogProfile t) =
      (fun x : ℝ => t * Real.cos (t * x)) := by
    funext x
    exact sineLogProfile_first t x
  rw [hfirst]
  fun_prop

/-- Each real component of `y^(1/2 ± i t)` solves the genuine constant
Fourier-mode eigen-equation with spectral parameter `1/4+t²`. -/
theorem cosine_constant_mode_eigen (t r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (constantMode (cosineLogProfile t))) (Real.exp r) =
        ((1 / 4 : ℝ) + t ^ 2) *
          constantMode (cosineLogProfile t) (Real.exp r) := by
  rw [constantMode_radial_conjugation (cosineLogProfile t)
    (cosineLogProfile_differentiable t)
    (cosineLogProfile_deriv_differentiable t) r,
    cosineLogProfile_second]
  simp only [constantMode, Real.log_exp]
  ring

theorem sine_constant_mode_eigen (t r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (constantMode (sineLogProfile t))) (Real.exp r) =
        ((1 / 4 : ℝ) + t ^ 2) *
          constantMode (sineLogProfile t) (Real.exp r) := by
  rw [constantMode_radial_conjugation (sineLogProfile t)
    (sineLogProfile_differentiable t)
    (sineLogProfile_deriv_differentiable t) r,
    sineLogProfile_second]
  simp only [constantMode, Real.log_exp]
  ring

/-- Euler form of the positive-real complex power `y^(1/2 + i t)`.
The sign parameter `ε = -1` gives `y^(1/2 - i t)`. -/
def positiveComplexPower (ε t y : ℝ) : ℂ :=
  ((constantMode (cosineLogProfile t) y : ℝ) : ℂ) +
    (ε : ℂ) * Complex.I *
      ((constantMode (sineLogProfile t) y : ℝ) : ℂ)

/-- Identification with the literal complex exponential definition of
`y^(1/2+i t)` for positive real `y`. -/
theorem positiveComplexPower_plus_eq_exp (t : ℝ) {y : ℝ} (hy : 0 < y) :
    positiveComplexPower 1 t y =
      Complex.exp (((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
        (Real.log y : ℂ)) := by
  let r := Real.log y
  have hs : Real.sqrt y = Real.exp (r / 2) := by
    have h := sqrt_exp_half r
    simpa [r, Real.exp_log hy] using h
  have heuler := Complex.exp_ofReal_mul_I (t * r)
  calc
    positiveComplexPower 1 t y =
        (Real.exp (r / 2) : ℂ) *
          ((Real.cos (t * r) : ℂ) +
            (Real.sin (t * r) : ℂ) * Complex.I) := by
      simp only [positiveComplexPower, constantMode,
        cosineLogProfile, sineLogProfile, r, hs]
      push_cast
      ring
    _ = Complex.exp ((r / 2 : ℝ) : ℂ) *
          Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_exp, heuler]
    _ = Complex.exp (((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
          (Real.log y : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [r]
      push_cast
      ring

theorem positiveComplexPower_minus_eq_exp (t : ℝ) {y : ℝ} (hy : 0 < y) :
    positiveComplexPower (-1) t y =
      Complex.exp (((1 / 2 : ℂ) - Complex.I * (t : ℂ)) *
        (Real.log y : ℂ)) := by
  have hminus : positiveComplexPower (-1) t y =
      positiveComplexPower 1 (-t) y := by
    simp [positiveComplexPower, constantMode,
      cosineLogProfile, sineLogProfile, Real.cos_neg, Real.sin_neg]
    ring
  rw [hminus, positiveComplexPower_plus_eq_exp (-t) hy]
  congr 1
  ring

def positiveComplexPowerFirst (ε t y : ℝ) : ℂ :=
  ((constantModeFirst (cosineLogProfile t) y : ℝ) : ℂ) +
    (ε : ℂ) * Complex.I *
      ((constantModeFirst (sineLogProfile t) y : ℝ) : ℂ)

def positiveComplexPowerSecond (ε t y : ℝ) : ℂ :=
  ((constantModeSecond (cosineLogProfile t) y : ℝ) : ℂ) +
    (ε : ℂ) * Complex.I *
      ((constantModeSecond (sineLogProfile t) y : ℝ) : ℂ)

private theorem positiveComplexPower_hasDerivAt (ε t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (positiveComplexPower ε t)
      (positiveComplexPowerFirst ε t y) y := by
  have hc := (constantMode_hasDerivAt (cosineLogProfile t)
    (cosineLogProfile_differentiable t) hy).ofReal_comp
  have hs := (constantMode_hasDerivAt (sineLogProfile t)
    (sineLogProfile_differentiable t) hy).ofReal_comp
  convert hc.add (hs.const_mul ((ε : ℂ) * Complex.I)) using 1
    <;> simp [positiveComplexPower, positiveComplexPowerFirst, mul_assoc]

private theorem positiveComplexPowerFirst_hasDerivAt (ε t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (positiveComplexPowerFirst ε t)
      (positiveComplexPowerSecond ε t y) y := by
  have hc := (constantModeFirst_hasDerivAt (cosineLogProfile t)
    (cosineLogProfile_differentiable t)
    (cosineLogProfile_deriv_differentiable t) hy).ofReal_comp
  have hs := (constantModeFirst_hasDerivAt (sineLogProfile t)
    (sineLogProfile_differentiable t)
    (sineLogProfile_deriv_differentiable t) hy).ofReal_comp
  convert hc.add (hs.const_mul ((ε : ℂ) * Complex.I)) using 1
    <;> simp [positiveComplexPowerFirst, positiveComplexPowerSecond, mul_assoc]

theorem positiveComplexPower_second_deriv (ε t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    deriv (deriv (positiveComplexPower ε t)) y =
      positiveComplexPowerSecond ε t y := by
  have hevent : (fun x => deriv (positiveComplexPower ε t) x) =ᶠ[𝓝 y]
      positiveComplexPowerFirst ε t := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact (positiveComplexPower_hasDerivAt ε t hx).deriv
  exact ((positiveComplexPowerFirst_hasDerivAt ε t hy).congr_of_eventuallyEq
    hevent.symm).deriv

/-- For `ε=1` this is the `y^(1/2+i t)` wave; for `ε=-1` it is
`y^(1/2-i t)`. Both have the exact constant-mode eigenvalue `1/4+t²`.
The Euler formula is built into `positiveComplexPower`; no spectral
decomposition or L² assertion is inferred from these generalized waves. -/
theorem positiveComplexPower_eigen (ε t r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (positiveComplexPower ε t)) (Real.exp r) =
        (((1 / 4 : ℝ) + t ^ 2) : ℂ) *
          positiveComplexPower ε t (Real.exp r) := by
  have hy : 0 < Real.exp r := Real.exp_pos r
  have hc := cosine_constant_mode_eigen t r
  have hs := sine_constant_mode_eigen t r
  rw [constantMode_second_deriv (cosineLogProfile t)
    (cosineLogProfile_differentiable t)
    (cosineLogProfile_deriv_differentiable t) hy] at hc
  rw [constantMode_second_deriv (sineLogProfile t)
    (sineLogProfile_differentiable t)
    (sineLogProfile_deriv_differentiable t) hy] at hs
  have hcC := congrArg (fun z : ℝ => (z : ℂ)) hc
  have hsC := congrArg (fun z : ℝ => (z : ℂ)) hs
  push_cast at hcC hsC
  rw [positiveComplexPower_second_deriv ε t hy]
  simp only [positiveComplexPower, positiveComplexPowerSecond]
  push_cast
  linear_combination hcC + ((ε : ℂ) * Complex.I) * hsC

theorem positiveComplexPower_plus_eigen (t r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (positiveComplexPower 1 t)) (Real.exp r) =
        (((1 / 4 : ℝ) + t ^ 2) : ℂ) *
          positiveComplexPower 1 t (Real.exp r) :=
  positiveComplexPower_eigen 1 t r

theorem positiveComplexPower_minus_eigen (t r : ℝ) :
    -((Real.exp r) ^ 2) *
      deriv (deriv (positiveComplexPower (-1) t)) (Real.exp r) =
        (((1 / 4 : ℝ) + t ^ 2) : ℂ) *
          positiveComplexPower (-1) t (Real.exp r) :=
  positiveComplexPower_eigen (-1) t r

/-- At `t=0`, the repeated indicial root has the logarithmic second
solution. Its logarithmic profile is the identity, not another cosine wave. -/
def thresholdMode (y : ℝ) : ℝ := constantMode (fun _ => 1) y
def thresholdLogMode (y : ℝ) : ℝ := constantMode id y

theorem thresholdMode_eigen (r : ℝ) :
    -((Real.exp r) ^ 2) * deriv (deriv thresholdMode) (Real.exp r) =
      (1 / 4 : ℝ) * thresholdMode (Real.exp r) := by
  have h := constantMode_radial_conjugation (fun _ : ℝ => (1 : ℝ))
    (by fun_prop) (by fun_prop) r
  simpa [thresholdMode, constantMode, mul_comm, mul_left_comm, mul_assoc] using h

theorem thresholdLogMode_eigen (r : ℝ) :
    -((Real.exp r) ^ 2) * deriv (deriv thresholdLogMode) (Real.exp r) =
      (1 / 4 : ℝ) * thresholdLogMode (Real.exp r) := by
  have hsecond : deriv (deriv (id : ℝ → ℝ)) r = 0 := by
    simp
  have h := constantMode_radial_conjugation (id : ℝ → ℝ)
    (by fun_prop) (by simpa using (differentiable_const :
      Differentiable ℝ (fun _ : ℝ => (1 : ℝ)))) r
  simpa [thresholdLogMode, constantMode, hsecond,
    mul_comm, mul_left_comm, mul_assoc] using h

theorem thresholdLogMode_not_proportional :
    ¬∃ c : ℝ, ∀ y : ℝ, thresholdLogMode y = c * thresholdMode y := by
  rintro ⟨c, hc⟩
  have h1 := hc 1
  have hc0 : c = 0 := by
    simp [thresholdMode, thresholdLogMode, constantMode] at h1
    linarith
  have he : Real.sqrt (Real.exp 1) = 0 := by
    simpa [thresholdMode, thresholdLogMode, constantMode,
      Real.log_exp, hc0] using hc (Real.exp 1)
  have hpos : 0 < Real.sqrt (Real.exp 1) :=
    Real.sqrt_pos.2 (Real.exp_pos 1)
  exact hpos.ne' he

end
end ImbalancedChen.Part3.CuspConstantModeLogOperatorSourceOnly
