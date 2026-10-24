import ImbalancedChen.Part3ImaginaryOrderKZeroOrderPositivity
import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import ImbalancedChen.Part3ActualKProfileLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24. No acceptance credit.

The real-order parameter `t` belongs to the repository's actual integral
realization of K_(2it). The horizontal coordinate is period one. The
physical cusp width `w` occurs in q = 2*pi*|n|*y/w, with n nonzero; hence
no n=0 assertion is made. The `sqrt y` factor and `dy/y^2` below are the
standard Maass Fourier-mode and hyperbolic area normalizations.

This is one mode only. There is no automorphic eigenfunction, Fourier
coefficient, spectral expansion, or global cusp sum in this file.
-/

namespace ImbalancedChen.Part3.RadialCuspTailEnergySourceOnly

noncomputable section
open Set MeasureTheory
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKZeroOrderPositivitySourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The argument of the actual K integral for the width-w, nonzero mode. -/
def modeScale (n : ℤ) (w : ℝ) : ℝ :=
  2 * Real.pi * |(n : ℝ)| / w

theorem modeScale_pos {n : ℤ} {w : ℝ} (hn : n ≠ 0) (hw : 0 < w) :
    0 < modeScale n w := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold modeScale
  positivity

/-- The phase is on the normalized period-one circle; width is already in
`modeScale`, so no extra width factor belongs in the horizontal Haar mass. -/
def nonzeroCuspMode (n : ℤ) (w t : ℝ)
    (x : AddCircle (1 : ℝ)) (y : ℝ) : ℂ :=
  ((Real.sqrt y * imaginaryOrderK t (modeScale n w * y) : ℝ) : ℂ) *
    AddCircle.fourier n x

theorem nonzeroCuspMode_norm_sq (n : ℤ) (w t : ℝ)
    (x : AddCircle (1 : ℝ)) {y : ℝ} (hy : 0 ≤ y) :
    ‖nonzeroCuspMode n w t x y‖ ^ 2 =
      y * imaginaryOrderK t (modeScale n w * y) ^ 2 := by
  simp only [nonzeroCuspMode, norm_mul, fourier_apply, Circle.norm_coe,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg y)]
  rw [mul_pow, sq_abs, Real.sq_sqrt hy]
  ring

/-- The horizontal cross-section has normalized Haar mass one. -/
theorem nonzeroCuspMode_horizontal_energy (n : ℤ) (w t : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ x : AddCircle (1 : ℝ), ‖nonzeroCuspMode n w t x y‖ ^ 2
      ∂AddCircle.haarAddCircle) =
      y * imaginaryOrderK t (modeScale n w * y) ^ 2 := by
  simp_rw [nonzeroCuspMode_norm_sq n w t _ hy]
  simp

/-- A genuinely exponential zero-order bound. It uses the same integral as
`imaginaryOrderK_zero_pos` and the already proved K0 domination. Averaging
`1 <= cosh u` and `u/2 <= cosh u` keeps both exponential factors. -/
theorem imaginaryOrderK_zero_exponential {q : ℝ} (hq : 0 < q) :
    imaginaryOrderK 0 q ≤ (4 / q) * Real.exp (-q / 2) := by
  have hmajor : IntegrableOn
      (fun u : ℝ => Real.exp (-(q / 4) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -(q / 4) < 0) 0
  have hK : IntegrableOn
      (fun u : ℝ => Real.exp (-q * Real.cosh u)) (Ioi 0) := by
    simpa [kIntegrand] using kIntegrand_integrable (0 : ℝ) hq
  have hpoint (u : ℝ) :
      Real.exp (-q * Real.cosh u) ≤
        Real.exp (-q / 2) * Real.exp (-(q / 4) * u) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := Real.one_le_cosh u
    have h2 := half_le_cosh u
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr h1),
      mul_nonneg hq.le (sub_nonneg.mpr h2)]
  have hupper :
      (∫ u in Ioi (0 : ℝ), Real.exp (-q * Real.cosh u)) ≤
        ∫ u in Ioi (0 : ℝ),
          Real.exp (-q / 2) * Real.exp (-(q / 4) * u) := by
    apply integral_mono hK (hmajor.const_mul _)
    exact hpoint
  have hexp :
      (∫ u in Ioi (0 : ℝ), Real.exp (-(q / 4) * u)) = 4 / q := by
    rw [integral_exp_mul_Ioi (by linarith : -(q / 4) < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hq.ne']
  simpa [imaginaryOrderK, kIntegrand, integral_const_mul, hexp,
    mul_comm] using hupper

theorem imaginaryOrderK_exponential (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |imaginaryOrderK t q| ≤ (4 / q) * Real.exp (-q / 2) :=
  (imaginaryOrderK_abs_le_zero t hq).trans
    (imaginaryOrderK_zero_exponential hq)

/-- The exact radial integrand after horizontal Haar integration and the
hyperbolic density: (sqrt y K)^2 dy/y^2 = K^2 dy/y. -/
def radialHyperbolicEnergyDensity (n : ℤ) (w t y : ℝ) : ℝ :=
  imaginaryOrderK t (modeScale n w * y) ^ 2 / y

theorem radialHyperbolicEnergyDensity_eq (n : ℤ) (w t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    radialHyperbolicEnergyDensity n w t y =
      (Real.sqrt y * imaginaryOrderK t (modeScale n w * y)) ^ 2 / y ^ 2 := by
  simp only [radialHyperbolicEnergyDensity, mul_pow, Real.sq_sqrt hy.le]
  field_simp [hy.ne']

/-- The literal horizontal Haar integral with hyperbolic dy/y² density
reduces exactly to the radial energy density. -/
theorem horizontal_hyperbolic_energy_density (n : ℤ) (w t : ℝ)
    {y : ℝ} (hy : 0 < y) :
    (∫ x : AddCircle (1 : ℝ), ‖nonzeroCuspMode n w t x y‖ ^ 2
      ∂AddCircle.haarAddCircle) / y ^ 2 =
      radialHyperbolicEnergyDensity n w t y := by
  rw [nonzeroCuspMode_horizontal_energy n w t hy.le]
  dsimp [radialHyperbolicEnergyDensity]
  field_simp [hy.ne']

/-- Pointwise exponential energy domination on y >= Y > 0. The constant
keeps the physical width through c = 2*pi*|n|/w. -/
theorem radial_energy_le_exp {n : ℤ} {w Y : ℝ}
    (hn : n ≠ 0) (hw : 0 < w) (hY : 0 < Y)
    (t : ℝ) {y : ℝ} (hy : Y ≤ y) :
    radialHyperbolicEnergyDensity n w t y ≤
      (16 / ((modeScale n w) ^ 2 * Y ^ 3)) *
        Real.exp (-(modeScale n w) * y) := by
  let c := modeScale n w
  have hc : 0 < c := modeScale_pos hn hw
  have hy0 : 0 < y := hY.trans_le hy
  have hq : 0 < c * y := mul_pos hc hy0
  have hK := imaginaryOrderK_exponential t hq
  have hKsq : imaginaryOrderK t (c * y) ^ 2 ≤
      ((4 / (c * y)) * Real.exp (-(c * y) / 2)) ^ 2 := by
    have hb : 0 ≤ (4 / (c * y)) * Real.exp (-(c * y) / 2) := by positivity
    nlinarith [abs_nonneg (imaginaryOrderK t (c * y)),
      sq_abs (imaginaryOrderK t (c * y))]
  have he : Real.exp (-(c * y) / 2) ^ 2 = Real.exp (-(c * y)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  dsimp [radialHyperbolicEnergyDensity]
  calc
    imaginaryOrderK t (c * y) ^ 2 / y ≤
        (((4 / (c * y)) * Real.exp (-(c * y) / 2)) ^ 2) / y :=
      div_le_div_of_nonneg_right hKsq hy0.le
    _ = (16 / (c ^ 2 * y ^ 3)) * Real.exp (-(c * y)) := by
      rw [mul_pow, he]
      field_simp [hc.ne', hy0.ne'] <;> ring
    _ ≤ (16 / (c ^ 2 * Y ^ 3)) * Real.exp (-(c * y)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      gcongr
  
/-- The single nonzero cusp mode has finite hyperbolic radial L2 energy.
The upper bound is explicit and exponential in the start height Y. -/
theorem radial_tail_integrable_and_bound {n : ℤ} {w Y : ℝ}
    (hn : n ≠ 0) (hw : 0 < w) (hY : 0 < Y) (t : ℝ) :
    IntegrableOn (radialHyperbolicEnergyDensity n w t) (Ioi Y) ∧
      (∫ y in Ioi Y, radialHyperbolicEnergyDensity n w t y) ≤
        (16 / ((modeScale n w) ^ 3 * Y ^ 3)) *
          Real.exp (-(modeScale n w) * Y) := by
  let c := modeScale n w
  have hc : 0 < c := modeScale_pos hn hw
  have hmajor : IntegrableOn (fun y : ℝ => Real.exp (-c * y)) (Ioi Y) :=
    integrableOn_exp_mul_Ioi (by linarith : -c < 0) Y
  have hcont : ContinuousOn (radialHyperbolicEnergyDensity n w t) (Ioi Y) := by
    -- Joint continuity of the actual integral on q >= c*Y is the input here.
    have hK := imaginaryOrderK_joint_continuous (c * Y) (mul_pos hc hY)
    have hq : ContinuousOn
        (fun y : ℝ => imaginaryOrderK t (c * y)) (Ioi Y) := by
      have hmap : Continuous (fun y : Ioi Y =>
          ((t, ⟨c * (y : ℝ), le_of_lt (mul_lt_mul_of_pos_left y.property hc)⟩) :
            ℝ × Ici (c * Y))) := by fun_prop
      exact continuousOn_iff_continuous_restrict.mpr (hK.comp hmap)
    exact (hq.pow 2).div continuousOn_id (fun y hy => (hY.trans hy).ne')
  have hpoint (y : ℝ) (hy : y ∈ Ioi Y) :
      ‖radialHyperbolicEnergyDensity n w t y‖ ≤
        (16 / (c ^ 2 * Y ^ 3)) * Real.exp (-c * y) := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact radial_energy_le_exp hn hw hY t hy.le
    · exact div_nonneg (sq_nonneg _) (hY.trans hy).le
  have htail : IntegrableOn (radialHyperbolicEnergyDensity n w t) (Ioi Y) := by
    exact ((hmajor.const_mul (16 / (c ^ 2 * Y ^ 3))).mono'
      hcont.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact hpoint y hy))
  refine ⟨htail, ?_⟩
  have hint :
      (∫ y in Ioi Y, radialHyperbolicEnergyDensity n w t y) ≤
        ∫ y in Ioi Y, (16 / (c ^ 2 * Y ^ 3)) * Real.exp (-c * y) := by
    apply integral_mono_ae htail (hmajor.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact radial_energy_le_exp hn hw hY t hy.le
  have hexp : (∫ y in Ioi Y, Real.exp (-c * y)) =
      Real.exp (-c * Y) / c := by
    rw [integral_exp_mul_Ioi (by linarith : -c < 0) Y]
    field_simp [hc.ne']
  calc
    (∫ y in Ioi Y, radialHyperbolicEnergyDensity n w t y) ≤
        ∫ y in Ioi Y, (16 / (c ^ 2 * Y ^ 3)) * Real.exp (-c * y) := hint
    _ = (16 / (c ^ 3 * Y ^ 3)) * Real.exp (-c * Y) := by
      rw [integral_const_mul, hexp]
      field_simp [hc.ne', hY.ne'] <;> ring

/-- Finite hyperbolic L² energy of the literal nonzero Fourier-Bessel mode
on the cusp cylinder above Y, with normalized horizontal period one. -/
theorem nonzeroCuspMode_hyperbolic_L2_tail {n : ℤ} {w Y : ℝ}
    (hn : n ≠ 0) (hw : 0 < w) (hY : 0 < Y) (t : ℝ) :
    IntegrableOn
      (fun y : ℝ =>
        (∫ x : AddCircle (1 : ℝ), ‖nonzeroCuspMode n w t x y‖ ^ 2
          ∂AddCircle.haarAddCircle) / y ^ 2) (Ioi Y) ∧
      (∫ y in Ioi Y,
        (∫ x : AddCircle (1 : ℝ), ‖nonzeroCuspMode n w t x y‖ ^ 2
          ∂AddCircle.haarAddCircle) / y ^ 2) ≤
        (16 / ((modeScale n w) ^ 3 * Y ^ 3)) *
          Real.exp (-(modeScale n w) * Y) := by
  have hradial := radial_tail_integrable_and_bound hn hw hY t
  have heq :
      (fun y : ℝ =>
        (∫ x : AddCircle (1 : ℝ), ‖nonzeroCuspMode n w t x y‖ ^ 2
          ∂AddCircle.haarAddCircle) / y ^ 2) =ᵐ[volume.restrict (Ioi Y)]
        radialHyperbolicEnergyDensity n w t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact horizontal_hyperbolic_energy_density n w t (hY.trans hy)
  refine ⟨hradial.1.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact hradial.2

end
end ImbalancedChen.Part3.RadialCuspTailEnergySourceOnly
