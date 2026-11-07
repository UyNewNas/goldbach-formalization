import ImbalancedChen.Part3FiniteLogHeightKernel
import Mathlib.Tactic

/-!
# Actual four-term scattering-wave Gram on a finite log-height band

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The left side pairs the actual physical sqrt(y) waves at y=exp(r),
including the reciprocal y factor left by dy/y^2 after dy=y*dr.
All four boundary kernels are retained, and the resonant diagonals use
the continuous integral kernel rather than an undefined quotient.
This proves a local finite-height Gram identity only. It does not replace
the quotient Green formula, Eisenstein unfolding, or completeness.
-/
namespace ImbalancedChen.Part3.FiniteHeightScatteringGram20261026b
noncomputable section
open Set MeasureTheory
open CuspCylinderMeasure20261024z HeightMellinUnitary20261026b
open HeightScatteringWaveGram20261026b FiniteLogHeightKernel20261026b

def expHeight (r : ℝ) : PositiveHeight := ⟨Real.exp r, Real.exp_pos r⟩

/-- Literal physical-wave Gram in logarithmic height coordinates. -/
def finiteHeightScatteringGram (a b t u : ℝ) (c d : ℂ) : ℂ :=
  ∫ r in a..b, star (scatteringWave t c (expHeight r)) *
    scatteringWave u d (expHeight r) / ((Real.exp r : ℝ) : ℂ)

/-- The actual four pointwise terms integrate to the four continuous
boundary kernels, with both difference and sum frequencies. -/
theorem finiteHeightScatteringGram_eq_four_kernels
    (a b t u : ℝ) (c d : ℂ) :
    finiteHeightScatteringGram a b t u c d =
      logBandKernel a b (t - u) + d * logBandKernel a b (t + u) +
      star c * logBandKernel a b (-t - u) +
      star c * d * logBandKernel a b (u - t) := by
  unfold finiteHeightScatteringGram
  have hpoint (r : ℝ) := scatteringWave_gram t u c d (expHeight r)
  simp only [expHeight, Real.log_exp] at hpoint
  simp_rw [hpoint]
  have h1 := planeWave_intervalIntegrable a b (t - u)
  have h2 := (planeWave_intervalIntegrable a b (t + u)).const_mul d
  have h3 := (planeWave_intervalIntegrable a b (-t - u)).const_mul (star c)
  have h4 := (planeWave_intervalIntegrable a b (u - t)).const_mul (star c * d)
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul, logBandKernel]

/-- Off both resonant hyperplanes, the finite physical Gram is exactly
four endpoint exponential quotients. -/
theorem finiteHeightScatteringGram_eq_boundary_terms
    (a b t u : ℝ) (c d : ℂ) (hminus : t - u ≠ 0) (hplus : t + u ≠ 0) :
    finiteHeightScatteringGram a b t u c d =
      (planeWave (t - u) b - planeWave (t - u) a) / (Complex.I * ((t - u : ℝ) : ℂ)) +
      d * ((planeWave (t + u) b - planeWave (t + u) a) / (Complex.I * ((t + u : ℝ) : ℂ))) +
      star c * ((planeWave (-t - u) b - planeWave (-t - u) a) / (Complex.I * ((-t - u : ℝ) : ℂ))) +
      star c * d * ((planeWave (u - t) b - planeWave (u - t) a) / (Complex.I * ((u - t : ℝ) : ℂ))) := by
  rw [finiteHeightScatteringGram_eq_four_kernels,
    logBandKernel_eq_boundary_quotient a b hminus,
    logBandKernel_eq_boundary_quotient a b hplus,
    logBandKernel_eq_boundary_quotient a b (show -t - u ≠ 0 by intro h; apply hplus; linarith),
    logBandKernel_eq_boundary_quotient a b (show u - t ≠ 0 by intro h; apply hminus; linarith)]

/-- The exact unit-modulus diagonal keeps both reflected cross terms.
The two direct terms are 2*(b-a), including at t=0. -/
theorem finiteHeightScatteringGram_diagonal
    (a b t : ℝ) (c : ℂ) (hc : ‖c‖ = 1) :
    finiteHeightScatteringGram a b t t c c =
      (2 : ℂ) * ((b - a : ℝ) : ℂ) +
      c * logBandKernel a b (2 * t) + star c * logBandKernel a b (-2 * t) := by
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [finiteHeightScatteringGram_eq_four_kernels]
  have e2 : t + t = 2 * t := by ring
  have e3 : -t - t = -2 * t := by ring
  rw [sub_self, logBandKernel_zero, e2, e3, hcc]
  ring

/-- Both resonance crossings are removable for fixed local coefficients.
For spectral-parameter-dependent scattering coefficients, their genuine
continuity is an additional analytic input, not an assumed normalization. -/
theorem finiteHeightScatteringGram_continuous (a b : ℝ) (c d : ℂ) :
    Continuous (fun p : ℝ × ℝ => finiteHeightScatteringGram a b p.1 p.2 c d) := by
  simp_rw [finiteHeightScatteringGram_eq_four_kernels]
  apply Continuous.add
  · apply Continuous.add
    · exact (logBandKernel_difference_continuous a b).add
        ((logBandKernel_sum_continuous a b).const_mul d)
    · exact ((logBandKernel_continuous a b).comp
        (continuous_fst.neg.sub continuous_snd)).const_mul (star c)
  · exact ((logBandKernel_continuous a b).comp
      (continuous_snd.sub continuous_fst)).const_mul (star c * d)

end
end ImbalancedChen.Part3.FiniteHeightScatteringGram20261026b
