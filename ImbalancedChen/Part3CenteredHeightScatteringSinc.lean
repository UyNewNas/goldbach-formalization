import ImbalancedChen.Part3FiniteHeightScatteringGram
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

/-!
# Centered finite-height sinc kernel and normalized two-channel Gram

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The exact centered kernel is 2*R*sinc(k*R), including k=0.
The two-channel wave is multiplied by sqrt(1/2), so its actual finite
Gram is one half of the incoming-coefficient-one Gram. This is a local
normalization identity, not an Eisenstein spectral measure theorem.
-/
namespace ImbalancedChen.Part3.CenteredHeightScatteringSinc20261026b
noncomputable section
open MeasureTheory
open HeightScatteringWaveGram20261026b FiniteLogHeightKernel20261026b
open FiniteHeightScatteringGram20261026b CuspCylinderMeasure20261024z

theorem logBandKernel_centered_sinc (R k : ℝ) :
    logBandKernel (-R) R k = ((2 * R * Real.sinc (k * R) : ℝ) : ℂ) := by
  by_cases hk : k = 0
  · simp [hk, logBandKernel_zero]
    <;> ring
  have hfun : planeWave k = fun r : ℝ => Complex.exp (((k * r : ℝ) : ℂ) * Complex.I) := by
    funext r
    unfold planeWave
    congr 1
    push_cast
    ring
  unfold logBandKernel
  rw [hfun, intervalIntegral.integral_comp_mul_left
    (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) hk]
  rw [mul_neg, intervalIntegral.integral_exp_mul_I_eq_sinc]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hk]
  <;> ring

/-- Each channel receives half the direct norm, without deleting either
of the reflection cross terms. -/
def normalizedScatteringWave (t : ℝ) (c : ℂ) (y : PositiveHeight) : ℂ :=
  (Real.sqrt (1 / 2 : ℝ) : ℂ) * scatteringWave t c y

def normalizedFiniteHeightGram (a b t u : ℝ) (c d : ℂ) : ℂ :=
  ∫ r in a..b, star (normalizedScatteringWave t c (expHeight r)) *
    normalizedScatteringWave u d (expHeight r) / ((Real.exp r : ℝ) : ℂ)

/-- Actual pointwise scalar normalization, before integration. -/
theorem normalizedScatteringWave_gram (t u : ℝ) (c d : ℂ) (y : PositiveHeight) :
    star (normalizedScatteringWave t c y) * normalizedScatteringWave u d y / (y : ℂ) =
      (1 / 2 : ℂ) * (star (scatteringWave t c y) * scatteringWave u d y / (y : ℂ)) := by
  have hs : (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold normalizedScatteringWave
  rw [Complex.star_def, map_mul, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ 2 *
      (star (scatteringWave t c y) * scatteringWave u d y / (y : ℂ)) := by ring
    _ = _ := by rw [hs]

theorem normalizedFiniteHeightGram_eq_half (a b t u : ℝ) (c d : ℂ) :
    normalizedFiniteHeightGram a b t u c d =
      (1 / 2 : ℂ) * finiteHeightScatteringGram a b t u c d := by
  unfold normalizedFiniteHeightGram finiteHeightScatteringGram
  have hpoint (r : ℝ) := normalizedScatteringWave_gram t u c d (expHeight r)
  simp only [expHeight] at hpoint
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]

/-- Exact normalized centered diagonal. Sinc supplies the removable t=0
value; both cross terms remain present through c+conj(c). -/
theorem normalizedFiniteHeightGram_centered_diagonal (R t : ℝ) (c : ℂ)
    (hc : ‖c‖ = 1) :
    normalizedFiniteHeightGram (-R) R t t c c =
      ((2 * R : ℝ) : ℂ) + (c + star c) * ((R * Real.sinc (2 * t * R) : ℝ) : ℂ) := by
  rw [normalizedFiniteHeightGram_eq_half,
    finiteHeightScatteringGram_diagonal (-R) R t c hc,
    logBandKernel_centered_sinc, logBandKernel_centered_sinc]
  have hneg : -2 * t * R = -(2 * t * R) := by ring
  rw [hneg, Real.sinc_neg]
  push_cast
  ring

/-- The normalized diagonal is continuous through zero frequency for
any fixed unit-modulus local scattering coefficient. -/
theorem normalizedFiniteHeightGram_centered_diagonal_continuous
    (R : ℝ) (c : ℂ) (hc : ‖c‖ = 1) :
    Continuous (fun t : ℝ => normalizedFiniteHeightGram (-R) R t t c c) := by
  simp_rw [normalizedFiniteHeightGram_centered_diagonal R _ c hc]
  fun_prop

end
end ImbalancedChen.Part3.CenteredHeightScatteringSinc20261026b
