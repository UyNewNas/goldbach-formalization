/-
SPDX-License-Identifier: Apache-2.0

HELD SOURCE CANDIDATE: static source review only; no Lean/Lake execution.
The imported generic triangle/swap module is CI verified. The imported
variable-kernel harmonic limits and this assembly still await CI.

These are actual harmonic-sum limits, with their original centre-masked
half-open prime selectors, not lower bounds for the sifted Y5/Y6 counts.
The only scalar hypothesis is ContinuousOn f [1,5]. The manuscript level
is the separately defined literal two-affine minimum vLevel; no envelope
comparison or reserved VariableEnvelope module is used.
-/
import ImbalancedChen.ChenVariablePairHarmonicLimit
import ImbalancedChen.SymmetricTriangleIntegral

namespace ImbalancedChen.ChenVariableTriangleLimits

noncomputable section

open Filter Topology
open ChenVariablePairKernel ChenVariablePairHarmonicLimit

/-- On the ordered region the density has exactly the manuscript argument
and denominator, with t the larger coordinate. -/
theorem weightedKernel_ordered (f : ℝ → ℝ) {u t : ℝ} (hut : u ≤ t) :
    weightedKernel f u t = f ((vLevel t - t - u) / a) / (t * u) := by
  rw [weightedKernel, kernel_of_le f hut, mul_comm u t]

/-- The genuine half-square limit for the fifth selector equals the
manuscript's triangle, with outer larger coordinate t and inner u ≤ t. -/
theorem half_square_eq_y5_triangle {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    (1 / 2 : ℝ) * (∫ u in a..h, ∫ t in a..h, weightedKernel f u t) =
      ∫ t in a..h, ∫ u in a..t, f ((vLevel t - t - u) / a) / (t * u) := by
  calc
    (1 / 2 : ℝ) * (∫ u in a..h, ∫ t in a..h, weightedKernel f u t) =
        ∫ t in a..h, ∫ u in a..t, weightedKernel f t u :=
      SymmetricTriangleIntegral.half_square_eq_triangle a_lt_h.le
        (continuousOn_weightedKernel_R5 hf)
        (fun t _ u _ => weightedKernel_symm f t u)
    _ = ∫ t in a..h, ∫ u in a..t,
        f ((vLevel t - t - u) / a) / (t * u) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a h := by
        simpa only [Set.uIcc_of_le a_lt_h.le] using ht
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc a t := by
        simpa only [Set.uIcc_of_le ht'.1] using hu
      rw [weightedKernel_symm f t u]
      exact weightedKernel_ordered f hu'.2

/-- Rectangular Fubini puts the entire sixth-term band in manuscript
order. The outer interval ends at d, with no argument-below-2 deletion. -/
theorem rectangle_eq_y6_manuscript {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    (∫ u in a..h, ∫ t in h..d, weightedKernel f u t) =
      ∫ t in h..d, ∫ u in a..h, f ((vLevel t - t - u) / a) / (t * u) := by
  calc
    (∫ u in a..h, ∫ t in h..d, weightedKernel f u t) =
        ∫ t in h..d, ∫ u in a..h, weightedKernel f u t :=
      SymmetricTriangleIntegral.rectangle_integral_swap a_lt_h.le h_lt_d.le
        (continuousOn_weightedKernel_R6 hf)
    _ = ∫ t in h..d, ∫ u in a..h,
        f ((vLevel t - t - u) / a) / (t * u) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc h d := by
        simpa only [Set.uIcc_of_le h_lt_d.le] using ht
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc a h := by
        simpa only [Set.uIcc_of_le a_lt_h.le] using hu
      exact weightedKernel_ordered f (hu'.2.trans ht'.1)

/-- The original fifth harmonic sum converges to the actual triangle. -/
theorem tendsto_y5HarmonicSum_triangle {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (y5HarmonicSum f) atTop
      (𝓝 (∫ t in a..h, ∫ u in a..t,
        f ((vLevel t - t - u) / a) / (t * u))) := by
  simpa only [half_square_eq_y5_triangle hf] using
    (ChenVariablePairHarmonicLimit.tendsto_y5HarmonicSum hf)

/-- The original sixth harmonic sum converges to the full manuscript
rectangle in outer-t/inner-u order. -/
theorem tendsto_y6HarmonicSum_manuscript {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (y6HarmonicSum f) atTop
      (𝓝 (∫ t in h..d, ∫ u in a..h,
        f ((vLevel t - t - u) / a) / (t * u))) := by
  simpa only [rectangle_eq_y6_manuscript hf] using
    (ChenVariablePairHarmonicLimit.tendsto_y6HarmonicSum hf)

/-- The fifth literal larger-coordinate numerator has the same genuine
triangle limit; its source selector and totient denominator are unchanged. -/
theorem tendsto_orderedY5HarmonicSum_triangle {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY5HarmonicSum f) atTop
      (𝓝 (∫ t in a..h, ∫ u in a..t,
        f ((vLevel t - t - u) / a) / (t * u))) := by
  simpa only [half_square_eq_y5_triangle hf] using
    (ChenVariablePairHarmonicLimit.tendsto_orderedY5HarmonicSum hf)

/-- The sixth literal larger-coordinate numerator keeps the entire
second band h ≤ t ≤ d in the limiting integral. -/
theorem tendsto_orderedY6HarmonicSum_manuscript {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY6HarmonicSum f) atTop
      (𝓝 (∫ t in h..d, ∫ u in a..h,
        f ((vLevel t - t - u) / a) / (t * u))) := by
  simpa only [rectangle_eq_y6_manuscript hf] using
    (ChenVariablePairHarmonicLimit.tendsto_orderedY6HarmonicSum hf)

/-- An entirely explicit target for the fifth literal harmonic sum.
Only the named source sum remains folded; no target constant is hidden. -/
theorem tendsto_orderedY5HarmonicSum_explicit {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY5HarmonicSum f) atTop
      (𝓝 (∫ t in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
        ∫ u in (100 / 1149 : ℝ)..t,
          f ((min ((1 + t) / 2) (57 / 64 - 3 * t / 2) - t - u) /
            (100 / 1149)) / (t * u))) := by
  simpa only [a, h, vLevel] using (tendsto_orderedY5HarmonicSum_triangle hf)

/-- An entirely explicit target for the full sixth literal harmonic sum. -/
theorem tendsto_orderedY6HarmonicSum_explicit {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 1 5)) :
    Tendsto (orderedY6HarmonicSum f) atTop
      (𝓝 (∫ t in (50 / 309 : ℝ)..(183 / 766 : ℝ),
        ∫ u in (100 / 1149 : ℝ)..(50 / 309 : ℝ),
          f ((min ((1 + t) / 2) (57 / 64 - 3 * t / 2) - t - u) /
            (100 / 1149)) / (t * u))) := by
  simpa only [a, h, d, vLevel] using (tendsto_orderedY6HarmonicSum_manuscript hf)

end
end ImbalancedChen.ChenVariableTriangleLimits
