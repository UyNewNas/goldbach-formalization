import ImbalancedChen.Part3RealOrderKFirstMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

An explicit endpoint normalization for the actual real-order K integral:
the first q moments at alpha = 1 and alpha = -1 are pi/2. The remaining
sech integral is proved from the primitive arctan(sinh u), not supplied as
a hypothesis. Absolute-order comparison then gives the sharper pi/2 upper
bound throughout |alpha| <= 1, including the exceptional 7/32 interval.

This does not evaluate the interior alpha Gamma product or construct an
automorphic spectral normalization.
-/

namespace ImbalancedChen.Part3.RealOrderKEndpointMoment20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RealOrderKExceptionalSourceOnly
open RealOrderKFirstMoment20261025a

private def sechPrimitive (u : ℝ) : ℝ := Real.arctan (Real.sinh u)

private theorem sechPrimitive_deriv (u : ℝ) :
    HasDerivAt sechPrimitive (1 / Real.cosh u) u := by
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hden : 1 + Real.sinh u ^ 2 = Real.cosh u ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  change HasDerivAt (fun x : ℝ => Real.arctan (Real.sinh x))
    (1 / Real.cosh u) u
  apply ((Real.hasDerivAt_sinh u).arctan).congr_deriv
  rw [hden]
  field_simp [hc] <;> ring

private theorem sinh_tendsto_atTop : Tendsto Real.sinh atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact Real.self_le_sinh_iff.mpr hu

private theorem sechPrimitive_tendsto :
    Tendsto sechPrimitive atTop (𝓝 (Real.pi / 2)) := by
  exact (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
    sinh_tendsto_atTop

/-- Integrability of the positive inverse-cosh kernel on the half-line. -/
theorem sech_integrable :
    IntegrableOn (fun u : ℝ => 1 / Real.cosh u) (Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (g := sechPrimitive) (l := Real.pi / 2)
    (fun u _ => sechPrimitive_deriv u)
    (fun u _ => (one_div_pos.mpr (Real.cosh_pos u)).le)
    sechPrimitive_tendsto

/-- The actual half-line sech integral, including its exact pi/2 constant. -/
theorem sech_integral :
    (∫ u in Ioi (0 : ℝ), 1 / Real.cosh u) = Real.pi / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := sechPrimitive) (g' := fun u : ℝ => 1 / Real.cosh u)
    (l := Real.pi / 2)
    (fun u _ => sechPrimitive_deriv u)
    (fun u _ => (one_div_pos.mpr (Real.cosh_pos u)).le)
    sechPrimitive_tendsto
  simpa [sechPrimitive] using h

/-- The first q moment of the literal alpha=1 K integral is pi/2. -/
theorem realOrderK_one_first_moment :
    (∫ q in Ioi (0 : ℝ), q * realOrderK 1 q) = Real.pi / 2 := by
  rw [realOrderK_first_moment (α := (1 : ℝ)) (by norm_num)]
  calc
    (∫ u in Ioi (0 : ℝ), firstMomentDensity 1 u) =
        ∫ u in Ioi (0 : ℝ), 1 / Real.cosh u := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => by
        simp only [firstMomentDensity, one_mul]
        field_simp [(Real.cosh_pos u).ne'] <;> ring)
    _ = Real.pi / 2 := sech_integral

/-- The negative endpoint has the same normalization by actual K evenness. -/
theorem realOrderK_neg_one_first_moment :
    (∫ q in Ioi (0 : ℝ), q * realOrderK (-1) q) = Real.pi / 2 := by
  simpa only [realOrderK_even] using realOrderK_one_first_moment

/-- A sharp endpoint envelope for the real-order first moment. -/
theorem realOrderK_first_moment_le_pi_half {α : ℝ} (hα : |α| ≤ 1) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) ≤ Real.pi / 2 := by
  rw [← realOrderK_one_first_moment]
  apply realOrderK_first_moment_mono_abs (β := (1 : ℝ)) (by norm_num)
  simpa only [abs_one] using hα

/-- In particular, every actual exceptional-order first moment obeys pi/2. -/
theorem exceptionalK_first_moment_le_pi_half {α : ℝ}
    (hα : |α| ≤ (7 / 32 : ℝ)) :
    (∫ q in Ioi (0 : ℝ), q * realOrderK α q) ≤ Real.pi / 2 :=
  realOrderK_first_moment_le_pi_half (by linarith)

end
end ImbalancedChen.Part3.RealOrderKEndpointMoment20261025a
