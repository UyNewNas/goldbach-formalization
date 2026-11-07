import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Tactic

/-!
# Honest Cauchy-dominated parameter differentiation on finite measures

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
A value bound on a genuine complex disk gives the derivative bound on the
half disk. The actual derivative is measurable by its punctured slope
limit, not an assumed derivative-measurability input. The native integral
DCT then differentiates the original integral and proves L1 of its jet.
This is intended for the original restricted compact quotient measure.
-/
namespace ImbalancedChen.Part3.FiniteMeasureCauchyParameterIntegral20261026b
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- A genuine Cauchy derivative bound selected before the measured point. -/
theorem disk_derivative_bound (f : ℂ → ℂ) {u : ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 < C)
    (hd : ∀ v ∈ ball u R, DifferentiableAt ℂ f v)
    (hb : ∀ v ∈ ball u R, ‖f v‖ ≤ C) {v : ℂ} (hv : v ∈ ball u (R / 2)) :
    ‖deriv f v‖ ≤ 4 * C / R := by
  have hsub : ball v (R / 2) ⊆ ball u R := by
    intro w hw
    have htri := dist_triangle w v u
    have hw' := mem_ball.mp hw
    have hv' := mem_ball.mp hv
    apply mem_ball.mpr
    linarith
  have hvR : v ∈ ball u R := by
    apply mem_ball.mpr
    linarith [mem_ball.mp hv]
  have hdiff : DifferentiableOn ℂ f (ball v (R / 2)) :=
    fun w hw => (hd w (hsub hw)).differentiableWithinAt
  have hmaps : MapsTo f (ball v (R / 2)) (closedBall (f v) (2 * C)) := by
    intro w hw
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb w (hsub hw), hb v hvR])
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps (half_pos hR)
  convert h using 1 <;> field_simp [hR.ne'] <;> ring

/-- The parameter jet of an a.e. holomorphic measurable family is itself
measurable, by the actual punctured slope limit. -/
theorem actual_parameter_derivative_aestronglyMeasurable (F : ℂ → X → ℂ) (u : ℂ)
    (hm : ∀ v, AEStronglyMeasurable (F v) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℂ (fun v => F v x) u) :
    AEStronglyMeasurable (fun x => deriv (fun v => F v x) u) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] u)
    (f := fun v x => slope (fun w => F w x) u v)
  · intro v
    simpa only [slope_def_module] using ((hm v).sub (hm u)).const_smul ((v - u)⁻¹)
  · filter_upwards [hd] with x hx
    exact hx.hasDerivAt.tendsto_slope

/-- Differentiation of the ORIGINAL measured integral from an actual
uniform value bound and actual holomorphy. Both input and output L1 are
proved; no integral identity or derivative bound is a hypothesis. -/
theorem hasDerivAt_original_integral_of_disk_bound (F : ℂ → X → ℂ)
    (u : ℂ) {R C : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hm : ∀ v, AEStronglyMeasurable (F v) μ)
    (hd : ∀ᵐ x ∂μ, ∀ v ∈ ball u R, DifferentiableAt ℂ (fun w => F w x) v)
    (hb : ∀ᵐ x ∂μ, ∀ v ∈ ball u R, ‖F v x‖ ≤ C) :
    Integrable (fun x => deriv (fun v => F v x) u) μ ∧
      HasDerivAt (fun v => ∫ x, F v x ∂μ) (∫ x, deriv (fun v => F v x) u ∂μ) u := by
  have hu : u ∈ ball u R := mem_ball_self hR
  have huHalf : u ∈ ball u (R / 2) := mem_ball_self (half_pos hR)
  have hi : Integrable (F u) μ :=
    (integrable_const C).mono' (hm u) (hb.mono (fun x hx => hx u hu))
  have hdm : AEStronglyMeasurable (fun x => deriv (fun v => F v x) u) μ :=
    actual_parameter_derivative_aestronglyMeasurable F u hm
      (hd.mono (fun x hx => hx u hu))
  have hderivbound : ∀ᵐ x ∂μ, ∀ v ∈ ball u (R / 2),
      ‖deriv (fun w => F w x) v‖ ≤ 4 * C / R := by
    filter_upwards [hd, hb] with x hdx hbx
    intro v hv
    exact disk_derivative_bound (fun w => F w x) hR hC hdx hbx hv
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds u (half_pos hR))
    (Eventually.of_forall hm) hi hdm hderivbound (integrable_const (4 * C / R)) ?_
  filter_upwards [hd] with x hx
  intro v hv
  have hvR : v ∈ ball u R := by
    apply mem_ball.mpr
    linarith [mem_ball.mp hv]
  exact (hx v hvR).hasDerivAt

end
end ImbalancedChen.Part3.FiniteMeasureCauchyParameterIntegral20261026b

