import ImbalancedChen.Part3FiniteMeasureCauchyParameterIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
Second parameter differentiation of the ORIGINAL finite-measure integral.
The first jet is bounded by the genuine Cauchy estimate and is measurable
by actual slopes. Repeating the same argument for the locally holomorphic
actual first jet proves measurability and L1 of the second jet. The first
integral derivative is identified on a genuine neighborhood before it is
differentiated. No second-jet measurability or bound is an input.
-/
namespace ImbalancedChen.Part3.FiniteMeasureSecondCauchyIntegral20261026b
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ImbalancedChen.Part3.FiniteMeasureCauchyParameterIntegral20261026b

/-- A nested ACTUAL Cauchy estimate, with explicit radii and constant. -/
theorem disk_second_derivative_bound (f : ℂ → ℂ) {u : ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 < C)
    (ha : ∀ v ∈ ball u R, AnalyticAt ℂ f v)
    (hb : ∀ v ∈ ball u R, ‖f v‖ ≤ C) {v : ℂ} (hv : v ∈ ball u (R / 4)) :
    ‖deriv (deriv f) v‖ ≤ 32 * C / R ^ 2 := by
  have hsub : ball u (R / 2) ⊆ ball u R := by
    intro w hw
    apply mem_ball.mpr
    linarith [mem_ball.mp hw]
  have hfirst : ∀ w ∈ ball u (R / 2), ‖deriv f w‖ ≤ 4 * C / R :=
    fun w hw => disk_derivative_bound f hR hC (fun z hz => (ha z hz).differentiableAt) hb hw
  have h := disk_derivative_bound (deriv f) (half_pos hR) (by positivity : 0 < 4 * C / R)
    (fun w hw => (ha w (hsub hw)).deriv.differentiableAt) hfirst
    (show v ∈ ball u ((R / 2) / 2) by convert hv using 1 <;> ring)
  convert h using 1 <;> field_simp [hR.ne'] <;> ring

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Second differentiation under the ORIGINAL integral. Actual value
bounds and holomorphy supply both derivative levels; all jet L1 claims
are proved using the finite measure, Cauchy estimates and native DCT. -/
theorem hasDerivAt_deriv_original_integral_of_disk_bound (F : ℂ → X → ℂ)
    (u : ℂ) {R C : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hm : ∀ v, AEStronglyMeasurable (F v) μ)
    (ha : ∀ᵐ x ∂μ, ∀ v ∈ ball u R, AnalyticAt ℂ (fun w => F w x) v)
    (hb : ∀ᵐ x ∂μ, ∀ v ∈ ball u R, ‖F v x‖ ≤ C) :
    Integrable (fun x => deriv (deriv (fun v => F v x)) u) μ ∧
      HasDerivAt (deriv (fun v => ∫ x, F v x ∂μ))
        (∫ x, deriv (deriv (fun v => F v x)) u ∂μ) u := by
  let G : ℂ → X → ℂ := fun v x => if v ∈ ball u R then deriv (fun w => F w x) v else 0
  have hmG : ∀ v, AEStronglyMeasurable (G v) μ := by
    intro v
    by_cases hv : v ∈ ball u R
    · simp only [G, if_pos hv]
      exact actual_parameter_derivative_aestronglyMeasurable F v hm
        (ha.mono (fun x hx => (hx v hv).differentiableAt))
    · simpa only [G, if_neg hv] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : X => (0 : ℂ)) μ)
  have hhalf : ball u (R / 2) ⊆ ball u R := by
    intro v hv
    apply mem_ball.mpr
    linarith [mem_ball.mp hv]
  have hGeq (x : X) {v : ℂ} (hv : v ∈ ball u R) :
      (fun w => G w x) =ᶠ[𝓝 v] deriv (fun w => F w x) := by
    filter_upwards [isOpen_ball.mem_nhds hv] with w hw
    simp only [G, if_pos hw]
  have hdG : ∀ᵐ x ∂μ, ∀ v ∈ ball u (R / 2), DifferentiableAt ℂ (fun w => G w x) v := by
    filter_upwards [ha] with x hx
    intro v hv
    exact ((hx v (hhalf hv)).deriv.differentiableAt).congr_of_eventuallyEq
      (hGeq x (hhalf hv))
  have hbG : ∀ᵐ x ∂μ, ∀ v ∈ ball u (R / 2), ‖G v x‖ ≤ 4 * C / R := by
    filter_upwards [ha, hb] with x hx hbx
    intro v hv
    simp only [G, if_pos (hhalf hv)]
    exact disk_derivative_bound (fun w => F w x) hR hC
      (fun w hw => (hx w hw).differentiableAt) hbx hv
  have hG := hasDerivAt_original_integral_of_disk_bound (μ := μ) G u
    (half_pos hR) (by positivity : 0 < 4 * C / R) hmG hdG hbG
  have hjet : (fun x => deriv (fun v => G v x) u) =
      (fun x => deriv (deriv (fun v => F v x)) u) := by
    funext x
    exact (hGeq x (mem_ball_self hR)).deriv_eq
  rw [hjet] at hG
  have hnear : deriv (fun v => ∫ x, F v x ∂μ) =ᶠ[𝓝 u] (fun v => ∫ x, G v x ∂μ) := by
    filter_upwards [ball_mem_nhds u (half_pos hR)] with v hv
    have hsub : ball v (R / 2) ⊆ ball u R := by
      intro w hw
      apply mem_ball.mpr
      have ht := dist_triangle w v u
      linarith [mem_ball.mp hv, mem_ball.mp hw]
    have hav : ∀ᵐ x ∂μ, ∀ w ∈ ball v (R / 2), DifferentiableAt ℂ (fun z => F z x) w :=
      ha.mono (fun x hx w hw => (hx w (hsub hw)).differentiableAt)
    have hbv : ∀ᵐ x ∂μ, ∀ w ∈ ball v (R / 2), ‖F w x‖ ≤ C :=
      hb.mono (fun x hx w hw => hx w (hsub hw))
    have hvD := (hasDerivAt_original_integral_of_disk_bound (μ := μ) F v
      (half_pos hR) hC hm hav hbv).2.deriv
    simpa only [G, if_pos (hhalf hv)] using hvD
  exact ⟨hG.1, hG.2.congr_of_eventuallyEq hnear⟩

end
end ImbalancedChen.Part3.FiniteMeasureSecondCauchyIntegral20261026b
