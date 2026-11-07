import ImbalancedChen.Part3HilbertBoundedWeakSubsequence
import ImbalancedChen.Part3NestedRectangleRealCutoff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The compact cutoff controls global L2 representatives of both gradients.
Their Hilbert subsequence is actually extracted; native first-order Green
and strong convergence of the values identify the limit on the set where
the cutoff is one, against every compact smooth test supported there. -/

namespace ImbalancedChen.Part3.PlanarLocalWeakGradientExtraction20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a
open PlanarFrechetCompactGreen20261026b NestedRectangleRealCutoff20261026b
open HilbertBoundedWeakSubsequence20261026b

abbrev PlaneL2 := Lp ℂ 2 (volume : Measure Plane)

instance planeL2_secondCountable : SecondCountableTopology PlaneL2 := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- Literal distributional local H1: both derivatives have L2 extensions
to the plane, and all smooth compact tests supported in Ω are legal. -/
def HasLocalL2GradientOn (Ω : Set Plane) (F : Plane → ℂ) : Prop :=
  MemLp F 2 volume ∧ ∃ gx gy : PlaneL2, ∀ ψ : Plane → ℂ,
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p : Plane, star (ψ p) * gx p) =
        -(∫ p : Plane, star (directional xDirection ψ p) * F p)) ∧
      ((∫ p : Plane, star (ψ p) * gy p) =
        -(∫ p : Plane, star (directional yDirection ψ p) * F p))

theorem inner_toLp_integral {P Q : Plane → ℂ}
    (hP : MemLp P 2 volume) (hQ : MemLp Q 2 volume) :
    inner ℂ (hP.toLp P) (hQ.toLp Q) = ∫ p, star (P p) * Q p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hP.coeFn_toLp, hQ.coeFn_toLp] with p hp hq
  rw [hp, hq]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem inner_toLp_Lp_integral {P : Plane → ℂ}
    (hP : MemLp P 2 volume) (g : PlaneL2) :
    inner ℂ (hP.toLp P) g = ∫ p, star (P p) * g p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hP.coeFn_toLp] with p hp
  rw [hp]
  simp only [RCLike.inner_apply', Complex.star_def]

def weightedGradientL2 {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hU : ContDiff ℝ ∞ U) (v : Plane) : PlaneL2 :=
  (weightedDerivative_memLp hθ hc hU v).toLp
    (fun p => (θ p : ℂ) * directional v U p)

theorem weightedGradient_green {θ : Plane → ℝ} {U ψ : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 volume)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hone : ∀ p ∈ tsupport ψ, θ p = 1) (v : Plane) :
    inner ℂ ((hψ.continuous.memLp_of_hasCompactSupport hψc).toLp ψ)
      (weightedGradientL2 hθ hc hU v) =
      -inner ℂ (((directional_cinfty hψ v).continuous.memLp_of_hasCompactSupport
        (directional_hasCompactSupport hψc v)).toLp (directional v ψ)) (hU2.toLp U) := by
  rw [weightedGradientL2, inner_toLp_integral, inner_toLp_integral]
  calc
    _ = ∫ p : Plane, star (ψ p) * directional v U p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        by_cases hp : p ∈ tsupport ψ
        · rw [hone p hp]; simp
        · simp [image_eq_zero_of_notMem_tsupport hp]
    _ = _ := compact_first_green hψc hψ hU v

/-- Primitive analytic extraction theorem. The only bounds concern
the known smooth approximants; neither a weak limit nor H1 is assumed. -/
theorem local_gradient_of_smooth_L2_approximation
    (F : Plane → ℂ) (hF : MemLp F 2 volume)
    (U : ℕ → Plane → ℂ) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hU2 : ∀ n, MemLp (U n) 2 volume)
    (hvalue : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hF.toLp F)))
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (C : ℝ) (hC : 0 ≤ C)
    (henergy : ∀ n,
      ‖weightedGradientL2 hθ hc (hU n) xDirection‖^2 +
        ‖weightedGradientL2 hθ hc (hU n) yDirection‖^2 ≤ C)
    (Ω : Set Plane) (hone : ∀ p ∈ Ω, θ p = 1) :
    HasLocalL2GradientOn Ω F := by
  let X n := weightedGradientL2 hθ hc (hU n) xDirection
  let Y n := weightedGradientL2 hθ hc (hU n) yDirection
  have hx (n : ℕ) : ‖X n‖ ≤ C + 1 := by
    have h := henergy n
    change ‖X n‖^2 + ‖Y n‖^2 ≤ C at h
    nlinarith [sq_nonneg ‖Y n‖, sq_nonneg (‖X n‖ - 1), norm_nonneg (X n)]
  have hy (n : ℕ) : ‖Y n‖ ≤ C + 1 := by
    have h := henergy n
    change ‖X n‖^2 + ‖Y n‖^2 ≤ C at h
    nlinarith [sq_nonneg ‖X n‖, sq_nonneg (‖Y n‖ - 1), norm_nonneg (Y n)]
  obtain ⟨gx, gy, _, _, σ, hσ, hxl, hyl⟩ :=
    exists_two_bounded_weak_subsequences X Y (C + 1) hx hy
  refine ⟨hF, gx, gy, fun ψ hψ hψc hψΩ => ?_⟩
  have honeψ : ∀ p ∈ tsupport ψ, θ p = 1 := fun p hp => hone p (hψΩ hp)
  have hψ2 := hψ.continuous.memLp_of_hasCompactSupport hψc (p := (2 : ℝ≥0∞))
  have hlim (v : Plane) (G : PlaneL2)
      (hg : Tendsto (fun n => inner ℂ (hψ2.toLp ψ)
        (weightedGradientL2 hθ hc (hU (σ n)) v)) atTop
          (𝓝 (inner ℂ (hψ2.toLp ψ) G))) :
      (∫ p : Plane, star (ψ p) * G p) =
        -(∫ p : Plane, star (directional v ψ p) * F p) := by
    let hd := (directional_cinfty hψ v).continuous.memLp_of_hasCompactSupport
      (directional_hasCompactSupport hψc v) (p := (2 : ℝ≥0∞))
    have hr := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => hd.toLp (directional v ψ))
      atTop (𝓝 (hd.toLp (directional v ψ)))).inner
        (hvalue.comp hσ.tendsto_atTop)).neg
    have heq : (fun n => inner ℂ (hψ2.toLp ψ)
        (weightedGradientL2 hθ hc (hU (σ n)) v)) =
      (fun n => -inner ℂ (hd.toLp (directional v ψ)) ((hU2 (σ n)).toLp (U (σ n)))) :=
      funext fun n => weightedGradient_green hθ hc (hU (σ n)) (hU2 (σ n))
        hψ hψc honeψ v
    rw [← heq] at hr
    have he := tendsto_nhds_unique hg hr
    rw [inner_toLp_Lp_integral, inner_toLp_integral] at he
    exact he
  exact ⟨hlim xDirection gx (hxl _), hlim yDirection gy (hyl _)⟩

end
end ImbalancedChen.Part3.PlanarLocalWeakGradientExtraction20261026b
