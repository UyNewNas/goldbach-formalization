import ImbalancedChen.Part3PlanarFrechetCompactGreen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An explicit real separated cutoff for a closed rectangle and a positive
margin. Its support lies strictly inside the expanded rectangle; its
derivative budget is a proved finite number, fixed before smoothing.
-/

namespace ImbalancedChen.Part3.NestedRectangleRealCutoff20261026b
noncomputable section
open Set Function MeasureTheory
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a

def intervalBump (L R δ : ℝ) (hLR : L ≤ R) (hδ : 0 < δ) :
    ContDiffBump ((L + R) / 2) where
  rIn := (R - L) / 2 + δ / 3
  rOut := (R - L) / 2 + 2 * δ / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem intervalBump_one {L R δ : ℝ} (hLR : L ≤ R) (hδ : 0 < δ)
    {x : ℝ} (hx : x ∈ Icc L R) : intervalBump L R δ hLR hδ x = 1 := by
  apply (intervalBump L R δ hLR hδ).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -((R - L) / 2 + δ / 3) ≤ x - (L + R) / 2 ∧
    x - (L + R) / 2 ≤ (R - L) / 2 + δ / 3
  constructor <;> linarith [hx.1, hx.2]

theorem intervalBump_support {L R δ : ℝ} (hLR : L ≤ R) (hδ : 0 < δ) :
    tsupport (intervalBump L R δ hLR hδ) ⊆ Ioo (L - δ) (R + δ) := by
  intro x hx
  rw [(intervalBump L R δ hLR hδ).tsupport_eq, Metric.mem_closedBall,
    Real.dist_eq, abs_le] at hx
  change -((R - L) / 2 + 2 * δ / 3) ≤ x - (L + R) / 2 ∧
    x - (L + R) / 2 ≤ (R - L) / 2 + 2 * δ / 3 at hx
  constructor <;> linarith [hx.1, hx.2]

def rectangleCutoff (L R a b δ : ℝ) (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ)
    (p : Plane) : ℝ :=
  intervalBump L R δ hLR hδ p.1 * intervalBump a b δ hab hδ p.2

theorem rectangleCutoff_smooth (L R a b δ : ℝ)
    (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (rectangleCutoff L R a b δ hLR hab hδ) :=
  ((intervalBump L R δ hLR hδ).contDiff.comp contDiff_fst).mul
    ((intervalBump a b δ hab hδ).contDiff.comp contDiff_snd)

theorem rectangleCutoff_compact (L R a b δ : ℝ)
    (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ) :
    HasCompactSupport (rectangleCutoff L R a b δ hLR hab hδ) := by
  apply HasCompactSupport.intro
    ((intervalBump L R δ hLR hδ).hasCompactSupport.prod
      (intervalBump a b δ hab hδ).hasCompactSupport)
  intro p hp
  by_cases hx : p.1 ∈ tsupport (intervalBump L R δ hLR hδ)
  · have hy : p.2 ∉ tsupport (intervalBump a b δ hab hδ) := fun h => hp ⟨hx, h⟩
    simp [rectangleCutoff, image_eq_zero_of_notMem_tsupport hy]
  · simp [rectangleCutoff, image_eq_zero_of_notMem_tsupport hx]

theorem rectangleCutoff_one (L R a b δ : ℝ)
    (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ)
    {p : Plane} (hp : p ∈ Icc L R ×ˢ Icc a b) :
    rectangleCutoff L R a b δ hLR hab hδ p = 1 := by
  rw [rectangleCutoff, intervalBump_one hLR hδ hp.1, intervalBump_one hab hδ hp.2,
    one_mul]

theorem rectangleCutoff_range (L R a b δ : ℝ)
    (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ) (p : Plane) :
    0 ≤ rectangleCutoff L R a b δ hLR hab hδ p ∧
      rectangleCutoff L R a b δ hLR hab hδ p ≤ 1 := by
  constructor
  · exact mul_nonneg (intervalBump L R δ hLR hδ).nonneg
      (intervalBump a b δ hab hδ).nonneg
  · exact mul_le_one₀ (intervalBump L R δ hLR hδ).le_one
      (intervalBump a b δ hab hδ).nonneg (intervalBump a b δ hab hδ).le_one

theorem rectangleCutoff_support (L R a b δ : ℝ)
    (hLR : L ≤ R) (hab : a ≤ b) (hδ : 0 < δ) :
    tsupport (rectangleCutoff L R a b δ hLR hab hδ) ⊆
      Ioo (L - δ) (R + δ) ×ˢ Ioo (a - δ) (b + δ) := by
  have hclosed : IsClosed (tsupport (intervalBump L R δ hLR hδ) ×ˢ
      tsupport (intervalBump a b δ hab hδ)) := isClosed_tsupport.prod isClosed_tsupport
  have hs : tsupport (rectangleCutoff L R a b δ hLR hab hδ) ⊆
      tsupport (intervalBump L R δ hLR hδ) ×ˢ tsupport (intervalBump a b δ hab hδ) := by
    apply closure_minimal _ hclosed
    intro p hp
    constructor
    · apply subset_closure
      intro hx
      exact hp (by simp [rectangleCutoff, hx])
    · apply subset_closure
      intro hy
      exact hp (by simp [rectangleCutoff, hy])
  intro p hp
  exact ⟨intervalBump_support hLR hδ (hs hp).1,
    intervalBump_support hab hδ (hs hp).2⟩

def cutoffGradientSq (θ : Plane → ℝ) (p : Plane) : ℝ :=
  directional xDirection θ p ^ 2 + directional yDirection θ p ^ 2

theorem cutoffGradientSq_nonneg (θ : Plane → ℝ) (p : Plane) :
    0 ≤ cutoffGradientSq θ p := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem cutoffGradientSq_continuous {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    Continuous (cutoffGradientSq θ) :=
  ((directional_cinfty hθ xDirection).continuous.pow 2).add
    ((directional_cinfty hθ yDirection).continuous.pow 2)

theorem cutoffGradientSq_compact {θ : Plane → ℝ} (hc : HasCompactSupport θ) :
    HasCompactSupport (cutoffGradientSq θ) := by
  have hx := (directional_hasCompactSupport hc xDirection).mul_right
    (f' := directional xDirection θ)
  have hy := (directional_hasCompactSupport hc yDirection).mul_right
    (f' := directional yDirection θ)
  simpa only [cutoffGradientSq, pow_two] using hx.add hy

/-- This number depends on the fixed cutoff and never on mollifier scale. -/
theorem exists_cutoff_gradient_budget {θ : Plane → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p, cutoffGradientSq θ p ≤ D := by
  obtain ⟨C, hC⟩ := (cutoffGradientSq_compact hc).exists_bound_of_continuous
    (cutoffGradientSq_continuous hθ)
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  exact (le_abs_self _).trans ((hC p).trans (le_max_left _ _))

theorem weightedDerivative_memLp {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hU : ContDiff ℝ ∞ U) (v : Plane) :
    MemLp (fun p => (θ p : ℂ) * directional v U p) 2 volume :=
  ((Complex.continuous_ofReal.comp hθ.continuous).mul
    (directional_cinfty hU v).continuous).memLp_of_hasCompactSupport
      ((hc.comp_left (g := Complex.ofReal) rfl).mul_right)

end
end ImbalancedChen.Part3.NestedRectangleRealCutoff20261026b
