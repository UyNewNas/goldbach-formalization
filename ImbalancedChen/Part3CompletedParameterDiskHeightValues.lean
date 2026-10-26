import ImbalancedChen.Part3CompletedCompactParameterHeightValues
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The actual completed family is bounded on closed parameter disks uniformly
on a compact positive height band, INCLUDING the removable central value.
Only the boundary circle is evaluated by the literal two-Lambda formula;
the genuine analytic continuation and maximum modulus principle carry the
bound through the interior. This supplies the Cauchy domination required
for differentiation over compact spatial regions.
-/
namespace ImbalancedChen.Part3.CompletedParameterDiskHeightValues20261026b
noncomputable section
open Set Complex Metric
open scoped Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3.CompletedCompactParameterHeightValues20261026b

/-- Central interior parameters are permitted. The genuine poles must be
outside the closed disk, and its boundary must avoid the removable point. -/
theorem exists_completedFourier_disk_height_bound (u : ℂ) {R a b : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hab : a ≤ b)
    (hpoles : ∀ s ∈ closedBall u R, s ≠ 0 ∧ s ≠ 1)
    (hcircle : ∀ s ∈ sphere u R, s ≠ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ closedBall u R, ∀ y ∈ Icc a b, ∀ x : ℝ,
      ‖completedEisensteinFourier s y x‖ ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_sphere u R).isBounded.exists_norm_le
  let M := Nat.ceil B
  have hM : ∀ s ∈ sphere u R, |s.re| ≤ (M : ℝ) := by
    intro s hs
    exact (Complex.abs_re_le_norm s).trans ((hB s hs).trans (Nat.le_ceil B))
  have hreg : ∀ s ∈ sphere u R, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 1 / 2 := by
    intro s hs
    have hp := hpoles s (sphere_subset_closedBall hs)
    exact ⟨hp.1, hp.2, hcircle s hs⟩
  obtain ⟨C, hC, hbound⟩ := exists_completedFourier_compact_height_bound
    (sphere u R) (isCompact_sphere u R) M hM ha hab hreg
  refine ⟨C, hC, ?_⟩
  intro s hs y hy x
  have hd : DifferentiableOn ℂ (fun w => completedEisensteinFourier w y x)
      (closedBall u R) := by
    intro w hw
    exact (completedEisensteinFourier_analyticAt (lt_of_lt_of_le ha hy.1) x
      (hpoles w hw).1 (hpoles w hw).2).differentiableAt.differentiableWithinAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball)
    (hd.diffContOnCl_ball Subset.rfl)
  · intro w hw
    rw [frontier_ball u hR.ne'] at hw
    exact hbound w hw y hy x
  · rwa [closure_ball u hR.ne']

/-- A concrete central disk, uniformly in the full positive height band
and in the horizontal coordinate. Its central value is the correctly
regularized completed family, rather than the raw pole expression. -/
theorem exists_completedFourier_center_height_bound {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ),
      ∀ y ∈ Icc a b, ∀ x : ℝ, ‖completedEisensteinFourier s y x‖ ≤ C := by
  apply exists_completedFourier_disk_height_bound (1 / 2 : ℂ) (by norm_num) ha hab
  · intro s hs
    have hn : ‖s - (1 / 2 : ℂ)‖ ≤ (1 / 4 : ℝ) := by
      simpa only [mem_closedBall, dist_eq_norm] using hs
    have hr := (Complex.abs_re_le_norm (s - (1 / 2 : ℂ))).trans hn
    norm_num [Complex.sub_re] at hr
    constructor <;> intro he <;> subst s <;> norm_num at hr
  · intro s hs he
    subst s
    norm_num [mem_sphere] at hs

end
end ImbalancedChen.Part3.CompletedParameterDiskHeightValues20261026b
