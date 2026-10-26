import ImbalancedChen.Part3PrimeCentralFourierFunctional
import Mathlib.Analysis.Complex.Schwarz

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Honest parameter domination of the actual full-level completed Fourier
family, uniformly in every real horizontal coordinate. The actual K-strip
majorant bounds the nonconstant series, while the correctly regularized
constant is bounded on the fixed closed disk |s-1/2|<=1/4. Schwarz estimates
on inner disks then bound the actual parameter derivative uniformly for
|s-1/2|<1/8. No derivative-majorant, Fourier reconstruction or asymptotic
bound is supplied as a premise. This is the missing analytic primitive for
passing the central derivative through the original Fourier integral.
-/

noncomputable section
open Set Complex Metric
open scoped Topology
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinMeromorphic20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

namespace ImbalancedChen.Part3.CompletedCentralParameterDomination20261026b

theorem quarter_disk_re_bounds {s : ℂ} (hs : s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 3 / 4 := by
  have hn : ‖s - (1 / 2 : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hr := (Complex.abs_re_le_norm (s - (1 / 2 : ℂ))).trans hn
  norm_num [Complex.sub_re] at hr
  constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2]

theorem quarter_disk_avoids_poles {s : ℂ}
    (hs : s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ)) : s ≠ 0 ∧ s ≠ 1 := by
  have hr := quarter_disk_re_bounds hs
  constructor
  · intro he
    subst s
    norm_num at hr
  · intro he
    subst s
    norm_num at hr

/-- Constant-term continuity is derived from the actual completed Fourier
expression and the already entire actual nonzero K sum. -/
theorem completedConstant_differentiableAt {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (completedConstant y) s := by
  have he : completedConstant y = (fun w : ℂ => completedEisensteinFourier w y 0 -
      (2 : ℂ) * (Real.sqrt y : ℂ) * ∑' n, nonzeroFrequencyPair n w y 0) := by
    funext w
    unfold completedEisensteinFourier
    ring
  rw [he]
  exact (completedEisensteinFourier_analyticAt hy 0 hs0 hs1).differentiableAt.sub
    ((nonzeroFrequencyPair_sum_differentiable hy 0).differentiableAt.const_mul _)

/-- An actual uniform value bound on a genuine parameter disk. The height
is fixed and positive; every real horizontal point is covered. -/
theorem exists_completedFourier_center_value_bound (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ), ∀ x : ℝ,
      ‖completedEisensteinFourier s y x‖ ≤ C := by
  have hc : ContinuousOn (completedConstant y) (closedBall (1 / 2 : ℂ) (1 / 4 : ℝ)) := by
    intro s hs
    exact (completedConstant_differentiableAt hy (quarter_disk_avoids_poles hs).1
      (quarter_disk_avoids_poles hs).2).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 / 2 : ℂ) (1 / 4 : ℝ)).exists_bound_of_continuousOn hc
  let U : ℕ → ℝ := fun n => 2 * majorant 1 y n
  have hU : Summable U := (majorant_summable 1 hy).const_mul 2
  have hUnonneg : ∀ n, 0 ≤ U n := by
    intro n
    exact (norm_nonneg (nonzeroFrequencyPair n (1 / 2 : ℂ) y 0)).trans
      (nonzeroFrequencyPair_norm_bound 1 hy n (by norm_num) le_rfl 0)
  have hmass : 0 ≤ ∑' n, U n := tsum_nonneg hUnonneg
  let C : ℝ := max B 0 + (2 * Real.sqrt y) * (∑' n, U n) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s hs x
  have hr : |s.re| ≤ (1 : ℝ) := by
    obtain ⟨hl, hu⟩ := quarter_disk_re_bounds hs
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum : ‖∑' n, nonzeroFrequencyPair n s y x‖ ≤ ∑' n, U n :=
    tsum_of_norm_bounded hU.hasSum (fun n => nonzeroFrequencyPair_norm_bound 1 hy n hr le_rfl x)
  have hfac : ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ = 2 * Real.sqrt y := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]
  calc
    ‖completedEisensteinFourier s y x‖ ≤ ‖completedConstant y s‖ +
        ‖(2 : ℂ) * (Real.sqrt y : ℂ)‖ * ‖∑' n, nonzeroFrequencyPair n s y x‖ := by
      unfold completedEisensteinFourier
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ max B 0 + (2 * Real.sqrt y) * (∑' n, U n) := by
      rw [hfac]
      exact add_le_add ((hB s hs).trans (le_max_left B 0))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ ≤ C := by dsimp [C]; linarith

/-- A single uniform bound for the ACTUAL parameter derivative, on a
neighborhood independent of every horizontal point. -/
theorem exists_completedFourier_center_derivative_bound (y : ℝ) (hy : 0 < y) :
    ∃ D : ℝ, 0 < D ∧ ∀ s ∈ ball (1 / 2 : ℂ) (1 / 8 : ℝ), ∀ x : ℝ,
      ‖deriv (fun w : ℂ => completedEisensteinFourier w y x) s‖ ≤ D := by
  obtain ⟨C, hCpos, hC⟩ := exists_completedFourier_center_value_bound y hy
  refine ⟨16 * C, by positivity, ?_⟩
  intro s hs x
  have hsQuarter : s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ) :=
    mem_closedBall.mpr (le_trans (mem_ball.mp hs).le (by norm_num))
  have hsub : ball s (1 / 8 : ℝ) ⊆ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ) := by
    intro w hw
    apply mem_closedBall.mpr
    have hdist := dist_triangle w s (1 / 2 : ℂ)
    have hw' := mem_ball.mp hw
    have hs' := mem_ball.mp hs
    linarith
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => completedEisensteinFourier w y x)
      (ball s (1 / 8 : ℝ)) := by
    intro w hw
    exact (completedEisensteinFourier_analyticAt hy x (quarter_disk_avoids_poles (hsub hw)).1
      (quarter_disk_avoids_poles (hsub hw)).2).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo (fun w : ℂ => completedEisensteinFourier w y x)
      (ball s (1 / 8 : ℝ)) (closedBall (completedEisensteinFourier s y x) (2 * C)) := by
    intro w hw
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hC w (hsub hw) x, hC s hsQuarter x])
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps (by norm_num : (0 : ℝ) < 1 / 8)
  convert h using 1 <;> ring

end ImbalancedChen.Part3.CompletedCentralParameterDomination20261026b
