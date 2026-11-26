import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite nonnegative weighted sums under uniformly small perturbations

This mathlib-only module separates a finite perturbation estimate, the
eventually bounded total-mass premise, and compact uniform continuity.
The index filter, finite supports, and nonnegative weights are arbitrary.
The test function is fixed and may have either sign. No prime-distribution
or sieve theorem is assumed or proved.

Held source candidate: local Lean/Lake execution is unavailable. Compilation,
kernel replay, and the transitive axiom audit remain pending.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology
open scoped BigOperators

/-- A uniform summand error costs the total nonnegative weight, not the
number of labels. Zero weights and the empty support are allowed. -/
theorem abs_nonneg_weighted_sum_sub_le {ι : Type*}
    (T : Finset ι) (w f g : ι → ℝ) (delta : ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i)
    (hfg : ∀ i ∈ T, |f i - g i| ≤ delta) :
    |(∑ i ∈ T, w i * f i) - ∑ i ∈ T, w i * g i| ≤
      delta * ∑ i ∈ T, w i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ T, |w i * f i - w i * g i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ T, delta * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
      calc
        w i * |f i - g i| ≤ w i * delta :=
          mul_le_mul_of_nonneg_left (hfg i hi) (hw i hi)
        _ = delta * w i := mul_comm _ _
    _ = delta * ∑ i ∈ T, w i := by rw [Finset.mul_sum]

/-- Uniformly vanishing errors can be summed against an eventually bounded
nonnegative mass. Both the mass bound and the uniformity are explicit. -/
theorem tendsto_nonneg_weighted_sum_sub_zero_of_uniform
    {κ ι : Type*} {l : Filter κ}
    (T : κ → Finset ι) (w f g : κ → ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hw : ∀ᶠ n in l, ∀ i ∈ T n, 0 ≤ w n i)
    (hmass : ∀ᶠ n in l, (∑ i ∈ T n, w n i) ≤ M)
    (hfg : ∀ epsilon > 0, ∀ᶠ n in l,
      ∀ i ∈ T n, |f n i - g n i| < epsilon) :
    Tendsto (fun n =>
      (∑ i ∈ T n, w n i * f n i) - ∑ i ∈ T n, w n i * g n i)
      l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hden : 0 < M + 1 := by linarith
  have hdelta : 0 < epsilon / (M + 1) := div_pos hepsilon hden
  filter_upwards [hw, hmass, hfg (epsilon / (M + 1)) hdelta]
    with n hnw hnm hnf
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ (epsilon / (M + 1)) * ∑ i ∈ T n, w n i :=
      abs_nonneg_weighted_sum_sub_le (T n) (w n) (f n) (g n)
        (epsilon / (M + 1)) hnw (fun i hi => (hnf i hi).le)
    _ ≤ (epsilon / (M + 1)) * M :=
      mul_le_mul_of_nonneg_left hnm hdelta.le
    _ < (epsilon / (M + 1)) * (M + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hdelta
    _ = epsilon := div_mul_cancel₀ _ hden.ne'

/-- Continuity on one fixed compact set supplies a common modulus for all
selected labels. Both coordinates must lie in that set eventually. -/
theorem eventually_uniform_comp_close_of_compact
    {κ ι : Type*} {l : Filter κ}
    (T : κ → Finset ι) (x y : κ → ι → ℝ)
    (K : Set ℝ) (F : ℝ → ℝ)
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hmem : ∀ᶠ n in l, ∀ i ∈ T n, x n i ∈ K ∧ y n i ∈ K)
    (hxy : ∀ delta > 0, ∀ᶠ n in l,
      ∀ i ∈ T n, |x n i - y n i| < delta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in l, ∀ i ∈ T n, |F (x n i) - F (y n i)| < epsilon := by
  obtain ⟨delta, hdelta, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hF) epsilon hepsilon
  filter_upwards [hmem, hxy delta hdelta] with n hnm hne
  intro i hi
  have hdist : dist (x n i) (y n i) < delta := by
    simpa only [Real.dist_eq] using hne i hi
  simpa only [Real.dist_eq] using
    hmod (x n i) (hnm i hi).1 (y n i) (hnm i hi).2 hdist

/-- Compact continuity transports uniformly close coordinates through a
fixed continuous test before summing against a bounded nonnegative mass. -/
theorem tendsto_nonneg_weighted_comp_sub_zero_of_compact
    {κ ι : Type*} {l : Filter κ}
    (T : κ → Finset ι) (w x y : κ → ι → ℝ)
    (K : Set ℝ) (F : ℝ → ℝ) (M : ℝ)
    (hK : IsCompact K) (hF : ContinuousOn F K) (hM : 0 ≤ M)
    (hw : ∀ᶠ n in l, ∀ i ∈ T n, 0 ≤ w n i)
    (hmass : ∀ᶠ n in l, (∑ i ∈ T n, w n i) ≤ M)
    (hmem : ∀ᶠ n in l, ∀ i ∈ T n, x n i ∈ K ∧ y n i ∈ K)
    (hxy : ∀ delta > 0, ∀ᶠ n in l,
      ∀ i ∈ T n, |x n i - y n i| < delta) :
    Tendsto (fun n =>
      (∑ i ∈ T n, w n i * F (x n i)) -
        ∑ i ∈ T n, w n i * F (y n i)) l (𝓝 0) := by
  apply tendsto_nonneg_weighted_sum_sub_zero_of_uniform T w
    (fun n i => F (x n i)) (fun n i => F (y n i)) M hM hw hmass
  exact eventually_uniform_comp_close_of_compact T x y K F hK hF hmem hxy

/-- A fixed-profile limit transfers to the moving profile. The fixed-profile
limit is retained as a separate, visibly analytic premise. -/
theorem tendsto_nonneg_weighted_comp_of_compact
    {κ ι : Type*} {l : Filter κ}
    (T : κ → Finset ι) (w x y : κ → ι → ℝ)
    (K : Set ℝ) (F : ℝ → ℝ) (M L : ℝ)
    (hK : IsCompact K) (hF : ContinuousOn F K) (hM : 0 ≤ M)
    (hw : ∀ᶠ n in l, ∀ i ∈ T n, 0 ≤ w n i)
    (hmass : ∀ᶠ n in l, (∑ i ∈ T n, w n i) ≤ M)
    (hmem : ∀ᶠ n in l, ∀ i ∈ T n, x n i ∈ K ∧ y n i ∈ K)
    (hxy : ∀ delta > 0, ∀ᶠ n in l,
      ∀ i ∈ T n, |x n i - y n i| < delta)
    (hfixed : Tendsto (fun n => ∑ i ∈ T n, w n i * F (y n i)) l (𝓝 L)) :
    Tendsto (fun n => ∑ i ∈ T n, w n i * F (x n i)) l (𝓝 L) := by
  have herror := tendsto_nonneg_weighted_comp_sub_zero_of_compact
    T w x y K F M hK hF hM hw hmass hmem hxy
  simpa only [sub_add_cancel, zero_add] using herror.add hfixed

/-- An independently proved total-mass limit supplies the bounded-mass
premise above. This implication contains no arithmetic input of its own. -/
theorem exists_eventually_bounded_mass_of_tendsto
    {κ : Type*} {l : Filter κ} {mass : κ → ℝ} {L : ℝ}
    (hlimit : Tendsto mass l (𝓝 L)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in l, mass n ≤ M := by
  refine ⟨max L 0 + 1, by positivity, ?_⟩
  have hL : L < max L 0 + 1 := by linarith [le_max_left L 0]
  filter_upwards [hlimit.eventually (gt_mem_nhds hL)] with n hn
  exact hn.le

end

end ImbalancedChen
