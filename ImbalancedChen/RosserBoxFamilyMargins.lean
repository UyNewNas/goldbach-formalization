import ImbalancedChen.RosserContinuousSourceUniformity

/-!
# Strict margins for fixed finite boundary-box families

Only finite inequalities and continuity occur here. Empty families are
allowed. The reference outer exponent can be chosen above any prescribed
floor below the center, and its change in the finite linear gain can be
made arbitrarily small before any target is chosen.
-/

namespace ImbalancedChen

open Filter Topology

/-- All finitely many strict lower and upper gates survive on one common
open interval about the central level exponent. -/
theorem exists_finite_strict_bounds_margin
    {ι κ : Type*} (L : Finset ι) (U : Finset κ)
    (lower : ι → ℝ) (upper : κ → ℝ) (beta0 : ℝ)
    (hlower : ∀ i ∈ L, lower i < beta0) (hupper : ∀ j ∈ U, beta0 < upper j) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ beta : ℝ, |beta - beta0| < delta →
      (∀ i ∈ L, lower i < beta) ∧ (∀ j ∈ U, beta < upper j) := by
  have hL : ∀ᶠ beta in 𝓝 beta0, ∀ i ∈ L, lower i < beta :=
    (eventually_all_finset L).mpr (fun i hi => lt_mem_nhds (hlower i hi))
  have hU : ∀ᶠ beta in 𝓝 beta0, ∀ j ∈ U, beta < upper j :=
    (eventually_all_finset U).mpr (fun j hj => gt_mem_nhds (hupper j hj))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp (hL.and hU)
  exact ⟨delta, hdelta, fun beta hbeta => hball (by simpa [Real.dist_eq] using hbeta)⟩

/-- Select an exponent strictly between all finite top endpoints and the
center, also above any preassigned floor. -/
theorem exists_finite_outer_reference
    {ι : Type*} (S : Finset ι) (top : ι → ℝ) (u_floor u0 : ℝ)
    (hu0 : 0 < u0) (hfloor : u_floor < u0) (htop : ∀ i ∈ S, top i < u0) :
    ∃ u_min : ℝ, 0 < u_min ∧ u_floor < u_min ∧ u_min < u0 ∧
      ∀ i ∈ S, top i < u_min := by
  have hT : ∀ᶠ u in 𝓝 u0, ∀ i ∈ S, top i < u :=
    (eventually_all_finset S).mpr (fun i hi => lt_mem_nhds (htop i hi))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    ((lt_mem_nhds hu0).and ((lt_mem_nhds hfloor).and hT))
  have hmem : u0 - delta / 2 ∈ Metric.ball u0 delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : u0 - delta / 2 - u0 = -(delta / 2) := by ring
    rw [heq, abs_neg, abs_of_pos (half_pos hdelta)]
    linarith
  obtain ⟨hpos, hfloor', ht⟩ := hball hmem
  exact ⟨u0 - delta / 2, hpos, hfloor', by linarith, ht⟩

/-- The same selection controls the finite gain lost by replacing the
central outer exponent by the fixed reference exponent. The gain may be
any real number; no sign assumption is used. -/
theorem exists_finite_outer_reference_with_gain
    {ι : Type*} (S : Finset ι) (top : ι → ℝ) (u_floor u0 gain eta : ℝ)
    (hu0 : 0 < u0) (hfloor : u_floor < u0) (htop : ∀ i ∈ S, top i < u0)
    (heta : 0 < eta) :
    ∃ u_min : ℝ, 0 < u_min ∧ u_floor < u_min ∧ u_min < u0 ∧
      (∀ i ∈ S, top i < u_min) ∧ |(u_min / u0) * gain - gain| < eta := by
  have hT : ∀ᶠ u in 𝓝 u0, ∀ i ∈ S, top i < u :=
    (eventually_all_finset S).mpr (fun i hi => lt_mem_nhds (htop i hi))
  have hlim : Tendsto (fun u : ℝ => (u / u0) * gain) (𝓝 u0) (𝓝 gain) := by
    have hc : Tendsto (fun u : ℝ => (u / u0) * gain) (𝓝 u0)
        (𝓝 ((u0 / u0) * gain)) := (continuousAt_id.div_const u0).mul_const gain
    simpa only [div_self (ne_of_gt hu0), one_mul] using hc
  have hgain : ∀ᶠ u in 𝓝 u0, |(u / u0) * gain - gain| < eta := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hlim) eta heta
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    ((lt_mem_nhds hu0).and ((lt_mem_nhds hfloor).and (hT.and hgain)))
  have hmem : u0 - delta / 2 ∈ Metric.ball u0 delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : u0 - delta / 2 - u0 = -(delta / 2) := by ring
    rw [heq, abs_neg, abs_of_pos (half_pos hdelta)]
    linarith
  obtain ⟨hpos, hfloor', ht, hg⟩ := hball hmem
  exact ⟨u0 - delta / 2, hpos, hfloor', by linarith, ht, hg⟩

/-- Pull a level-exponent interval back along `beta = s*u`, while keeping
the outer exponent above its fixed reference. Pairs are ordered `(u,s)`. -/
theorem eventually_product_parameter_margin (u0 s0 u_min delta : ℝ)
    (humin : u_min < u0) (hdelta : 0 < delta) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0),
      u_min < p.1 ∧ |p.2 * p.1 - s0 * u0| < delta := by
  have hu : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), u_min < p.1 :=
    continuous_fst.continuousAt.eventually (lt_mem_nhds humin)
  have hp : Tendsto (fun p : ℝ × ℝ => p.2 * p.1) (𝓝 (u0, s0)) (𝓝 (s0 * u0)) :=
    (continuous_snd.mul continuous_fst).continuousAt
  have hb : ∀ᶠ p : ℝ × ℝ in 𝓝 (u0, s0), |p.2 * p.1 - s0 * u0| < delta := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hp) delta hdelta
  exact hu.and hb

end ImbalancedChen
