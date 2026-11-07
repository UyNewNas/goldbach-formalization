import ImbalancedChen.Part3ActualCompletedEnergyResolvent
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
The actual positive self-adjoint contraction R has (1-R)^n tending strongly
to zero. Real continuous functional calculus gives the explicit range-R
bound 1/(n+1); actual dense range and uniform contraction extend it to H.
No strong convergence, spectral measure or no-atom supplier is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualResolventSurvivalStrongLimit20261025a

noncomputable section

open Filter Topology Set
open scoped BigOperators
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

/-- The elementary bound is proved by summing n+1 terms of the same
geometric progression, including t=0 and t=1. -/
theorem mul_one_sub_pow_le_inv_succ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    t * (1 - t) ^ n ≤ 1 / ((n : ℝ) + 1) := by
  let s : ℝ := 1 - t
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hsum : ((n : ℝ) + 1) * (t * s ^ n) ≤ ∑ k ∈ Finset.range (n + 1), t * s ^ k := by
    calc
      _ = ∑ _k ∈ Finset.range (n + 1), t * s ^ n := by simp [Nat.cast_add, Nat.cast_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hs0 hs1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) ht0
  have hgeom := mul_neg_geom_sum s (n + 1)
  have hs : 1 - s = t := by dsimp [s]; ring
  rw [hs] at hgeom
  have hweighted : (∑ k ∈ Finset.range (n + 1), t * s ^ k) = 1 - s ^ (n + 1) := by
    rw [← Finset.mul_sum]
    exact hgeom
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  change t * s ^ n * ((n : ℝ) + 1) ≤ 1
  nlinarith [pow_nonneg hs0 (n + 1)]

def actualSurvival : HyperbolicL2 →L[ℂ] HyperbolicL2 := 1 - actualWeakResolvent

theorem actualResolvent_spectrum_mem_Icc {t : ℝ}
    (ht : t ∈ spectrum ℝ actualWeakResolvent) : t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨spectrum_nonneg_of_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive _).2 actualWeakResolvent_positive) ht, ?_⟩
  exact (Real.le_norm_self t).trans
    ((spectrum.norm_le_norm_of_mem ht).trans actualWeakResolvent_opNorm_le_one)

theorem cfc_actualSurvival :
    cfc (fun t : ℝ => 1 - t) actualWeakResolvent = actualSurvival := by
  rw [cfc_sub, cfc_const_one ℝ actualWeakResolvent actualWeakResolvent_selfAdjoint,
    cfc_id' ℝ actualWeakResolvent actualWeakResolvent_selfAdjoint]
  rfl

theorem cfc_actualSurvival_pow (n : ℕ) :
    cfc (fun t : ℝ => (1 - t) ^ n) actualWeakResolvent = actualSurvival ^ n := by
  rw [cfc_pow (fun t : ℝ => 1 - t) n actualWeakResolvent
    (ha := actualWeakResolvent_selfAdjoint), cfc_actualSurvival]

theorem cfc_actualSurvival_pow_mul_resolvent (n : ℕ) :
    cfc (fun t : ℝ => (1 - t) ^ n * t) actualWeakResolvent =
      actualSurvival ^ n * actualWeakResolvent := by
  rw [cfc_mul, cfc_actualSurvival_pow,
    cfc_id' ℝ actualWeakResolvent actualWeakResolvent_selfAdjoint]

/-- Uniform contraction is supplied by the actual spectrum, for every
power including n=0, rather than by a convergence hypothesis. -/
theorem actualSurvival_pow_opNorm_le_one (n : ℕ) : ‖actualSurvival ^ n‖ ≤ 1 := by
  rw [← cfc_actualSurvival_pow]
  apply norm_cfc_le zero_le_one
  intro t ht
  have h := actualResolvent_spectrum_mem_Icc ht
  have h0 : 0 ≤ 1 - t := sub_nonneg.mpr h.2
  have h1 : 1 - t ≤ 1 := by linarith [h.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 n)]
  exact pow_le_one₀ h0 h1

/-- The actual range-R operator bound comes from a proved scalar CFC
bound on the actual spectrum [0,1]. -/
theorem actualSurvival_pow_mul_resolvent_opNorm_le (n : ℕ) :
    ‖actualSurvival ^ n * actualWeakResolvent‖ ≤ 1 / ((n : ℝ) + 1) := by
  rw [← cfc_actualSurvival_pow_mul_resolvent]
  apply norm_cfc_le (by positivity)
  intro t ht
  have h := actualResolvent_spectrum_mem_Icc ht
  have h0 : 0 ≤ 1 - t := sub_nonneg.mpr h.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg h0 n) h.1)]
  simpa only [mul_comm] using mul_one_sub_pow_le_inv_succ h.1 h.2 n

theorem actualSurvival_pow_norm_le (n : ℕ) (f : HyperbolicL2) :
    ‖(actualSurvival ^ n) f‖ ≤ ‖f‖ := by
  exact ((actualSurvival ^ n).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (actualSurvival_pow_opNorm_le_one n) (norm_nonneg f))

theorem actualSurvival_pow_on_range_norm_le (n : ℕ) (f : HyperbolicL2) :
    ‖(actualSurvival ^ n) (actualWeakResolvent f)‖ ≤
      (1 / ((n : ℝ) + 1)) * ‖f‖ := by
  exact ((actualSurvival ^ n * actualWeakResolvent).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (actualSurvival_pow_mul_resolvent_opNorm_le n) (norm_nonneg f))

/-- The actual range of R has strong decay with the explicit finite
bound above; no scalar spectral measure is needed for this step. -/
theorem tendsto_actualSurvival_pow_on_range (f : HyperbolicL2) :
    Tendsto (fun n : ℕ => (actualSurvival ^ n) (actualWeakResolvent f)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hb : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * ‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => actualSurvival_pow_on_range_norm_le n f) hb

/-- Actual dense range and the proved uniform contraction extend decay
to every actual canonical Hilbert-space vector. -/
theorem tendsto_actualSurvival_pow (f : HyperbolicL2) :
    Tendsto (fun n : ℕ => (actualSurvival ^ n) f) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  obtain ⟨y, hy, hnear⟩ := actualWeakResolvent_denseRange.exists_dist_lt f
    (show 0 < epsilon / 2 by positivity)
  obtain ⟨g, rfl⟩ := hy
  have hdiff : ‖f - actualWeakResolvent g‖ < epsilon / 2 := by
    simpa only [dist_eq_norm] using hnear
  have hnorm : Tendsto (fun n : ℕ => ‖(actualSurvival ^ n) (actualWeakResolvent g)‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (tendsto_actualSurvival_pow_on_range g).norm
  have hrange : ∀ᶠ n : ℕ in atTop,
      ‖(actualSurvival ^ n) (actualWeakResolvent g)‖ < epsilon / 2 :=
    hnorm.eventually
      (gt_mem_nhds (show (0 : ℝ) < epsilon / 2 by positivity))
  filter_upwards [hrange] with n hn
  rw [dist_zero_right]
  have hsplit : (actualSurvival ^ n) f =
      (actualSurvival ^ n) (f - actualWeakResolvent g) +
        (actualSurvival ^ n) (actualWeakResolvent g) := by rw [map_sub, sub_add_cancel]
  calc
    ‖(actualSurvival ^ n) f‖ ≤ ‖(actualSurvival ^ n) (f - actualWeakResolvent g)‖ +
        ‖(actualSurvival ^ n) (actualWeakResolvent g)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ ‖f - actualWeakResolvent g‖ +
        ‖(actualSurvival ^ n) (actualWeakResolvent g)‖ :=
      add_le_add_right (actualSurvival_pow_norm_le n _) _
    _ < epsilon := by linarith

end

end ImbalancedChen.Part3.ActualResolventSurvivalStrongLimit20261025a
