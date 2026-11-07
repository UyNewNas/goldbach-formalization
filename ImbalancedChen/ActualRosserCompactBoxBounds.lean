import ImbalancedChen.ActualRosserLocalBoxThreshold
import ImbalancedChen.RosserContinuousSourceUniformity
import ImbalancedChen.CompactLocalThreshold

/-!
# Uniform box-side density bounds on compact parameter sets

Each center supplies an actual finite box family with a neighborhood and a
common target threshold. Continuity changes the factor at the center to
the factor at the varying residual. A finite subcover then supplies one
threshold on any compact subset of the legal parameter domain, including
the lower-sieve endpoint two. This uses local common thresholds, rather
than inferring uniform convergence from fixed-parameter convergence.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory

/-- One threshold for the box-side lower bound of the actual upper density
on an arbitrary compact set of pairs `(outer exponent, residual)`. -/
theorem exists_actualSmallRosserPlusDensity_compact_lower_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        suzukiContinuousUpperFactor p.2 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
              ((N : ℝ) ^ (p.2 * p.1)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) := by
  let P := fun (N : ℕ) (p : ℝ × ℝ) => Even N →
    ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
      suzukiContinuousUpperFactor p.2 - eta ≤
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ p.1)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => suzukiContinuousUpperFactor p.2) S :=
    continuousOn_suzukiContinuousUpperFactor.comp continuous_snd.continuousOn
      (fun p hp => (hparam p hp).2)
  have hlocal (p : ℝ × ℝ) (hp : p ∈ S) :
      ∃ n : ℕ, ∀ᶠ q in 𝓝[S] p, ∀ N : ℕ, n ≤ N → P N q := by
    obtain ⟨n, _hn, hbound⟩ := exists_actualSmallRosserPlusDensity_local_lower_threshold
      p.1 (hparam p hp).1 p.2 (hparam p hp).2 (eta / 2) (by linarith)
    have hnear := (hcont p hp).eventually
      (gt_mem_nhds (show suzukiContinuousUpperFactor p.2 <
        suzukiContinuousUpperFactor p.2 + eta / 2 by linarith))
    refine ⟨n, ?_⟩
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds, hnear] with q hq hnearq
    intro N hN hEven cap hcap
    have h := hq N hN hEven cap hcap
    linarith
  obtain ⟨N0, hN0, hbound⟩ := exists_uniform_threshold_on_compact_of_local S hS P hlocal
  exact ⟨N0, hN0, fun N hN hEven p hp cap hcap => hbound N hN p hp hEven cap hcap⟩

/-- The analogous compact upper bound for the actual lower density
retains all boundary points with residual equal to two. -/
theorem exists_actualSmallRosserMinusDensity_compact_upper_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) ≤
            suzukiContinuousLowerFactor p.2 + eta := by
  let P := fun (N : ℕ) (p : ℝ × ℝ) => Even N →
    ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
      actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
          ((N : ℝ) ^ (p.2 * p.1)) /
        actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) ≤
          suzukiContinuousLowerFactor p.2 + eta
  have hcont : ContinuousOn (fun p : ℝ × ℝ => suzukiContinuousLowerFactor p.2) S :=
    continuousOn_suzukiContinuousLowerFactor.comp continuous_snd.continuousOn
      (fun p hp => (hparam p hp).2)
  have hlocal (p : ℝ × ℝ) (hp : p ∈ S) :
      ∃ n : ℕ, ∀ᶠ q in 𝓝[S] p, ∀ N : ℕ, n ≤ N → P N q := by
    obtain ⟨n, _hn, hbound⟩ := exists_actualSmallRosserMinusDensity_local_upper_threshold
      p.1 (hparam p hp).1 p.2 (hparam p hp).2 (eta / 2) (by linarith)
    have hnear := (hcont p hp).eventually
      (lt_mem_nhds (show suzukiContinuousLowerFactor p.2 - eta / 2 <
        suzukiContinuousLowerFactor p.2 by linarith))
    refine ⟨n, ?_⟩
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds, hnear] with q hq hnearq
    intro N hN hEven cap hcap
    have h := hq N hN hEven cap hcap
    linarith
  obtain ⟨N0, hN0, hbound⟩ := exists_uniform_threshold_on_compact_of_local S hS P hlocal
  exact ⟨N0, hN0, fun N hN hEven p hp cap hcap => hbound N hN p hp hEven cap hcap⟩

end

end ImbalancedChen
