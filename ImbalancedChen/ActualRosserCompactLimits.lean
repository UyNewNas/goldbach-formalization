import ImbalancedChen.ActualRosserCompactAnalyticBounds
import ImbalancedChen.ActualRosserCompactBoxBounds
import ImbalancedChen.RosserCompactParameterBounds

/-!
# Two-sided actual Rosser density limits on compact parameter sets

The analytic all-depth estimate and the finite actual-box estimate bound
the same coefficient density divided by its own Euler product. Compact
coordinate bounds place the analytic side in one fixed rectangle, while
the box side uses proved local neighborhoods and a finite subcover. The
result is uniform in both parameters and every covering enumeration cap.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory

theorem exists_actualSmallRosserPlusDensity_compact_upper_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) ≤
            suzukiContinuousUpperFactor p.2 + eta := by
  obtain ⟨a, _b, ha, hu⟩ := exists_compact_positive_first_coordinate_bounds S hS
    (fun p hp => (hparam p hp).1)
  obtain ⟨sigma, B, hsigma, hs⟩ := exists_compact_strict_second_coordinate_bounds S hS 1
    (fun p hp => (hparam p hp).2)
  obtain ⟨N0, hN0, hbound⟩ := exists_actualSmallRosserPlusDensity_rectangle_upper_threshold
    a ha sigma hsigma B eta heta
  exact ⟨N0, hN0, fun N hN hEven p hp cap hcap =>
    hbound N hN hEven p.1 (hu p hp).1 p.2 (hs p hp).1 (hs p hp).2 cap hcap⟩

theorem exists_actualSmallRosserMinusDensity_compact_lower_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        suzukiContinuousLowerFactor p.2 - eta ≤
          actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
              ((N : ℝ) ^ (p.2 * p.1)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) := by
  obtain ⟨a, _b, ha, hu⟩ := exists_compact_positive_first_coordinate_bounds S hS
    (fun p hp => (hparam p hp).1)
  obtain ⟨B, hB⟩ := hS.bddAbove_image continuous_snd.continuousOn
  obtain ⟨N0, hN0, hbound⟩ := exists_actualSmallRosserMinusDensity_rectangle_lower_threshold
    a ha 2 (by norm_num) B eta heta
  exact ⟨N0, hN0, fun N hN hEven p hp cap hcap =>
    hbound N hN hEven p.1 (hu p hp).1 p.2 (hparam p hp).2
      (hB (Set.mem_image_of_mem _ hp)) cap hcap⟩

/-- The actual upper ratio has one two-sided threshold on every legal compact
set. The threshold precedes both parameters and every covering cap. -/
theorem exists_actualSmallRosserPlusDensity_compact_close_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
              ((N : ℝ) ^ (p.2 * p.1)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) -
              suzukiContinuousUpperFactor p.2| < eta := by
  obtain ⟨L, hL, hlo⟩ := exists_actualSmallRosserPlusDensity_compact_lower_threshold
    S hS hparam (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ := exists_actualSmallRosserPlusDensity_compact_upper_threshold
    S hS hparam (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven p hp cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven p hp cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven p hp cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The lower ratio has the analogous common threshold, including all
compact-set points on the boundary with residual equal to two. -/
theorem exists_actualSmallRosserMinusDensity_compact_close_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
              ((N : ℝ) ^ (p.2 * p.1)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) -
              suzukiContinuousLowerFactor p.2| < eta := by
  obtain ⟨L, hL, hlo⟩ := exists_actualSmallRosserMinusDensity_compact_lower_threshold
    S hS hparam (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ := exists_actualSmallRosserMinusDensity_compact_upper_threshold
    S hS hparam (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven p hp cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven p hp cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven p hp cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem tendstoUniformlyOn_actualSmallRosserPlusDensity_ratio
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun (N : ℕ) (p : ℝ × ℝ) =>
        actualSmallRosserPlusDensity N (cap N p) ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.1))
      (fun p => suzukiContinuousUpperFactor p.2)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_compact_close_threshold S hS hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

theorem tendstoUniformlyOn_actualSmallRosserMinusDensity_ratio
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun (N : ℕ) (p : ℝ × ℝ) =>
        actualSmallRosserMinusDensity N (cap N p) ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) /
          actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.1))
      (fun p => suzukiContinuousLowerFactor p.2)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_compact_close_threshold S hS hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

end

end ImbalancedChen
