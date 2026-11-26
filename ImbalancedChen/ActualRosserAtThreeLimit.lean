import ImbalancedChen.ActualRosserAtThreeLower
import ImbalancedChen.ActualRosserAtThreeUpper
import ImbalancedChen.FullPowerEulerNormalization

/-!
# The same actual upper Rosser density converges at residual three

The independently proved lower and upper thresholds concern the same
literal coefficients, target exclusions, and ceiling level. Their common
threshold works for every covering enumeration cap. This gives convergence
for any eventually covering cap sequence, including the canonical ceiling
cap, and the corresponding full singular-series normalization.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- Both proved sides give one threshold uniform in the covering cap. -/
theorem exists_actualSmallRosserPlusDensity_at_three_close_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) -
              2 * Real.exp Real.eulerMascheroniConstant / 3| < eta := by
  obtain ⟨L, hL, hlo⟩ :=
    exists_actualSmallRosserPlusDensity_at_three_sharp_lower_threshold
      u hu (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ :=
    exists_actualSmallRosserPlusDensity_at_three_sharp_upper_threshold
      u hu (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- An arbitrary cap sequence can cover the power cutoff only eventually.
The conclusion is the actual same-coefficient two-sided limit. -/
theorem tendsto_actualSmallRosserPlusDensity_at_three_ratio
    (u : ℝ) (hu : 0 < u) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / 3)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_at_three_close_threshold u hu eta heta
  have hN0 : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hN0, heven, hcap] with N hN hEven hcapN
  simpa only [Real.dist_eq] using hbound N hN hEven.2 (cap N) hcapN

/-- The canonical strict power carrier uses the literal ceiling cap. -/
theorem tendsto_actualSmallRosserPlusDensity_at_three_ceil_ratio
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ u))
          ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
        actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ u)) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / 3)) :=
  tendsto_actualSmallRosserPlusDensity_at_three_ratio u hu _
    (Filter.Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ u)))

/-- Full singular-series normalization of this actual raw density. -/
theorem tendsto_actualSmallRosserPlusDensity_at_three_normalized
    (u : ℝ) (hu : 0 < u) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (4 / (3 * u))) := by
  have heuler : Tendsto (fun N : ℕ =>
      actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / u)) := by
    apply (tendsto_finiteSieveDensity_power_normalized hu).congr'
    filter_upwards [hcap] with N hN
    rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hN]
  have hlim := (tendsto_actualSmallRosserPlusDensity_at_three_ratio u hu cap hcap).mul heuler
  have hconstant : (2 * Real.exp Real.eulerMascheroniConstant / 3) *
      (2 * Real.exp (-Real.eulerMascheroniConstant) / u) = 4 / (3 * u) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hconstant] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun N hN => by
    field_simp [(actualSmallEulerProduct_pos N (cap N) ((N : ℝ) ^ u) hN.2).ne'])

/-- At the original level `R=N`, the normalized actual density tends to four. -/
theorem tendsto_actualSmallRosserPlusDensity_oneThird_normalized
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 4) := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one, div_one] using
    tendsto_actualSmallRosserPlusDensity_at_three_normalized
      (1 / 3) (by norm_num) cap hcap

end

end ImbalancedChen
