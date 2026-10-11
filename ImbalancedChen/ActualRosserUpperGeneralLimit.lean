import ImbalancedChen.ActualRosserOddGeneralLayers
import ImbalancedChen.ActualRosserUpperGeneralUpper
import ImbalancedChen.FullPowerEulerNormalization

/-!
# Actual upper Rosser density at all fixed residuals greater than one

The genuine odd-layer prefix bound and the all-depth upper bound concern
exactly the same actual coefficient and literal ceiling level. They imply
the two-sided limit at every fixed positive outer exponent and residual
above one. The limit is the canonical Suzuki continuous upper factor.
This module makes no inference of convergence uniform in those parameters.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory

/-- A common threshold for both sides is uniform in every covering cap.
The outer exponent and residual are fixed before this threshold is chosen. -/
theorem exists_actualSmallRosserPlusDensity_general_close_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) -
              suzukiContinuousUpperFactor s| < eta := by
  obtain ⟨L, hL, hlo⟩ := exists_actualSmallRosserPlusDensity_general_lower_threshold
    u hu s hs (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ := exists_actualSmallRosserPlusDensity_general_upper_threshold
    u hu s hs (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The same actual upper density converges to the canonical continuous upper
factor at every fixed residual greater than one. -/
theorem tendsto_actualSmallRosserPlusDensity_general_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (suzukiContinuousUpperFactor s)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_general_close_threshold u hu s hs eta heta
  have hN0 : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hN0, heven, hcap] with N hN hEven hcapN
  simpa only [Real.dist_eq] using hbound N hN hEven.2 (cap N) hcapN

/-- Multiplying by the independently proved target-deleted Euler
normalization gives the actual singular-series-normalized density limit. -/
theorem tendsto_actualSmallRosserPlusDensity_general_normalized
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
        suzukiContinuousUpperFactor s)) := by
  have heuler : Tendsto (fun N : ℕ =>
      actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / u)) := by
    apply (tendsto_finiteSieveDensity_power_normalized hu).congr'
    filter_upwards [hcap] with N hN
    rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hN]
  have hlim := (tendsto_actualSmallRosserPlusDensity_general_ratio u hu s hs cap hcap).mul heuler
  rw [mul_comm (suzukiContinuousUpperFactor s)] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun N hN => by
    field_simp [(actualSmallEulerProduct_pos N (cap N) ((N : ℝ) ^ u) hN.2).ne'])

/-- The canonical ceiling cap removes the cap premise from the limit. -/
theorem tendsto_actualSmallRosserPlusDensity_general_ceil_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ u))
          ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ u)) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (suzukiContinuousUpperFactor s)) :=
  tendsto_actualSmallRosserPlusDensity_general_ratio u hu s hs _
    (Filter.Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ u)))

end

end ImbalancedChen
