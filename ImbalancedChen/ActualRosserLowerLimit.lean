import ImbalancedChen.ActualRosserEvenFiniteLayers
import ImbalancedChen.ActualRosserEvenSourceSeries
import ImbalancedChen.ActualRosserLowerThreshold
import ImbalancedChen.FullPowerEulerNormalization

/-!
# Same-weight lower Rosser density limits

The convergent genuine even-layer series selects a finite prefix before
the actual prime-box threshold. Its nonnegative boundary loss gives the
reverse bound for the same actual lower coefficient. Combining with the
proved all-depth lower threshold yields a two-sided limit for every fixed
positive outer exponent and residual at least two. No discrete-tail decay,
uniform parameter convergence or additional analytic premise is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple

/-- One finite continuous prefix supplies the complete reverse density
bound, with the mesh and target threshold chosen after that prefix. -/
theorem exists_actualSmallRosserMinusDensity_upper_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
          actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            suzukiContinuousLowerFactor s + eta := by
  have hnear := (tendsto_rosserEvenLayerIntegral_partialSum s hs).eventually
    (lt_mem_nhds (show 1 - suzukiContinuousLowerFactor s - eta / 2 <
      1 - suzukiContinuousLowerFactor s by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_evenFiniteLayers_upper_threshold
      (Finset.range m) s (by linarith) u hu (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

/-- A common threshold for both sides is uniform in every covering cap.
The outer exponent and residual are fixed before this threshold is chosen. -/
theorem exists_actualSmallRosserMinusDensity_close_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) -
              suzukiContinuousLowerFactor s| < eta := by
  obtain ⟨L, hL, hlo⟩ := exists_actualSmallRosserMinusDensity_lower_threshold
    u hu s hs (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ := exists_actualSmallRosserMinusDensity_upper_threshold
    u hu s hs (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The same actual lower density converges to the actual continuous lower
factor at every fixed residual at least two. -/
theorem tendsto_actualSmallRosserMinusDensity_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (suzukiContinuousLowerFactor s)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_close_threshold u hu s hs eta heta
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
theorem tendsto_actualSmallRosserMinusDensity_normalized
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
        suzukiContinuousLowerFactor s)) := by
  have heuler : Tendsto (fun N : ℕ =>
      actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / u)) := by
    apply (tendsto_finiteSieveDensity_power_normalized hu).congr'
    filter_upwards [hcap] with N hN
    rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hN]
  have hlim := (tendsto_actualSmallRosserMinusDensity_ratio u hu s hs cap hcap).mul heuler
  rw [mul_comm (suzukiContinuousLowerFactor s)] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun N hN => by
    field_simp [(actualSmallEulerProduct_pos N (cap N) ((N : ℝ) ^ u) hN.2).ne'])

/-- The canonical ceiling cap removes the cap premise from the limit. -/
theorem tendsto_actualSmallRosserMinusDensity_ceil_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ u))
          ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ u)) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (suzukiContinuousLowerFactor s)) :=
  tendsto_actualSmallRosserMinusDensity_ratio u hu s hs _
    (Filter.Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ u)))

/-- The concrete source factor has the exact classical first-interval
normalization, including its zero endpoint at two. -/
theorem suzukiContinuousLowerFactor_firstInterval_eq (s : ℝ)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiContinuousLowerFactor s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]

theorem tendsto_actualSmallRosserMinusDensity_firstInterval_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s)) := by
  simpa only [suzukiContinuousLowerFactor_firstInterval_eq s hs hs4] using
    tendsto_actualSmallRosserMinusDensity_ratio u hu s hs cap hcap

/-- The Euler and source amplitudes cancel exactly in the manuscript's
singular-series normalization; the remaining constant is `4 log(s-1)/(s*u)`. -/
theorem tendsto_actualSmallRosserMinusDensity_firstInterval_normalized
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (4 * Real.log (s - 1) / (s * u))) := by
  have hfactor : (2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
      suzukiContinuousLowerFactor s = 4 * Real.log (s - 1) / (s * u) := by
    rw [suzukiContinuousLowerFactor_firstInterval_eq s hs hs4, Real.exp_neg]
    field_simp
    ring
  simpa only [hfactor] using
    tendsto_actualSmallRosserMinusDensity_normalized u hu s hs cap hcap

end

end ImbalancedChen
