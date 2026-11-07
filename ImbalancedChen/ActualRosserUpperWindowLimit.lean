import ImbalancedChen.ActualRosserUpperWindowLower
import ImbalancedChen.ActualRosserUpperWindowUpper
import ImbalancedChen.ActualRosserCubeLimit

/-!
# Same-weight upper Rosser density limits through residual four

The two independent bounds in `[3,4]` concern the same raw coefficient at
the same literal ceiling level. Their common threshold is uniform in the
enumeration cap. Combining with the exact cube result covers every fixed
positive residual at most four. No uniform two-sided parameter limit is
inferred from these pointwise limits.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

/-- For fixed parameters in `[3,4]` both sides have a common cap-uniform
threshold, with the target and cap chosen afterwards. -/
theorem exists_actualSmallRosserPlusDensity_upperWindow_close_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) -
              jurkatRichertUpperLinearSieveFactor s| < eta := by
  obtain ⟨L, hL, hlo⟩ :=
    exists_actualSmallRosserPlusDensity_upperWindow_lower_threshold
      u hu s hs3 hs4 (eta / 2) (by linarith)
  obtain ⟨U, _hU, hhi⟩ :=
    exists_actualSmallRosserPlusDensity_upperWindow_upper_threshold
      u hu s (by linarith) hs4 (eta / 2) (by linarith)
  refine ⟨max L U, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven cap hcap
  have hl := hlo N ((le_max_left _ _).trans hN) hEven cap hcap
  have hh := hhi N ((le_max_right _ _).trans hN) hEven cap hcap
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The same actual density converges to the standard upper factor on the
second interval, with any eventually covering cap sequence. -/
theorem tendsto_actualSmallRosserPlusDensity_upperWindow_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (jurkatRichertUpperLinearSieveFactor s)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_upperWindow_close_threshold u hu s hs3 hs4 eta heta
  have hN0 : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hN0, heven, hcap] with N hN hEven hcapN
  simpa only [Real.dist_eq] using hbound N hN hEven.2 (cap N) hcapN

/-- Combining the cube identity with the second interval proves the raw
ratio limit for every fixed positive residual at most four. -/
theorem tendsto_actualSmallRosserPlusDensity_upToFour_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 0 < s) (hs4 : s ≤ 4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (jurkatRichertUpperLinearSieveFactor s)) := by
  by_cases hs3 : s ≤ 3
  · simpa only [jurkatRichertUpperLinearSieveFactor, hs3, if_true] using
      tendsto_actualSmallRosserPlusDensity_fixedResidual_ratio u hu s hs hs3 cap hcap
  · exact tendsto_actualSmallRosserPlusDensity_upperWindow_ratio
      u hu s (le_of_not_ge hs3) hs4 cap hcap

/-- The full singular-series constant is the product of the proved raw
factor and the proved target-deleted Mertens normalization. -/
theorem tendsto_actualSmallRosserPlusDensity_upToFour_normalized
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 0 < s) (hs4 : s ≤ 4)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
        jurkatRichertUpperLinearSieveFactor s)) := by
  have heuler : Tendsto (fun N : ℕ =>
      actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / u)) := by
    apply (tendsto_finiteSieveDensity_power_normalized hu).congr'
    filter_upwards [hcap] with N hN
    rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hN]
  have hlim := (tendsto_actualSmallRosserPlusDensity_upToFour_ratio u hu s hs hs4 cap hcap).mul heuler
  rw [mul_comm (jurkatRichertUpperLinearSieveFactor s)] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun N hN => by
    field_simp [(actualSmallEulerProduct_pos N (cap N) ((N : ℝ) ^ u) hN.2).ne'])

/-- A canonical covering sequence gives an unconditional instance of the
raw ratio limit, without leaving a cap hypothesis for the caller. -/
theorem tendsto_actualSmallRosserPlusDensity_upToFour_ceil_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 0 < s) (hs4 : s ≤ 4) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ u))
          ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ u)) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (jurkatRichertUpperLinearSieveFactor s)) :=
  tendsto_actualSmallRosserPlusDensity_upToFour_ratio u hu s hs hs4 _
    (Filter.Eventually.of_forall (fun N => Nat.le_ceil ((N : ℝ) ^ u)))

end

end ImbalancedChen
