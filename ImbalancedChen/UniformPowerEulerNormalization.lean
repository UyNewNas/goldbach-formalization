import ImbalancedChen.FullPowerEulerNormalization
import ImbalancedChen.SieveDimensionComparison
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform Euler normalization on compact positive exponent intervals

For each positive even target, its normalized Euler product is antitone
in the cutoff exponent. The proved pointwise leading constant is continuous
on the positive exponents. Two nearby fixed exponents therefore bracket
all intermediate exponents, giving locally uniform convergence without
asserting continuity of the finite, discontinuous Euler products. Compactness
then supplies one threshold for every exponent in a fixed closed interval.
The actual-carrier corollary is uniform in every cap covering its cutoff.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

private theorem normalizedPowerEuler_antitone {N : ℕ} (hN : 2 ≤ N)
    (hEven : Even N) :
    Antitone (fun a : ℝ => finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) *
      Real.log (N : ℝ) / singularSeries N) := by
  intro a b hab
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcap : Nat.ceil ((N : ℝ) ^ a) ≤ Nat.ceil ((N : ℝ) ^ b) :=
    Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hN1 hab)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (finiteSieveDensity_antitone hEven hcap)
      (Real.log_nonneg hN1)) (singularSeries_pos N).le

/-- Locally uniform convergence on all positive exponents. The finite
functions may have prime jumps; only their antitonicity is used. -/
theorem tendstoLocallyUniformlyOn_finiteSieveDensity_power_normalized :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (a : ℝ) => finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) *
        Real.log (N : ℝ) / singularSeries N)
      (fun a : ℝ => 2 * Real.exp (-Real.eulerMascheroniConstant) / a)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (Set.Ioi 0) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro eta heta a ha
  change 0 < a at ha
  let c : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant)
  let f : ℝ → ℝ := fun x => c / x
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : ContinuousAt f a := continuousAt_const.div continuousAt_id ha.ne'
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousAt_iff.mp hf (eta / 4) (by positivity)
  let d : ℝ := min (a / 2) (delta / 2)
  let l : ℝ := a - d
  let u : ℝ := a + d
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hda : d ≤ a / 2 := min_le_left _ _
  have hddelta : d < delta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hl : 0 < l := by dsimp [l]; linarith
  have hla : l < a := by dsimp [l]; linarith
  have hau : a < u := by dsimp [u]; linarith
  have hu : 0 < u := lt_trans ha hau
  have hdistL : dist l a < delta := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hla)]
    dsimp [l]
    linarith
  have hdistU : dist u a < delta := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hau)]
    dsimp [u]
    linarith
  have hnearL : |f l - f a| < eta / 4 := by
    simpa only [Real.dist_eq] using hnear hdistL
  have hnearU : |f u - f a| < eta / 4 := by
    simpa only [Real.dist_eq] using hnear hdistU
  refine ⟨Set.Ioo l u, nhdsWithin_le_nhds (Ioo_mem_nhds hla hau), ?_⟩
  have hleft : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      |finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ l)) * Real.log (N : ℝ) /
        singularSeries N - f l| < eta / 4 := by
    simpa only [Real.dist_eq, f, c] using
      Metric.tendsto_nhds.mp (tendsto_finiteSieveDensity_power_normalized hl)
        (eta / 4) (by positivity)
  have hright : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      |finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ u)) * Real.log (N : ℝ) /
        singularSeries N - f u| < eta / 4 := by
    simpa only [Real.dist_eq, f, c] using
      Metric.tendsto_nhds.mp (tendsto_finiteSieveDensity_power_normalized hu)
        (eta / 4) (by positivity)
  rw [Filter.eventually_inf_principal] at hleft hright ⊢
  filter_upwards [hleft, hright, eventually_ge_atTop (2 : ℕ)] with N hleftN hrightN hN
  rintro ⟨_hNpos, hEven⟩ x hx
  have hL := abs_lt.mp (hleftN ⟨by omega, hEven⟩)
  have hU := abs_lt.mp (hrightN ⟨by omega, hEven⟩)
  have hFL := normalizedPowerEuler_antitone hN hEven hx.1.le
  have hFU := normalizedPowerEuler_antitone hN hEven hx.2.le
  have hxpos : 0 < x := lt_trans hl hx.1
  have hfL : f x ≤ f l := div_le_div_of_nonneg_left hc.le hl hx.1.le
  have hfU : f u ≤ f x := div_le_div_of_nonneg_left hc.le hxpos hx.2.le
  have hgap : f l - f u < eta / 2 := by
    have h1 := abs_lt.mp hnearL
    have h2 := abs_lt.mp hnearU
    linarith
  change dist (f x) _ < eta
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- Uniform convergence on any closed interval bounded away from zero.
The statement also permits an empty interval. -/
theorem tendstoUniformlyOn_finiteSieveDensity_power_normalized
    (a0 a1 : ℝ) (ha0 : 0 < a0) :
    TendstoUniformlyOn
      (fun (N : ℕ) (a : ℝ) => finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) *
        Real.log (N : ℝ) / singularSeries N)
      (fun a : ℝ => 2 * Real.exp (-Real.eulerMascheroniConstant) / a)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (Set.Icc a0 a1) := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
  exact tendstoLocallyUniformlyOn_finiteSieveDensity_power_normalized.mono
    (fun _ ha => ha0.trans_le ha.1)

/-- One natural threshold works simultaneously for every later positive
even target, every exponent in the interval, and every enumeration cap
covering that exponent's strict cutoff. The cap may vary with both N and a. -/
theorem exists_actualSmallEulerProduct_power_uniform_threshold
    (a0 a1 eta : ℝ) (ha0 : 0 < a0) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ a : ℝ, a ∈ Set.Icc a0 a1 → ∀ cap : ℕ, (N : ℝ) ^ a ≤ (cap : ℝ) →
        |actualSmallEulerProduct N cap ((N : ℝ) ^ a) * Real.log (N : ℝ) /
          singularSeries N - 2 * Real.exp (-Real.eulerMascheroniConstant) / a| < eta := by
  have huniform := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_finiteSieveDensity_power_normalized a0 a1 ha0) eta heta
  rw [Filter.eventually_inf_principal] at huniform
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp huniform
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven a ha cap hcap
  have hlarge : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have h := hN1 N hlarge ⟨by omega, hEven⟩ a ha
  rw [Real.dist_eq, abs_sub_comm] at h
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N cap ((N : ℝ) ^ a) hcap]
  exact h

/-- An exponent may vary with the target, provided it converges to a
positive limit along the same positive-even filter. No rate is needed. -/
theorem tendsto_finiteSieveDensity_varying_power_normalized
    (alpha : ℕ → ℝ) {a : ℝ} (ha : 0 < a)
    (halpha : Tendsto alpha
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 a)) :
    Tendsto (fun N : ℕ => finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ alpha N)) *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hinterval : ∀ᶠ N : ℕ in
      atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      alpha N ∈ Set.Icc (a / 2) (2 * a) :=
    halpha.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hzero : Tendsto (fun N : ℕ =>
      finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ alpha N)) * Real.log (N : ℝ) /
        singularSeries N - 2 * Real.exp (-Real.eulerMascheroniConstant) / alpha N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eta heta
    have huniform := Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_finiteSieveDensity_power_normalized
        (a / 2) (2 * a) (by positivity)) eta heta
    filter_upwards [huniform, hinterval] with N hN hmem
    rw [Real.dist_eq, sub_zero, abs_sub_comm]
    exact hN (alpha N) hmem
  have hmain : Tendsto (fun N : ℕ =>
      2 * Real.exp (-Real.eulerMascheroniConstant) / alpha N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) :=
    tendsto_const_nhds.div halpha ha.ne'
  simpa only [sub_add_cancel, zero_add] using hzero.add hmain

/-- The moving-exponent result for the same actual small-prime carrier.
The natural cap may also vary and only eventually needs to cover the cutoff. -/
theorem tendsto_actualSmallEulerProduct_varying_power_normalized
    (alpha : ℕ → ℝ) (cap : ℕ → ℕ) {a : ℝ} (ha : 0 < a)
    (halpha : Tendsto alpha
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 a))
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ alpha N ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualSmallEulerProduct N (cap N) ((N : ℝ) ^ alpha N) *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  apply (tendsto_finiteSieveDensity_varying_power_normalized alpha ha halpha).congr'
  filter_upwards [hcap] with N hN
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) ((N : ℝ) ^ alpha N) hN]

end

end ImbalancedChen
