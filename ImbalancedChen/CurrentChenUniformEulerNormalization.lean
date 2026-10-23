import ImbalancedChen.CurrentChenFixedEulerNormalization
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Topology.Order.Compact

/-!
# Uniform normalization of the actual Euler product

The finite prime-deleted products are antitone in their cutoff exponent.
Two fixed positive endpoint limits therefore control an entire parameter
neighborhood, and a finite compact subcover gives one threshold before
the target, exponent, and covering cap.

The endpoint and compactness arguments reuse the mathematical routes of
UniformPowerEulerNormalization and CompactLocalThreshold locally. Their
old project dependency chains are not imported. This theorem concerns the
Euler normalizer, not a two-sided Rosser density or the signed policy mean.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- One threshold controls every exponent in the fixed positive interval
and every cap covering its literal strict power cutoff. -/
theorem exists_currentChen_actualEuler_power_uniform_threshold
    (a0 a1 eta : ℝ) (ha0 : 0 < a0) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ a : ℝ, a ∈ Set.Icc a0 a1 → ∀ cap : ℕ,
        (N : ℝ) ^ a ≤ (cap : ℝ) →
          |actualSmallEulerProduct N cap ((N : ℝ) ^ a) * Real.log (N : ℝ) /
              singularSeries N -
            2 * Real.exp (-Real.eulerMascheroniConstant) / a| < eta := by
  classical
  let F : ℕ → ℝ → ℝ := fun N a =>
    actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a) *
      Real.log (N : ℝ) / singularSeries N
  let c : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant)
  let f : ℝ → ℝ := fun a => c / a
  have hc : 0 < c := by dsimp [c]; positivity
  have canonical_cap_identity (N cap : ℕ) (a : ℝ)
      (hcap : (N : ℝ) ^ a ≤ (cap : ℝ)) :
      actualSmallEulerProduct N cap ((N : ℝ) ^ a) =
        actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a) := by
    rw [currentChen_model_actualEuler_eq_finite N cap _ hcap,
      currentChen_model_actualEuler_eq_finite N (Nat.ceil ((N : ℝ) ^ a)) _
        (Nat.le_ceil _)]
  have finite_normalized_antitone (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
      Antitone (F N) := by
    intro a b hab
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (le_trans (by decide : 1 ≤ (2 : ℕ)) hN)
    have hcap : Nat.ceil ((N : ℝ) ^ a) ≤ Nat.ceil ((N : ℝ) ^ b) :=
      Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le hN1 hab)
    have hsub : sievePrimes N (Nat.ceil ((N : ℝ) ^ a)) ⊆
        sievePrimes N (Nat.ceil ((N : ℝ) ^ b)) := by
      intro p hp
      obtain ⟨hpCap, hpPrime, hpN⟩ := mem_sievePrimes.mp hp
      exact mem_sievePrimes.mpr ⟨hpCap.trans_le hcap, hpPrime, hpN⟩
    have hfactor (p : ℕ) (hp : p ∈ sievePrimes N (Nat.ceil ((N : ℝ) ^ b))) :
        0 ≤ 1 - 1 / ((p : ℝ) - 1) ∧ 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
      have hpData := mem_sievePrimes.mp hp
      have hpne : p ≠ 2 := by
        intro heq
        subst p
        exact hpData.2.2 hEven.two_dvd
      have hp2 : (2 : ℝ) < p := by
        exact_mod_cast (show 2 < p by have := hpData.2.1.two_le; omega)
      have hden : 0 < (p : ℝ) - 1 := by linarith
      have hlt : 1 / ((p : ℝ) - 1) < (1 : ℝ) :=
        (div_lt_one hden).mpr (by linarith)
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
        div_nonneg zero_le_one hden.le
      constructor <;> linarith
    have hprod : finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ b)) ≤
        finiteSieveDensity N (Nat.ceil ((N : ℝ) ^ a)) := by
      unfold finiteSieveDensity
      exact Finset.prod_le_prod_of_subset_of_le_one hsub
        (fun p hp => (hfactor p hp).1) (fun p hp _ => (hfactor p hp).2)
    change actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ b)) ((N : ℝ) ^ b) *
        Real.log (N : ℝ) / singularSeries N ≤
      actualSmallEulerProduct N (Nat.ceil ((N : ℝ) ^ a)) ((N : ℝ) ^ a) *
        Real.log (N : ℝ) / singularSeries N
    rw [currentChen_model_actualEuler_eq_finite N (Nat.ceil ((N : ℝ) ^ b)) _
        (Nat.le_ceil _),
      currentChen_model_actualEuler_eq_finite N (Nat.ceil ((N : ℝ) ^ a)) _
        (Nat.le_ceil _)]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprod (Real.log_nonneg hN1))
      (singularSeries_pos N).le
  have local_common_threshold (x : ℝ) (hx : 0 < x) :
      ∃ n : ℕ, 2 ≤ n ∧
        ∀ᶠ a : ℝ in 𝓝 x, ∀ N : ℕ, n ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ a ≤ (cap : ℝ) →
            |actualSmallEulerProduct N cap ((N : ℝ) ^ a) * Real.log (N : ℝ) /
                singularSeries N -
              2 * Real.exp (-Real.eulerMascheroniConstant) / a| < eta := by
    have hf : ContinuousAt f x := continuousAt_const.div continuousAt_id hx.ne'
    obtain ⟨delta, hdelta, hnear⟩ :=
      Metric.continuousAt_iff.mp hf (eta / 8) (div_pos heta (by norm_num))
    let d : ℝ := min (x / 2) (delta / 2)
    let l : ℝ := x - d
    let u : ℝ := x + d
    have hd : 0 < d := lt_min (by positivity) (by positivity)
    have hdx : d ≤ x / 2 := min_le_left _ _
    have hdDelta : d < delta :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hl : 0 < l := by dsimp [l]; linarith
    have hlx : l < x := by dsimp [l]; linarith
    have hxu : x < u := by dsimp [u]; linarith
    have hu : 0 < u := hx.trans hxu
    have hdistL : dist l x < delta := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlx)]
      dsimp [l]
      linarith
    have hdistU : dist u x < delta := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxu)]
      dsimp [u]
      linarith
    have hnearL : |f l - f x| < eta / 8 := by
      simpa only [Real.dist_eq] using hnear hdistL
    have hnearU : |f u - f x| < eta / 8 := by
      simpa only [Real.dist_eq] using hnear hdistU
    have hleft : ∀ᶠ N : ℕ in atTop ⊓
        Filter.principal {N : ℕ | 0 < N ∧ Even N},
        |F N l - f l| < eta / 4 := by
      simpa only [F, f, c, Real.dist_eq] using
        Metric.tendsto_nhds.mp (tendsto_currentChen_actualEuler_fixed_normalized hl)
          (eta / 4) (div_pos heta (by norm_num))
    have hright : ∀ᶠ N : ℕ in atTop ⊓
        Filter.principal {N : ℕ | 0 < N ∧ Even N},
        |F N u - f u| < eta / 4 := by
      simpa only [F, f, c, Real.dist_eq] using
        Metric.tendsto_nhds.mp (tendsto_currentChen_actualEuler_fixed_normalized hu)
          (eta / 4) (div_pos heta (by norm_num))
    rw [Filter.eventually_inf_principal] at hleft hright
    have hboth : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
        (Even N → |F N l - f l| < eta / 4 ∧ |F N u - f u| < eta / 4) := by
      filter_upwards [hleft, hright, eventually_ge_atTop (2 : ℕ)]
        with N hleftN hrightN hN
      exact ⟨hN, fun hEven =>
        ⟨hleftN ⟨by omega, hEven⟩, hrightN ⟨by omega, hEven⟩⟩⟩
    obtain ⟨n, hn⟩ := eventually_atTop.mp hboth
    refine ⟨max 2 n, le_max_left _ _, ?_⟩
    filter_upwards [Ioo_mem_nhds hlx hxu] with a ha
    intro N hN hEven cap hcap
    obtain ⟨hN2, hEnds⟩ := hn N ((le_max_right _ _).trans hN)
    have hL := abs_lt.mp (hEnds hEven).1
    have hU := abs_lt.mp (hEnds hEven).2
    have hFL := finite_normalized_antitone N hN2 hEven ha.1.le
    have hFU := finite_normalized_antitone N hN2 hEven ha.2.le
    have haPos : 0 < a := hl.trans ha.1
    have hfL : f a ≤ f l :=
      div_le_div_of_nonneg_left hc.le hl ha.1.le
    have hfU : f u ≤ f a :=
      div_le_div_of_nonneg_left hc.le haPos ha.2.le
    have hgap : f l - f u < eta / 4 := by
      have h1 := abs_lt.mp hnearL
      have h2 := abs_lt.mp hnearU
      linarith
    rw [canonical_cap_identity N cap a hcap]
    change |F N a - f a| < eta
    apply abs_lt.mpr
    constructor <;> linarith
  have finite_compact_maximum :
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ a : ℝ, a ∈ Set.Icc a0 a1 → ∀ cap : ℕ,
          (N : ℝ) ^ a ≤ (cap : ℝ) →
            |actualSmallEulerProduct N cap ((N : ℝ) ^ a) * Real.log (N : ℝ) /
                singularSeries N -
              2 * Real.exp (-Real.eulerMascheroniConstant) / a| < eta := by
    let S : Set ℝ := Set.Icc a0 a1
    let P : ℕ → ℝ → Prop := fun N a => Even N →
      ∀ cap : ℕ, (N : ℝ) ^ a ≤ (cap : ℝ) →
        |actualSmallEulerProduct N cap ((N : ℝ) ^ a) * Real.log (N : ℝ) /
            singularSeries N -
          2 * Real.exp (-Real.eulerMascheroniConstant) / a| < eta
    have hlocal : ∀ x ∈ S, ∃ n : ℕ,
        ∀ᶠ a : ℝ in 𝓝[S] x, ∀ N : ℕ, n ≤ N → P N a := by
      intro x hx
      obtain ⟨n, _hn, hn⟩ := local_common_threshold x (ha0.trans_le hx.1)
      exact ⟨n, hn.filter_mono nhdsWithin_le_nhds⟩
    choose n hn using fun x : S => hlocal x.val x.property
    let U := fun x : S => {a : ℝ | ∀ N : ℕ, n x ≤ N → P N a}
    have hS : IsCompact S := isCompact_Icc
    obtain ⟨t, ht⟩ := hS.elim_nhdsWithin_subcover'
      (fun x hx => U ⟨x, hx⟩) (fun x hx => hn ⟨x, hx⟩)
    refine ⟨max 2 (t.sup n), le_max_left _ _, ?_⟩
    intro N hN hEven a ha cap hcap
    obtain ⟨x, hxt, hax⟩ := Set.mem_iUnion₂.mp (ht ha)
    exact hax N ((Finset.le_sup (f := n) hxt).trans
      ((le_max_right _ _).trans hN)) hEven cap hcap
  exact finite_compact_maximum

end

end ImbalancedChen
