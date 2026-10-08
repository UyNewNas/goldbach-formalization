/-
SPDX-License-Identifier: Apache-2.0

NONEXECUTED CONSUMER CANDIDATE. Held outside the owned project source tree.
No Lean/Lake invocation, foreign execution, axiom replay, kernel replay,
publication, or integration into the owned core has been performed.

Uses the actual proved PNT and Mertens interfaces of the Apache-2.0 project
subfish-zhou/goldbach-lean at 09b97db5764ade1246bfb77206baa1b124760958:
* AnalyticNumberTheory/PrimeDistribution/PrimeNumberTheorem.lean
* AnalyticNumberTheory/Mertens/Theorems.lean
The adjacent LICENSE preserves the upstream Apache-2.0 notice. Upstream:
https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/docs/PROVENANCE.md
The PNT implementation credits AlexKontorovich/PrimeNumberTheoremAnd,
release v4.32.2, commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.

Modifications: actual prime-prefix cardinality bridge; negligible actual
centre-prime correction; exact strict real-cutoff ceiling/predecessor
bridge; positive-power log scaling; actual density and mass normalization.
No supplier analytic proof body or pending lower-sieve module is copied.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1;
LeanArchitect 78dd66840d3efe8c824c699fc03381cec817c271.
-/
import ImbalancedChen.CenterEulerTail
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.Mertens.Theorems

/-!
# Actual initial Chen mass and strict real-cutoff density normalization

The mass is the cardinality of the actual coprime additive-prime source,
not a logarithmic-integral model. Its exact difference from the inclusive
prime prefix is retained and proved negligible using the owned bound.

For every fixed real `a > 0`, `z = N^a` means the strict real prime cutoff.
The natural sieve cap is `ceil z`; the inclusive Mertens endpoint is
`ceil z - 1`, including when `z` itself is integral. The varying-centre
Euler tail is paid using the owned uniform general-power theorem.

The density limit is restricted to positive even centres, and its full
manuscript singular series has no hidden factor two. The leading factor
`2 * exp(-EulerGamma)` is explicit. No PNT, Mertens, source-mass asymptotic,
fixed-centre truncation limit, or target density estimate is a premise.
-/

namespace ImbalancedChen.ChenInitialNormalizationAdapter

noncomputable section

open Filter Topology
open scoped BigOperators

/-- The inclusive prefix in the actual-source identity is exactly pi(N). -/
theorem chenPrimePrefix_card_eq_primeCounting (N : ℕ) :
    (chenPrimePrefix N).card = Nat.primeCounting N := by
  simp only [chenPrimePrefix, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

/-- The centre-prime subtraction is literal, including a prime centre. -/
theorem actual_initial_mass_eq_primeCounting_sub (N : ℕ) :
    ((chenAdditivePrimeCarrier N).card : ℝ) =
      (Nat.primeCounting N : ℝ) - chenPrimeDivisorCount N N := by
  rw [chenAdditivePrimeCarrier_card_cast, chenPrimePrefix_card_eq_primeCounting]

/-- Genuine PNT, specialized to the normalization used by the initial sieve. -/
theorem tendsto_primeCounting_div_main :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 1) := by
  obtain ⟨c, hc, hcount⟩ :=
    AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
  have hc0 : Tendsto c atTop (𝓝 0) := by
    simpa only [div_one] using hc.tendsto_div_nhds_zero
  have h := hc0.const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hNr)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNr).ne'
  rw [hcount]
  field_simp [hN0, hlog] <;> ring

/-- The actual full prefix-centre correction costs o(N/log N). -/
theorem tendsto_centre_prime_correction_div_main :
    Tendsto (fun N : ℕ => chenPrimeDivisorCount N N /
      ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)) ^ 2 / (N : ℝ) / Real.log 2) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, zero_div] using
      (tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0 : ℝ) < 1)).div_const
        (Real.log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact div_nonneg (chenPrimeDivisorCount_nonneg N N)
      (div_nonneg (Nat.cast_nonneg N) (Real.log_pos hNr).le)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hNr
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
    calc
      chenPrimeDivisorCount N N / ((N : ℝ) / Real.log (N : ℝ)) ≤
          (Real.log (N : ℝ) / Real.log 2) /
            ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right
          (chenPrimeDivisorCount_le_log N (by omega : 0 < N))
          (div_pos hNpos hlog).le
      _ = (Real.log (N : ℝ)) ^ 2 / (N : ℝ) / Real.log 2 := by
        field_simp [hNpos.ne', hlog.ne',
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] <;> ring

/-- Actual X_N ~ N/log N, on all natural centres before any parity gate. -/
theorem tendsto_actual_initial_mass_div_main :
    Tendsto (fun N : ℕ => ((chenAdditivePrimeCarrier N).card : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ))) atTop (𝓝 1) := by
  have h := tendsto_primeCounting_div_main.sub
    tendsto_centre_prime_correction_div_main
  simpa only [sub_zero, actual_initial_mass_eq_primeCounting_sub, sub_div] using h

/-- The actual `BoundingSieve.totalMass` statement is uniform in the real
cutoff; the only evenness assumption is the constructor's existing gate. -/
theorem eventually_actual_initial_totalMass_div_main
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N,
      |(chenInitialBoundingSieve N z hN).totalMass /
        ((N : ℝ) / Real.log (N : ℝ)) - 1| < epsilon := by
  have h := Metric.tendsto_nhds.mp tendsto_actual_initial_mass_div_main
    epsilon hepsilon
  filter_upwards [h] with N hN z hEven
  simpa only [chenInitialBoundingSieve, Real.dist_eq] using hN

/-- Exact natural cap for the strict real power cutoff. -/
def powerSieveCap (a : ℝ) (N : ℕ) : ℕ := Nat.ceil ((N : ℝ) ^ a)

/-- Mertens is inclusive, so its endpoint is the predecessor of the cap. -/
def powerMertensEndpoint (a : ℝ) (N : ℕ) : ℕ := powerSieveCap a N - 1

/-- This bridge is exact even when a prime equals the real cutoff. -/
theorem mem_power_sieve_primes {a : ℝ} {N p : ℕ} :
    p ∈ sievePrimes N (powerSieveCap a N) ↔
      (p : ℝ) < (N : ℝ) ^ a ∧ Nat.Prime p ∧ ¬p ∣ N :=
  mem_sievePrimes_chen_real_cap

/-- For a positive cap, the strict and inclusive ordinary Euler products
coincide at precisely cap-1; no floor endpoint is substituted. -/
theorem primeEulerProduct_eq_supplier_predecessor {k : ℕ} (hk : 0 < k) :
    primeEulerProduct k = AnalyticNumberTheory.Mertens.primeProduct (k - 1) := by
  classical
  have hset : primesBelowCap k = AnalyticNumberTheory.Mertens.primesUpTo (k - 1) := by
    ext p
    simp only [mem_primesBelowCap, AnalyticNumberTheory.Mertens.mem_primesUpTo]
    constructor
    · rintro ⟨hpk, hp⟩
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hpk⟩
      exact ⟨by omega, hp⟩
  unfold primeEulerProduct AnalyticNumberTheory.Mertens.primeProduct
  rw [hset]

/-- Both endpoints go to infinity at every fixed positive exponent. -/
theorem tendsto_powerSieveCap_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (powerSieveCap a) atTop atTop := by
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop (b : ℝ)))
  refine ⟨N₀, fun N hN => ?_⟩
  exact Nat.cast_le.mp ((hN₀ N hN).trans (Nat.le_ceil _))

theorem tendsto_powerMertensEndpoint_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (powerMertensEndpoint a) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_powerSieveCap_atTop ha).eventually (eventually_ge_atTop (b + 1)))
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  unfold powerMertensEndpoint
  omega

/-- In particular, the endpoint always lies in [N^a-1,N^a) when N^a>0.
The upper inequality is strict at every integral cutoff as well. -/
theorem powerMertensEndpoint_bounds {a : ℝ} {N : ℕ}
    (hpower : 0 < (N : ℝ) ^ a) :
    (N : ℝ) ^ a - 1 ≤ (powerMertensEndpoint a N : ℝ) ∧
      (powerMertensEndpoint a N : ℝ) < (N : ℝ) ^ a := by
  have hcap : 1 ≤ powerSieveCap a N := Nat.one_le_ceil_iff.mpr hpower
  constructor
  · unfold powerMertensEndpoint
    rw [Nat.cast_sub hcap, Nat.cast_one]
    exact sub_le_sub_right (Nat.le_ceil _) 1
  · apply Nat.lt_ceil.mp
    change powerSieveCap a N - 1 < powerSieveCap a N
    omega

/-- Rounding loses less than one, hence a vanishing relative amount. -/
theorem tendsto_powerMertensEndpoint_div_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (powerMertensEndpoint a N : ℝ) / (N : ℝ) ^ a)
      atTop (𝓝 1) := by
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ) ^ a) atTop (𝓝 1) := by
    simpa only [sub_zero] using (hpower.const_div_atTop 1).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [hpower.eventually (eventually_gt_atTop 0)] with N hpos
    calc
      1 - 1 / (N : ℝ) ^ a = ((N : ℝ) ^ a - 1) / (N : ℝ) ^ a := by
        rw [sub_div, div_self hpos.ne']
      _ ≤ (powerMertensEndpoint a N : ℝ) / (N : ℝ) ^ a :=
        div_le_div_of_nonneg_right (powerMertensEndpoint_bounds hpos).1 hpos.le
  · filter_upwards [hpower.eventually (eventually_gt_atTop 0)] with N hpos
    exact (div_le_one hpos).mpr (powerMertensEndpoint_bounds hpos).2.le

/-- The logarithm of the rounding ratio tends to zero. This controls a
moving cutoff while the centre varies, rather than fixing the centre. -/
theorem tendsto_log_powerMertensEndpoint_sub_log_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (powerMertensEndpoint a N : ℝ) -
      Real.log ((N : ℝ) ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_powerMertensEndpoint_div_power ha).log one_ne_zero
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [(tendsto_powerMertensEndpoint_atTop ha).eventually
    (eventually_ge_atTop (1 : ℕ)), eventually_ge_atTop (1 : ℕ)] with N hy hN
  have hypos : (0 : ℝ) < powerMertensEndpoint a N := by
    exact_mod_cast (show 0 < powerMertensEndpoint a N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact Real.log_div hypos.ne' (Real.rpow_pos_of_pos hNpos a).ne'

/-- Exact logarithmic scale of the inclusive endpoint for the strict cap. -/
theorem tendsto_log_powerMertensEndpoint_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (powerMertensEndpoint a N : ℝ) /
      Real.log (N : ℝ)) atTop (𝓝 a) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero := (tendsto_log_powerMertensEndpoint_sub_log_power ha).div_atTop hlog
  have h := hzero.add_const a
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hNr
  rw [Real.log_rpow hNpos]
  field_simp [(Real.log_pos hNr).ne'] <;> ring

/-- The named genuine Mertens theorem gives the exact Euler constant. -/
theorem tendsto_supplier_primeProduct_mul_log :
    Tendsto (fun n : ℕ => AnalyticNumberTheory.Mertens.primeProduct n *
      Real.log (n : ℝ)) atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  obtain ⟨C, _hC, hbound⟩ := AnalyticNumberTheory.Mertens.primeProduct_mertens_nat
  have hsmall : Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [hsmall.eventually (gt_mem_nhds hepsilon),
    eventually_ge_atTop (2 : ℕ)] with n hsmalln hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  calc
    dist (AnalyticNumberTheory.Mertens.primeProduct n * Real.log (n : ℝ))
        (Real.exp (-Real.eulerMascheroniConstant)) =
        |AnalyticNumberTheory.Mertens.primeProduct n -
          Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)| *
            Real.log (n : ℝ) := by
      rw [Real.dist_eq]
      calc
        |AnalyticNumberTheory.Mertens.primeProduct n * Real.log (n : ℝ) -
            Real.exp (-Real.eulerMascheroniConstant)| =
            |(AnalyticNumberTheory.Mertens.primeProduct n -
              Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)) *
                Real.log (n : ℝ)| := by
          congr 1
          field_simp [hlog.ne'] <;> ring
        _ = _ := by rw [abs_mul, abs_of_pos hlog]
    _ ≤ (C / (Real.log (n : ℝ)) ^ 2) * Real.log (n : ℝ) :=
      mul_le_mul_of_nonneg_right (hbound n hn) hlog.le
    _ = C / Real.log (n : ℝ) := by field_simp [hlog.ne'] <;> ring
    _ < epsilon := hsmalln

/-- Ordinary strict real-cutoff prime product, with no centre correction. -/
theorem tendsto_primeEulerProduct_power_mul_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => primeEulerProduct (powerSieveCap a N) *
      Real.log (N : ℝ)) atTop
        (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hmertens := tendsto_supplier_primeProduct_mul_log.comp
    (tendsto_powerMertensEndpoint_atTop ha)
  have h := hmertens.div (tendsto_log_powerMertensEndpoint_div_log ha) ha.ne'
  apply h.congr'
  filter_upwards [(tendsto_powerMertensEndpoint_atTop ha).eventually
    (eventually_ge_atTop (2 : ℕ)), eventually_ge_atTop (2 : ℕ)] with N hy hN
  have hy1 : (1 : ℝ) < powerMertensEndpoint a N := by
    exact_mod_cast (show 1 < powerMertensEndpoint a N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hcap : 0 < powerSieveCap a N := by
    dsimp [powerMertensEndpoint] at hy
    omega
  rw [primeEulerProduct_eq_supplier_predecessor hcap]
  change
    (AnalyticNumberTheory.Mertens.primeProduct (powerMertensEndpoint a N) *
      Real.log (powerMertensEndpoint a N : ℝ)) /
        (Real.log (powerMertensEndpoint a N : ℝ) / Real.log (N : ℝ)) = _
  field_simp [(Real.log_pos hy1).ne', (Real.log_pos hN1).ne'] <;> ring

/-- The genuine odd Euler product and the uniform varying-centre tail
supply the remaining factor. Fixed-centre convergence is not used. -/
theorem tendsto_oddEulerProduct_div_full_tail_power {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => oddEulerProduct (powerSieveCap a N) /
      (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a))) atTop (𝓝 1) := by
  have hodd := tendsto_oddEulerProduct.comp (tendsto_powerSieveCap_atTop ha)
  have htail := (tendsto_centerEulerTail_power ha).const_mul twinPrimeConstant
  simp only [mul_one] at htail
  have h := hodd.div htail twinPrimeConstant_pos.ne'
  simpa only [div_self twinPrimeConstant_pos.ne'] using h

/-- Algebraic use of the owned exact Euler identity. The full series stays
at the full centre N and the leading factor two remains explicit. -/
theorem actual_density_log_normalization_eq {a : ℝ} {N : ℕ}
    (hN : N ≠ 0) (hEven : Even N) (hcap : 2 < powerSieveCap a N) :
    finiteSieveDensity N (powerSieveCap a N) * Real.log (N : ℝ) / singularSeries N =
      2 * (primeEulerProduct (powerSieveCap a N) * Real.log (N : ℝ)) *
        (oddEulerProduct (powerSieveCap a N) /
          (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a))) := by
  have h := normalizedFiniteSieveDensity_eq_odd_div_tail hN hEven hcap
  change finiteSieveDensity N (powerSieveCap a N) /
    (2 * primeEulerProduct (powerSieveCap a N) * singularSeries N) =
      oddEulerProduct (powerSieveCap a N) /
        (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a)) at h
  rw [(div_eq_iff (finiteSieveNormalization_denominator_pos N
    (powerSieveCap a N)).ne').mp h]
  have htail : centerEulerTail N ((N : ℝ) ^ a) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (one_le_centerEulerTail N ((N : ℝ) ^ a))).ne'
  field_simp [(singularSeries_pos N).ne', twinPrimeConstant_pos.ne', htail] <;> ring

/-- Actual V_N(N^a) * log N / S(N) -> 2 exp(-EulerGamma)/a along the
positive even centres. This is for every fixed real exponent a>0. -/
theorem tendsto_actual_density_mul_log_div_singularSeries {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => finiteSieveDensity N (powerSieveCap a N) *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hfull := ((tendsto_primeEulerProduct_power_mul_log ha).mul
    (tendsto_oddEulerProduct_div_full_tail_power ha)).const_mul 2
  have hlim : Tendsto (fun N : ℕ =>
      2 * (primeEulerProduct (powerSieveCap a N) * Real.log (N : ℝ)) *
        (oddEulerProduct (powerSieveCap a N) /
          (twinPrimeConstant * centerEulerTail N ((N : ℝ) ^ a))))
      atTop (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
    simpa only [mul_one, ← mul_assoc, ← mul_div_assoc] using hfull
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  rw [Filter.eventually_inf_principal]
  filter_upwards [Metric.tendsto_nhds.mp hlim epsilon hepsilon,
    (tendsto_powerSieveCap_atTop ha).eventually (eventually_gt_atTop 2)]
    with N hclose hcap
  intro hN
  rw [actual_density_log_normalization_eq hN.1.ne' hN.2 hcap]
  exact hclose

/-- Relative asymptotic with exactly the full manuscript correction and
`2 exp(-EulerGamma)/(a log N)`. All normalizing factors are nonzero
eventually; no correction depending on the cutoff is hidden in S(N). -/
theorem tendsto_actual_density_div_mertens_main {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => finiteSieveDensity N (powerSieveCap a N) /
      (singularSeries N *
        (2 * Real.exp (-Real.eulerMascheroniConstant) / (a * Real.log (N : ℝ)))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 1) := by
  have hC : 2 * Real.exp (-Real.eulerMascheroniConstant) / a ≠ 0 := by positivity
  have h := (tendsto_actual_density_mul_log_div_singularSeries ha).div_const
    (2 * Real.exp (-Real.eulerMascheroniConstant) / a)
  rw [div_self hC] at h
  apply h.congr'
  rw [Filter.eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  intro _hEven
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  field_simp [(singularSeries_pos N).ne', ha.ne', (Real.log_pos hN1).ne',
    (Real.exp_pos (-Real.eulerMascheroniConstant)).ne'] <;> ring

/-- This finite product is literally the density of the actual initial
BoundingSieve, not an unrelated or logarithmic-integral model. -/
theorem actual_initial_density_eq_product (N : ℕ) (z : ℝ) (hEven : Even N) :
    finiteSieveDensity N (Nat.ceil z) =
      ∏ p ∈ sievePrimes N (Nat.ceil z),
        (1 - (chenInitialBoundingSieve N z hEven).nu p) := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [chenInitialBoundingSieve_prime_density N z hEven (mem_sievePrimes.mp hp).2.1]

/-- Both normalizations for the actual initial sieve, with one threshold,
the literal real power cutoff, full series, and explicit constructor gate. -/
theorem exists_actual_initial_normalization_threshold {a : ℝ} (ha : 0 < a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      2 ≤ N ∧
      |(chenInitialBoundingSieve N ((N : ℝ) ^ a) hEven).totalMass /
        ((N : ℝ) / Real.log (N : ℝ)) - 1| < epsilon ∧
      |(∏ p ∈ sievePrimes N (Nat.ceil ((N : ℝ) ^ a)),
          (1 - (chenInitialBoundingSieve N ((N : ℝ) ^ a) hEven).nu p)) /
        (singularSeries N *
          (2 * Real.exp (-Real.eulerMascheroniConstant) / (a * Real.log (N : ℝ)))) -
          1| < epsilon := by
  have hmass := eventually_actual_initial_totalMass_div_main epsilon hepsilon
  have hdensity := Metric.tendsto_nhds.mp
    (tendsto_actual_density_div_mertens_main ha) epsilon hepsilon
  rw [Filter.eventually_inf_principal] at hdensity
  apply eventually_atTop.mp
  filter_upwards [hmass, hdensity, eventually_ge_atTop (2 : ℕ)] with N hm hd hN
  intro hEven
  refine ⟨hN, hm _ hEven, ?_⟩
  rw [← actual_initial_density_eq_product N ((N : ℝ) ^ a) hEven]
  simpa only [powerSieveCap, Real.dist_eq] using hd ⟨by omega, hEven⟩

end

end ImbalancedChen.ChenInitialNormalizationAdapter
