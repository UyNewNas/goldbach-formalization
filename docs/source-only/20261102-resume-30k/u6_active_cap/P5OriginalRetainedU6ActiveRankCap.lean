import ImbalancedChen.P5OriginalRetainedU6RawSourcePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is a restriction of the literal J coefficient, with its entire
pair-dependent even-exit policy unchanged. It is NOT a new lower policy.
Unique small/rough factors give an actual rank stratification of its
physical support. Rank <= 2 satisfies the original piecewise L6 cap;
rank <= 3 satisfies the original global cap; rank <= 7 has a strict
subunit cap and its two prime corrections can therefore be paid.
All higher-rank signed atoms remain in the final original raw count.
No complete W/tent adoption, H248, PP saving or L6 endpoint is assumed.
-/

namespace ImbalancedChen.P5OriginalRetainedU6ActiveRankCap

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalRetainedU6RawSourcePayment

def enumerationCap (N : ℕ) : ℕ := Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)

def factorPairs (N : ℕ) (epsilon : ℝ) (policy : Policy) (p : ℕ × ℕ) :
    Finset (ℕ × ℕ) :=
  P5CausalRhoFactorization.activePairs (policy p) N (enumerationCap N)
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon)

def shortFactors (r N : ℕ) (epsilon : ℝ) (policy : Policy) (p : ℕ × ℕ) :
    Finset (ℕ × ℕ) :=
  (factorPairs N epsilon policy p).filter (fun x => x.2.primeFactors.card ≤ r)

def physical (p x : ℕ × ℕ) : ℕ := (p.1 * p.2) * (x.1 * x.2)

def shortSupport (r N : ℕ) (eta epsilon : ℝ) (policy : Policy) : Finset ℕ :=
  (source N eta).biUnion (fun p => (shortFactors r N epsilon policy p).image (physical p))

theorem factor_product_mem {N : ℕ} {epsilon : ℝ} {policy : Policy}
    {p x : ℕ × ℕ} (hx : x ∈ factorPairs N epsilon policy p) :
    x.1 * x.2 ∈ divisors N epsilon policy p := by
  exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩

theorem shortSupport_subset (r N : ℕ) (eta epsilon : ℝ) (policy : Policy) :
    shortSupport r N eta epsilon policy ⊆ support N eta epsilon policy := by
  intro q hq
  obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨⟨p, x.1 * x.2⟩,
    Finset.mem_sigma.mpr ⟨hp, factor_product_mem (Finset.mem_filter.mp hx).1⟩, rfl⟩

/-- The rank split reads the genuine scalar coefficient; no new
independent beta product is substituted. -/
theorem sigma_at_factor {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {p x : ℕ × ℕ} (hp : p ∈ source N eta) (hx : x ∈ factorPairs N epsilon policy p) :
    sigma N eta epsilon policy (physical p x) =
      P5CausalRhoFactorization.coefficient (policy p) N (enumerationCap N)
        (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon) x := by
  have hm : (⟨p, x.1 * x.2⟩ : Mark) ∈ marks N eta epsilon policy :=
    Finset.mem_sigma.mpr ⟨hp, factor_product_mem hx⟩
  rw [show physical p x = modulus (⟨p, x.1 * x.2⟩ : Mark) from rfl,
    sigma_at_mark policy hwz hm]
  exact P5CausalRhoFactorization.rho_at_pair (policy p) N (enumerationCap N)
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon)
    (Finset.mem_filter.mp hx).1

theorem shortSupport_active {r N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ} (hq : q ∈ shortSupport r N eta epsilon policy) :
    sigma N eta epsilon policy q ≠ 0 := by
  obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have hactive := (Finset.mem_filter.mp hx).1
  rw [sigma_at_factor policy hwz hp hactive]
  exact (Finset.mem_filter.mp hactive).2

/-- The actual strict retained source has the literal buffered product
wall. This bound does not identify its raw density with a Runbo mean. -/
theorem source_log_product {N : ℕ} (hN : (1 : ℝ) < N) {eta : ℝ}
    {p : ℕ × ℕ} (hp : p ∈ source N eta) :
    currentChenUpsilon6LogCoordinates N p 0 + currentChenUpsilon6LogCoordinates N p 1 ≤
      (833 / 2500 : ℝ) - eta := by
  have hx := ((mem_currentChenUpsilon6RetainedSelector_log_iff hN _ eta p).mp
    (source_subset_closed N eta hp)).2.2.2
  exact hx.2

/-- A uniform strict lower gap for the original L6 physical level,
proved separately on its enhanced and nonenhanced branches. -/
theorem original_level_gt {eta : ℝ} {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    (53 / 100 : ℝ) < P5U6CausalLevelGeometry.physicalLevel (x 0) (x 1) := by
  obtain ⟨hu, huh, ht, htd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx.1
  by_cases htm : x 1 < VariableEnvelope.mu
  · have hv : VariableEnvelope.v (x 1) = (1 + x 1) / 2 :=
      VariableEnvelope.v_eq_A htm.le
    have hbase : (53 / 100 : ℝ) < VariableEnvelope.v (x 1) := by
      rw [hv]
      linarith
    unfold P5U6CausalLevelGeometry.physicalLevel
    rw [if_pos htm]
    exact hbase.trans_le (le_max_left _ _)
  · rw [P5U6CausalLevelGeometry.physicalLevel_nonEnhanced (le_of_not_gt htm)]
    linarith

/-- All rough primes are below the original N^a cutoff. Squarefreeness
turns that real prime bound into a product bound at the actual rank. -/
theorem rough_factor_le_power {N : ℕ} (hN : (1 : ℝ) < N) {epsilon : ℝ}
    {policy : Policy} {p x : ℕ × ℕ} (hx : x ∈ factorPairs N epsilon policy p) :
    (x.2 : ℝ) ≤ (N : ℝ) ^ (a * (x.2.primeFactors.card : ℝ)) := by
  have hr := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  have hsf := fixedEvenRoughSupport_squarefree (policy p) N (enumerationCap N)
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) hr
  calc
    (x.2 : ℝ) = ∏ l ∈ x.2.primeFactors, (l : ℝ) := by
      exact_mod_cast (Nat.prod_primeFactors_of_squarefree hsf).symm
    _ ≤ ∏ _l ∈ x.2.primeFactors, (N : ℝ) ^ a := by
      apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
      intro l hl
      exact (mem_roughPrimeUniverse_upper
        (fixedEvenRoughSupport_primeFactors_mem (policy p) N (enumerationCap N)
          (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) hr hl)).le
    _ = _ := by
      rw [Finset.prod_const, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]

/-- This is the full b*s*r modulus. Both beta signs give the strict
small-factor bound, derived from actual nonvanishing, including r=1. -/
theorem active_physical_lt_rank_power {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} {policy : Policy} {p x : ℕ × ℕ}
    (hp : p ∈ source N eta) (hx : x ∈ factorPairs N epsilon policy p) :
    (physical p x : ℝ) < (N : ℝ) ^
      (currentChenUpsilon6LogCoordinates N p 0 + currentChenUpsilon6LogCoordinates N p 1 +
        a * epsilon + a * (x.2.primeFactors.card : ℝ)) := by
  have hs := P5CausalRhoFactorization.active_small_factor_lt (policy p) N (enumerationCap N)
    (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon) hx
  change (x.1 : ℝ) < (N : ℝ) ^ (a * epsilon) at hs
  have hr := rough_factor_le_power hN hx
  have hb := P5U6CausalLevelGeometry.pair_product_power hN (source_subset_sixth N eta hp)
  have hrough := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
  have hrpos : (0 : ℝ) < x.2 := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fixedEvenRoughSupport_squarefree (policy p) N (enumerationCap N)
        (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) hrough).ne_zero
  have hNpos := zero_lt_one.trans hN
  have hsr := (mul_lt_mul_of_pos_right hs hrpos).trans_le
    (mul_le_mul_of_nonneg_left hr (Real.rpow_pos_of_pos hNpos (a * epsilon)).le)
  calc
    (physical p x : ℝ) = (N : ℝ) ^
        (currentChenUpsilon6LogCoordinates N p 0 + currentChenUpsilon6LogCoordinates N p 1) *
          ((x.1 : ℝ) * (x.2 : ℝ)) := by
      rw [hb]
      simp only [physical, Nat.cast_mul]
    _ < (N : ℝ) ^
        (currentChenUpsilon6LogCoordinates N p 0 + currentChenUpsilon6LogCoordinates N p 1) *
          ((N : ℝ) ^ (a * epsilon) * (N : ℝ) ^ (a * (x.2.primeFactors.card : ℝ))) :=
      mul_lt_mul_of_pos_left hsr (Real.rpow_pos_of_pos hNpos _)
    _ = _ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring

/-- The complete actual rank <= 2 slice passes its OWN original L6
physical cap, rather than merely an auxiliary support cover. -/
theorem active_rank_two_original_cap {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : epsilon < 1 / 8)
    {policy : Policy} {p x : ℕ × ℕ} (hp : p ∈ source N eta)
    (hx : x ∈ factorPairs N epsilon policy p) (hrank : x.2.primeFactors.card ≤ 2) :
    (physical p x : ℝ) < (N : ℝ) ^ P5U6CausalLevelGeometry.physicalLevel
      (currentChenUpsilon6LogCoordinates N p 0) (currentChenUpsilon6LogCoordinates N p 1) := by
  have hprod := source_log_product hN hp
  have hcard : (x.2.primeFactors.card : ℝ) ≤ 2 := by exact_mod_cast hrank
  have hdomain := ((mem_currentChenUpsilon6RetainedSelector_log_iff hN _ eta p).mp
    (source_subset_closed N eta hp)).2.2.2
  have hlevel := original_level_gt hdomain
  apply (active_physical_lt_rank_power hN hp hx).trans_le
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  dsimp [a] at *
  linarith

/-- Exact physical residual, with the original selected pair divided
out. Above mu this is 57/64-(5/2)t-u, not 1/2-t-u. -/
theorem original_residual_power {N : ℕ} (hN : (1 : ℝ) < N)
    {eta : ℝ} {p : ℕ × ℕ} (hp : p ∈ source N eta) :
    (N : ℝ) ^ P5U6CausalLevelGeometry.residual (currentChenUpsilon6LogCoordinates N p) =
      (N : ℝ) ^ P5U6CausalLevelGeometry.physicalLevel
        (currentChenUpsilon6LogCoordinates N p 0) (currentChenUpsilon6LogCoordinates N p 1) /
          ((p.1 * p.2 : ℕ) : ℝ) := by
  rw [← P5U6CausalLevelGeometry.pair_product_power hN (source_subset_sixth N eta hp),
    ← Real.rpow_sub (zero_lt_one.trans hN)]
  congr 1
  unfold P5U6CausalLevelGeometry.residual
  ring

theorem active_rank_two_residual_cap {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : epsilon < 1 / 8)
    {policy : Policy} {p x : ℕ × ℕ} (hp : p ∈ source N eta)
    (hx : x ∈ factorPairs N epsilon policy p) (hrank : x.2.primeFactors.card ≤ 2) :
    ((x.1 * x.2 : ℕ) : ℝ) <
      (N : ℝ) ^ P5U6CausalLevelGeometry.residual (currentChenUpsilon6LogCoordinates N p) ∧
      2 ≤ P5U6CausalLevelGeometry.alpha (currentChenUpsilon6LogCoordinates N p) := by
  refine ⟨?_, (source_original_root hN heta hp).2⟩
  rw [original_residual_power hN hp]
  have hb : (0 : ℝ) < ((p.1 * p.2 : ℕ) : ℝ) := by
    rw [← P5U6CausalLevelGeometry.pair_product_power hN (source_subset_sixth N eta hp)]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans hN) _
  apply (lt_div_iff₀ hb).mpr
  simpa only [physical, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    active_rank_two_original_cap hN heta heps hp hx hrank

/-- Rank <= 3 has the original global 153/256 cap. This does NOT assert
that every such atom passes its smaller individual nonenhanced root. -/
theorem active_rank_three_global_cap {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : epsilon < 1 / 8)
    {policy : Policy} {p x : ℕ × ℕ} (hp : p ∈ source N eta)
    (hx : x ∈ factorPairs N epsilon policy p) (hrank : x.2.primeFactors.card ≤ 3) :
    (physical p x : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hprod := source_log_product hN hp
  have hcard : (x.2.primeFactors.card : ℝ) ≤ 3 := by exact_mod_cast hrank
  apply (active_physical_lt_rank_power hN hp hx).trans_le
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  dsimp [a] at *
  linarith

/-- Up to seven ACTUAL rough primes the physical modulus has a uniform
subunit cap. This weaker cap suffices for the two prime corrections. -/
theorem shortSupport_seven_cap {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : epsilon < 1 / 8)
    (policy : Policy) {q : ℕ} (hq : q ∈ shortSupport 7 N eta epsilon policy) :
    (q : ℝ) < (N : ℝ) ^ (15 / 16 : ℝ) := by
  obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx, hrank⟩ := Finset.mem_filter.mp hx
  have hprod := source_log_product hN hp
  have hcard : (x.2.primeFactors.card : ℝ) ≤ 7 := by exact_mod_cast hrank
  apply (active_physical_lt_rank_power hN hp hx).trans_le
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  dsimp [a] at *
  linarith

def shortCorrections (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ q ∈ shortSupport 7 N eta epsilon policy,
    sigma N eta epsilon policy q * P5CausalPrimeCorrectionPayment.atomCost N 1 q

def longCorrections (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ q ∈ support N eta epsilon policy \ shortSupport 7 N eta epsilon policy,
    sigma N eta epsilon policy q * P5CausalPrimeCorrectionPayment.atomCost N 1 q

/-- Both corrections and both signs are preserved in this exact split. -/
theorem primeCorrections_eq_short_add_long (N : ℕ) (eta epsilon : ℝ) (policy : Policy) :
    primeCorrections N eta epsilon policy =
      shortCorrections N eta epsilon policy + longCorrections N eta epsilon policy := by
  have htotal : primeCorrections N eta epsilon policy =
      ∑ q ∈ support N eta epsilon policy,
        sigma N eta epsilon policy q * P5CausalPrimeCorrectionPayment.atomCost N 1 q := by
    unfold primeCorrections
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    simp only [P5CausalPrimeCorrectionPayment.atomCost, Nat.one_mul, mul_add]
  have hsplit := Finset.sum_sdiff
    (f := fun q => sigma N eta epsilon policy q * P5CausalPrimeCorrectionPayment.atomCost N 1 q)
    (shortSupport_subset 7 N eta epsilon policy)
  change longCorrections N eta epsilon policy =
    (∑ q ∈ support N eta epsilon policy,
      sigma N eta epsilon policy q * P5CausalPrimeCorrectionPayment.atomCost N 1 q) -
        shortCorrections N eta epsilon policy at hsplit
  rw [← htotal] at hsplit
  linarith only [hsplit]

/-- Every remaining nonzero atom really has at least eight rough primes.
The policy is unchanged; no unsupported signed atom is discarded. -/
theorem long_active_has_eight_rough_primes {N : ℕ} {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ} (hq : q ∈ support N eta epsilon policy \ shortSupport 7 N eta epsilon policy)
    (hsigma : sigma N eta epsilon policy q ≠ 0) :
    ∃ p ∈ source N eta, ∃ x ∈ factorPairs N epsilon policy p,
      8 ≤ x.2.primeFactors.card ∧ physical p x = q := by
  obtain ⟨hqs, hqlong⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨⟨p, k⟩, hmark, hq⟩ := Finset.mem_image.mp hqs
  obtain ⟨hp, hk⟩ := Finset.mem_sigma.mp hmark
  have hrho : rho N epsilon policy p k ≠ 0 := by
    rw [← sigma_at_mark policy hwz (m := (⟨p, k⟩ : Mark))
      (Finset.mem_sigma.mpr ⟨hp, hk⟩), hq]
    exact hsigma
  have hactive : k ∈ P5CausalRhoQuotientBridge.active (policy p) N (enumerationCap N)
      (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N) (smallLevel N epsilon) :=
    Finset.mem_filter.mpr ⟨hk, hrho⟩
  obtain ⟨x, ⟨hx, hxk⟩, _⟩ := P5CausalRhoFactorization.active_unique_factors (policy p) N
    (enumerationCap N) (smallCutoff N epsilon) (P5CausalRhoQuotientBridge.cutoff N)
    (smallLevel N epsilon) hactive
  have hphys : physical p x = q := by
    change (p.1 * p.2) * (x.1 * x.2) = q
    rw [hxk]
    exact hq
  refine ⟨p, hp, x, hx, ?_, hphys⟩
  by_contra hn
  have hshort : x.2.primeFactors.card ≤ 7 := by omega
  exact hqlong (Finset.mem_biUnion.mpr ⟨p, hp,
    Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hshort⟩, hphys⟩⟩)

/-- Counting the actual physical support uses each modulus once. The
cost includes primes in the original selected pair b as well as in k. -/
theorem shortCorrections_le_power_log {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (heta : 0 ≤ eta) (heps : 0 < epsilon) (heps8 : epsilon < 1 / 8)
    (policy : Policy) :
    shortCorrections N eta epsilon policy ≤
      (2 / Real.log 2) * (N : ℝ) ^ (15 / 16 : ℝ) * Real.log (N : ℝ) := by
  have hwz := (attachment_gates hN heps heps8).2.2
  have hNnat : 1 ≤ N := by exact_mod_cast hN.le
  have hpow : 0 ≤ (N : ℝ) ^ (15 / 16 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hpowN : (N : ℝ) ^ (15 / 16 : ℝ) ≤ N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN.le (show (15 / 16 : ℝ) ≤ 1 by norm_num)
  have hsub : shortSupport 7 N eta epsilon policy ⊆
      Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (15 / 16 : ℝ))) := by
    intro q hq
    have hpos := (support_primitive_squarefree policy hwz
      (shortSupport_subset 7 N eta epsilon policy hq)).1
    exact Finset.mem_Icc.mpr ⟨hpos,
      (Nat.le_floor_iff hpow).mpr (shortSupport_seven_cap hN heta heps8 policy hq).le⟩
  have hcard : ((shortSupport 7 N eta epsilon policy).card : ℝ) ≤
      (N : ℝ) ^ (15 / 16 : ℝ) := by
    have hc : (shortSupport 7 N eta epsilon policy).card ≤
        Nat.floor ((N : ℝ) ^ (15 / 16 : ℝ)) := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hpow)
  have hB : 0 ≤ 2 * (Real.log (N : ℝ) / Real.log 2) := by
    exact mul_nonneg (by norm_num) (div_nonneg (Real.log_pos hN).le
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  calc
    shortCorrections N eta epsilon policy ≤
        ∑ _q ∈ shortSupport 7 N eta epsilon policy, 2 * (Real.log (N : ℝ) / Real.log 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hpos := (support_primitive_squarefree policy hwz
        (shortSupport_subset 7 N eta epsilon policy hq)).1
      have hqN : 1 * q ≤ N := by
        simpa only [Nat.one_mul] using
          (show q ≤ N by exact_mod_cast (shortSupport_seven_cap hN heta heps8 policy hq).le.trans hpowN)
      have hcost := P5CausalPrimeCorrectionPayment.atomCost_le_log hNnat (by norm_num : 0 < (1 : ℕ))
        hpos hqN
      have hsigma := (le_abs_self (sigma N eta epsilon policy q)).trans
        (sigma_abs_le_one policy hwz q)
      exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsigma
        (P5CausalPrimeCorrectionPayment.atomCost_nonneg N 1 q)).trans hcost
    _ = ((shortSupport 7 N eta epsilon policy).card : ℝ) *
        (2 * (Real.log (N : ℝ) / Real.log 2)) := by simp
    _ ≤ (N : ℝ) ^ (15 / 16 : ℝ) * (2 * (Real.log (N : ℝ) / Real.log 2)) :=
      mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by ring

/-- One threshold precedes the buffer, beta precision and ENTIRE policy.
The only cap in this theorem has been derived above on actual support. -/
theorem eventually_shortCorrections_paid (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ eta epsilon : ℝ, 0 ≤ eta → 0 < epsilon → epsilon < 1 / 8 →
      ∀ policy : Policy, shortCorrections N eta epsilon policy ≤ delta * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization (2 / Real.log 2)
    (15 / 16) 1 (by norm_num) delta hdelta, eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  intro eta epsilon heta heps heps8 policy
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (shortCorrections_le_power_log hNr heta heps heps8 policy).trans
    (by simpa only [pow_one] using hpaid)

/-- J's FULL original raw-density lower count, now with no correction
cost on ranks 0--7. The signed PP is untouched, and the literal higher
rank correction remains. In particular this asserts no L6 endpoint. -/
theorem exists_uniform_raw_count_short_corrections_paid
    (delta kappa epsilonMax : ℝ) (hdelta : 0 < delta) (hkappa : 0 < kappa)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ eta : ℝ, 0 ≤ eta → ∀ policy : Policy,
          rawMain N eta policy - delta * primeScale N + signedPP N eta epsilon policy -
            longCorrections N eta epsilon policy - kappa * singularNormalization N ≤
              currentChenUpsilon6 N (actualMask N) := by
  obtain ⟨epsilon, heps, heps8, hepsMax, N1, hN1, hraw⟩ :=
    exists_uniform_full_raw_count delta epsilonMax hdelta hepsilonMax
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (eventually_shortCorrections_paid kappa hkappa)
  refine ⟨epsilon, heps, heps8, hepsMax, max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN hEven eta heta policy
  have hcount := hraw N ((le_max_left _ _).trans hN) hEven eta heta policy
  have hpaid := hN2 N ((le_max_right _ _).trans hN) eta epsilon heta heps heps8 policy
  rw [primeCorrections_eq_short_add_long] at hcount
  linarith only [hcount, hpaid]

end
end ImbalancedChen.P5OriginalRetainedU6ActiveRankCap
