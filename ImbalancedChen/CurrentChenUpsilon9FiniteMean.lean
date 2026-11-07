import ImbalancedChen.CurrentChenUpsilon9PanAggregate
import ImbalancedChen.CurrentChenUpsilon9UnitBudget

/-!
# The actual ninth count and its paid switched density main term

The prefix prime fibre uses the supplier's literal closed product bound
`a*q <= N`, including its possible receiver zero.  The original switched
prime fibre has `a*q < N`.  It is enlarged only after the complete actual
upper Rosser divisor sum has been proved nonnegative at every receiver.

Small original prime receivers are counted by injective complementation
inside each positive multiplier fibre.  Their cost, the actual unit fibres,
the genuine coprimality defect and the full signed Pan error are paid
separately.  The remaining main term contains the same actual upper Rosser
coefficient and the actual li mass.  Its density and harmonic asymptotics,
and the ordinary switched factor eight, are not assumptions or conclusions
of this finite-mean module.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

/-- The exact native Pan prime carrier, before any receiver sieve.  The
endpoint a*q=N remains in this source. -/
def currentChenUpsilon9PrefixPrimeFibre (N a : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun q => Nat.Prime q ∧ a * q ≤ N

/-- Divisibility of the nonnegative shifted receiver is exactly the
native AP filter, including the closed endpoint with receiver zero. -/
theorem currentChenUpsilon9PrefixPrimeFibre_divisor_card (N a d : ℕ) :
    ((currentChenUpsilon9PrefixPrimeFibre N a).filter
      (fun q => d ∣ N - a * q)).card = primesInAPBelow N a d N := by
  unfold primesInAPBelow
  congr 1
  ext q
  simp only [currentChenUpsilon9PrefixPrimeFibre, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, hprime, hle⟩, hd⟩
    exact ⟨hq, hprime, hle, (dvd_sub_iff_modEq_of_le hle).mp hd⟩
  · rintro ⟨hq, hprime, hle, hAP⟩
    exact ⟨⟨hq, hprime, hle⟩, (dvd_sub_iff_modEq_of_le hle).mpr hAP⟩

/-- Finite Fubini on the actual closed prefix source, with the complete
signed Rosser coefficient retained. -/
theorem currentChenUpsilon9_prefix_sum_upperDivisorSum
    (N a cap : ℕ) (z L : ℝ) :
    (∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
      supportedDivisorSum (actualSmallRosserSupport N cap z)
        (actualSmallRosserPlus N cap z L) (N - a * q)) =
      ∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserPlus N cap z L d * (primesInAPBelow N a d N : ℝ) := by
  simp only [supportedDivisorSum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [currentChenUpsilon9PrefixPrimeFibre_divisor_card]
  ring

private theorem currentChenUpsilon9_upperDivisorSum_nonneg
    (N cap : ℕ) (z L : ℝ) (hL : 1 < L) (hzL : z ≤ L) (n : ℕ) :
    0 ≤ supportedDivisorSum (actualSmallRosserSupport N cap z)
      (actualSmallRosserPlus N cap z L) n := by
  have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL n).2
  have hi : 0 ≤ (if Nat.Coprime (actualSmallPrimeProduct N cap z) n then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  exact hi.trans h

private theorem currentChenUpsilon9_prime_coprime_actualProduct
    (N cap : ℕ) (z : ℝ) {P : ℕ} (hP : Nat.Prime P) (hzP : z ≤ (P : ℝ)) :
    Nat.Coprime (actualSmallPrimeProduct N cap z) P := by
  rw [actualSmallPrimeProduct, Nat.coprime_prod_left_iff]
  intro p hp
  have hpd := mem_actualSmallPrimeFinset.mp hp
  apply hpd.2.1.coprime_iff_not_dvd.mpr
  intro hd
  have heq : p = P := (Nat.prime_dvd_prime_iff_eq hpd.2.1 hP).mp hd
  have hlt : (p : ℝ) < (P : ℝ) := hpd.2.2.2.trans_le hzP
  exact hlt.ne (by exact_mod_cast heq)

/-- The original strict prime fibre is bounded by the whole nonnegative
upper divisor sum on the true closed Pan carrier and its small-P loss.
No sign restriction on any individual Rosser coefficient is used. -/
theorem currentChenUpsilon9_switchedPrimeFibre_card_le_upperDivisorSum_add_cap
    (N a cap : ℕ) (ha : 0 < a) (z L : ℝ) (hL : 1 < L) (hzL : z ≤ L) :
    ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ) ≤
      (∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
        supportedDivisorSum (actualSmallRosserSupport N cap z)
          (actualSmallRosserPlus N cap z L) (N - a * q)) + (Nat.ceil z : ℝ) := by
  let F := currentChenUpsilon9SwitchedPrimeFibre N a
  let large := F.filter (fun q => z ≤ ((N - a * q : ℕ) : ℝ))
  let small := F.filter (fun q => ¬ z ≤ ((N - a * q : ℕ) : ℝ))
  have hlargeSubset : large ⊆ currentChenUpsilon9PrefixPrimeFibre N a := by
    intro q hq
    have hF := (Finset.mem_filter.mp hq).1
    obtain ⟨hqN, hprime, hlt, _⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_filter.mpr ⟨hqN, hprime, hlt.le⟩
  have hlarge : (large.card : ℝ) ≤
      ∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
        supportedDivisorSum (actualSmallRosserSupport N cap z)
          (actualSmallRosserPlus N cap z L) (N - a * q) := by
    calc
      _ = ∑ _q ∈ large, (1 : ℝ) := by simp
      _ ≤ ∑ q ∈ large, supportedDivisorSum (actualSmallRosserSupport N cap z)
          (actualSmallRosserPlus N cap z L) (N - a * q) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hF, hcut⟩ := Finset.mem_filter.mp hq
        have hP := (Finset.mem_filter.mp hF).2.2.2
        have hprime := (mem_chenAdditivePrimeCarrier.mp hP).2.1
        have hcop := currentChenUpsilon9_prime_coprime_actualProduct N cap z hprime hcut
        have h := (actualSmallRosser_sandwich_nat N cap z L hL hzL (N - a * q)).2
        rwa [if_pos hcop] at h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hlargeSubset
        (fun q _ _ => currentChenUpsilon9_upperDivisorSum_nonneg N cap z L hL hzL (N - a * q))
  have hsmall : small.card ≤ Nat.ceil z := by
    calc
      _ ≤ (Finset.range (Nat.ceil z)).card := by
        apply Finset.card_le_card_of_injOn (fun q : ℕ => N - a * q)
        · intro q hq
          have hcut := (Finset.mem_filter.mp hq).2
          exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (lt_of_not_ge hcut))
        · intro q hq r hr heq
          have hqF := (Finset.mem_filter.mp hq).1
          have hrF := (Finset.mem_filter.mp hr).1
          have hqN := (Finset.mem_filter.mp hqF).2.2.1
          have hrN := (Finset.mem_filter.mp hrF).2.2.1
          change N - a * q = N - a * r at heq
          have hprod : a * q = a * r := by omega
          exact Nat.eq_of_mul_eq_mul_left ha hprod
      _ = _ := Finset.card_range _
  have hpartition : (F.card : ℝ) = (large.card : ℝ) + (small.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := F) (fun q => z ≤ ((N - a * q : ℕ) : ℝ))).symm
  have hsmallR : (small.card : ℝ) ≤ (Nat.ceil z : ℝ) := by exact_mod_cast hsmall
  change (F.card : ℝ) ≤ _
  linarith only [hpartition, hlarge, hsmallR]

/-- Summing the literal prefix fibres preserves every actual multiplier
once, and still uses the supplier's closed product endpoint. -/
theorem currentChenUpsilon9_product_sum_upperDivisorSum
    (N cap : ℕ) (z L : ℝ) :
    (∑ a ∈ currentChenUpsilon9PrefixProducts N,
      ∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
        supportedDivisorSum (actualSmallRosserSupport N cap z)
          (actualSmallRosserPlus N cap z L) (N - a * q)) =
      ∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserPlus N cap z L d * currentChenUpsilon9PrefixAPCount N d := by
  simp_rw [currentChenUpsilon9_prefix_sum_upperDivisorSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [currentChenUpsilon9PrefixAPCount, Finset.mul_sum]

private theorem currentChenUpsilon9_upper_sum_eq_active
    (B : ℝ) (N cap : ℕ) (z : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d * G d) =
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d * G d := by
  rw [currentChenUpsilon9PanActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ panModulusCutoff N B
  · simp only [hd, if_true]
  · have hz : actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d = 0 := by
      by_contra hn
      have hactive := (actualSmallRosserPlus_active hn).2.1
      have hdlt : d < panModulusCutoff N B + 1 := by exact_mod_cast hactive
      omega
    simp only [hd, if_false, hz, zero_mul]

/-- The actual density of the same complete upper Rosser coefficient.
This is an explicit reciprocal-totient sum, with no density bound assumed. -/
def currentChenUpsilon9SwitchedUpperDensity (B : ℝ) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRosserSupport N cap z,
    actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d /
      (Nat.totient d : ℝ)

/-- Exact density, signed coprimality correction, and signed Pan error
for one and the same actual upper coefficient. -/
theorem currentChenUpsilon9_upper_AP_sum_eq_main_errors
    (B : ℝ) {N : ℕ} (hN : (1 : ℝ) ≤ N) (cap : ℕ) (z : ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
        currentChenUpsilon9PrefixAPCount N d) =
      currentChenUpsilon9LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z -
        currentChenUpsilon9CoprimeGateError N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)
          (currentChenUpsilon9PanActive B N cap z) +
        currentChenUpsilon9PanRosserError B N cap z := by
  have hgate : currentChenUpsilon9CoprimeGateError N cap z
      ((panModulusCutoff N B + 1 : ℕ) : ℝ) (actualSmallRosserSupport N cap z) =
      currentChenUpsilon9CoprimeGateError N cap z
        ((panModulusCutoff N B + 1 : ℕ) : ℝ) (currentChenUpsilon9PanActive B N cap z) :=
    currentChenUpsilon9_upper_sum_eq_active B N cap z _
  rw [← hgate]
  calc
    _ = ∑ d ∈ actualSmallRosserSupport N cap z,
        ((currentChenUpsilon9LiMainMass N *
          (actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d /
            (Nat.totient d : ℝ)) -
          actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
            (currentChenUpsilon9CoprimeMainDefect N d / (Nat.totient d : ℝ))) +
          actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
            currentChenUpsilon9PanError N d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [currentChenUpsilon9_prefixAPCount_eq_main_sub_defect_add_error hN
        (actualSmallRosserSupport_coprime_target N cap z hd).symm]
      ring
    _ = _ := by
      simp only [currentChenUpsilon9SwitchedUpperDensity, currentChenUpsilon9CoprimeGateError,
        currentChenUpsilon9PanRosserError, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]

/-- The actual ninth count has this finite main-and-errors bound.  All
prime, unit, endpoint, centre and coefficient multiplicities are retained. -/
theorem currentChenUpsilon9_le_upper_density_main_add_errors
    (B : ℝ) {N : ℕ} (hN : (1 : ℝ) ≤ N) (cap : ℕ) (z : ℝ)
    (hL : 1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ))
    (hzL : z ≤ ((panModulusCutoff N B + 1 : ℕ) : ℝ)) :
    currentChenUpsilon9 N ≤
      currentChenUpsilon9LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z -
        currentChenUpsilon9CoprimeGateError N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)
          (currentChenUpsilon9PanActive B N cap z) +
        currentChenUpsilon9PanRosserError B N cap z +
        ((currentChenUpsilon9PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) +
        ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  have hsource := currentChenUpsilon9_le_switched_prime_fibres_add_unitFibres N
  have hrows : (∑ a ∈ currentChenUpsilon9PrefixProducts N,
      ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) ≤
      (∑ a ∈ currentChenUpsilon9PrefixProducts N,
        ∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
          supportedDivisorSum (actualSmallRosserSupport N cap z)
            (actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)) (N - a * q)) +
        ((currentChenUpsilon9PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) := by
    have h := Finset.sum_le_sum (s := currentChenUpsilon9PrefixProducts N)
      (fun a ha => currentChenUpsilon9_switchedPrimeFibre_card_le_upperDivisorSum_add_cap
        N a cap (currentChenUpsilon9PrefixProducts_data ha).1 z
          ((panModulusCutoff N B + 1 : ℕ) : ℝ) hL hzL)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using h
  rw [currentChenUpsilon9_product_sum_upperDivisorSum,
    currentChenUpsilon9_upper_AP_sum_eq_main_errors B hN cap z] at hrows
  linarith only [hsource, hrows]

/-- The actual product image, followed by the small-prime receiver cap,
has exponent 309/500+1/5=409/500<1.  Both ceiling losses are paid. -/
theorem currentChenUpsilon9_small_prime_cost_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((currentChenUpsilon9PrefixProducts N).card : ℝ) *
      (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
        4 * (N : ℝ) ^ (409 / 500 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hsubset : currentChenUpsilon9PrefixProducts N ⊆
      Finset.range (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ))) := by
    intro a ha
    exact Finset.mem_range.mpr
      (Nat.lt_ceil.mpr (currentChenUpsilon9PrefixProducts_power_bounds hN ha).2)
  have hcard : ((currentChenUpsilon9PrefixProducts N).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) : ℝ) := by
    have h := Finset.card_le_card hsubset
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hprodOne : 1 ≤ (N : ℝ) ^ (309 / 500 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hsmallOne : 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hprodCeil : (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (309 / 500 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (309 / 500 : ℝ))
    linarith
  have hsmallCeil : (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (1 / 5 : ℝ))
    linarith
  calc
    _ ≤ (2 * (N : ℝ) ^ (309 / 500 : ℝ)) * (2 * (N : ℝ) ^ (1 / 5 : ℝ)) :=
      mul_le_mul (hcard.trans hprodCeil) hsmallCeil (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hNp.le _))
    _ = _ := by
      rw [show (409 / 500 : ℝ) = 309 / 500 + 1 / 5 by norm_num, Real.rpow_add hNp]
      ring

private theorem eventually_currentChenUpsilon9_panLevel_sieveCutoff
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ) ∧
      (N : ℝ) ^ (1 / 5 : ℝ) ≤ ((panModulusCutoff N B + 1 : ℕ) : ℝ) ∧
      panModulusCutoff N B ≤ N := by
  filter_upwards [eventually_pan_conductor_bounds B hB,
    eventually_pan_log_rpow_le_rpow B (3 / 10) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with N hb hlogPower hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hb.1
  have hden : 0 < Real.log (N : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos _
  have hQ : 1 ≤ panModulusCutoff N B := hb.2.1.trans hb.2.2.1
  have hlevel : 1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < panModulusCutoff N B + 1 by omega)
  have hcut : (N : ℝ) ^ (1 / 5 : ℝ) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogPower (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp, show (1 / 5 : ℝ) + 3 / 10 = 1 / 2 by norm_num]
  have hfloor : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B <
      ((panModulusCutoff N B + 1 : ℕ) : ℝ) := by
    simpa only [panModulusCutoff, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B)
  exact ⟨hlevel, hcut.trans hfloor.le, hb.2.2.2.2⟩

/-- One proved Pan exponent precedes every epsilon.  The actual ninth
count is bounded by its same-coefficient switched density main term,
with all Pan, coprimality, small-P and unit errors paid in full. -/
theorem exists_currentChenUpsilon9_le_switched_density_main :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
        currentChenUpsilon9 N ≤
          currentChenUpsilon9LiMainMass N *
            currentChenUpsilon9SwitchedUpperDensity B N cap ((N : ℝ) ^ (1 / 5 : ℝ)) +
              ε * singularNormalization N := by
  obtain ⟨B, hB, hPan⟩ := exists_currentChenUpsilon9_panRosserError_budget
  refine ⟨B, hB, ?_⟩
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hPan δ hδ,
    eventually_currentChenUpsilon9_abs_coprimeGateError_le_singularNormalization δ hδ,
    eventually_powerLog_le_singularNormalization 4 (409 / 500) 0 (by norm_num) δ hδ,
    eventually_currentChenUpsilon9_unitFibres_le_singularNormalization δ hδ,
    eventually_currentChenUpsilon9_panLevel_sieveCutoff B hB,
    eventually_ge_atTop (1 : ℕ)] with N hPanN hGateN hSmallN hUnitN hlevel hN
  intro cap
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let z : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let L : ℝ := ((panModulusCutoff N B + 1 : ℕ) : ℝ)
  let S := currentChenUpsilon9PanActive B N cap z
  have hS : S ⊆ Finset.Icc 1 N := by
    intro d hd
    have h := Finset.mem_Icc.mp (currentChenUpsilon9PanActive_subset B N cap z hd)
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hlevel.2.2⟩
  have hGate := hGateN cap z L S hS
  dsimp only [L, S] at hGate
  have hPanCost := hPanN cap z
  have hSmall : ((currentChenUpsilon9PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) ≤
      δ * singularNormalization N := by
    apply (currentChenUpsilon9_small_prime_cost_le_power hNr).trans
    simpa only [pow_zero, mul_one] using hSmallN
  have hfinite := currentChenUpsilon9_le_upper_density_main_add_errors B hNr cap z
    hlevel.1 hlevel.2.1
  have hPanHi := (abs_le.mp hPanCost).2
  have hGateLo := (abs_le.mp hGate).1
  have htotal : 4 * (δ * singularNormalization N) = ε * singularNormalization N := by
    dsimp [δ]
    ring
  change currentChenUpsilon9 N ≤
    currentChenUpsilon9LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z +
      ε * singularNormalization N
  nlinarith only [hfinite, hPanHi, hGateLo, hSmall, hUnitN, htotal]

end

end ImbalancedChen
