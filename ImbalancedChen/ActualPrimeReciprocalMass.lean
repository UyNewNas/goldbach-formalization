import ImbalancedChen.ChenPrimeHarmonicFinite
import ImbalancedChen.RoughPrimeUniverse
import ImbalancedChen.PowerErrorBudget
import MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogScale

/-!
# Actual reciprocal prime mass on fixed logarithmic cells

The carrier is exactly `N^a <= p < N^b`, with `p` prime and `p` not dividing
the same varying target `N`. Its enumeration cap is `ceil(N^b)`, so no
restriction `b <= 1` is necessary. The summand is the actual sieve density
`1/(p-1)`.

The proof pays separately for the target-prime deletion, the denominator
shift, and the two endpoint atoms. The remaining reciprocal-prime interval
limit is the pinned dependency's proved Mertens theorem. No prime-density
limit is an input and no infinite Rosser tail is estimated here.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Filter Topology

open MathlibNt.SieveTheory.PrimeReciprocalLogScale

/-- The actual local density on the complete target-linked power interval. -/
def actualPrimeReciprocalMass (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ b))
      ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / ((p : ℝ) - 1)

/-- A separate enumeration cap allows the target to remain `N`, even when
the upper endpoint exceeds it. -/
theorem roughPrimeFinset_ceil_eq_harmonic_filter (N : ℕ) (A U : ℝ) :
    roughPrimeFinset N (Nat.ceil U) A U =
      (chenPrimeHarmonicWindow (Nat.ceil U) A U).filter (fun p => ¬p ∣ N) := by
  classical
  ext p
  rw [mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil U)]
  simp only [chenPrimeHarmonicWindow, Finset.mem_filter, mem_chenPrimePrefix]
  constructor
  · rintro ⟨hp, hpN, hA, hU⟩
    have hpcap : p ≤ Nat.ceil U := by exact_mod_cast hU.le.trans (Nat.le_ceil U)
    exact ⟨⟨⟨hpcap, hp⟩, hA, hU⟩, hpN⟩
  · rintro ⟨⟨⟨_, hp⟩, hA, hU⟩, hpN⟩
    exact ⟨hp, hpN, hA, hU⟩

/-- The three finite corrections with independent target and enumeration
cap. This uses only the already proved finite inequalities. -/
theorem actualPrimeReciprocalWindow_difference_le
    (N : ℕ) {A U : ℝ} (hN : 0 < N) (hA : 2 ≤ A) (hAU : A < U) :
    |(∑ p ∈ roughPrimeFinset N (Nat.ceil U) A U, 1 / ((p : ℝ) - 1)) -
      ∑ p ∈ chenPrimeHarmonicSupplierWindow (Nat.ceil U) A U, 1 / (p : ℝ)| ≤
      2 * (Real.log (N : ℝ) / Real.log 2) / A + 6 / A := by
  classical
  let cap := Nat.ceil U
  let T := chenPrimeHarmonicWindow cap A U
  let X := ∑ p ∈ roughPrimeFinset N cap A U, 1 / ((p : ℝ) - 1)
  let Y := ∑ p ∈ T, 1 / ((p : ℝ) - 1)
  let Z := ∑ p ∈ T, 1 / (p : ℝ)
  let W := ∑ p ∈ chenPrimeHarmonicSupplierWindow cap A U, 1 / (p : ℝ)
  have hcentre : |X - Y| ≤ (2 / A) * (Real.log (N : ℝ) / Real.log 2) := by
    dsimp [X, Y, cap]
    rw [roughPrimeFinset_ceil_eq_harmonic_filter]
    apply chen_prime_centre_removal_bound hN T _ (by positivity)
    · intro p hp
      exact (mem_chenPrimePrefix.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp _
      have hAp : A ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2.1
      have hp1 : 0 < (p : ℝ) - 1 := by linarith
      rw [abs_of_pos (div_pos zero_lt_one hp1)]
      apply (div_le_div_iff₀ hp1 (by linarith : 0 < A)).mpr
      linarith
  have hshift : |Y - Z| ≤ 4 / A := by
    simpa only [mul_one] using
      chen_prime_reciprocal_shift_bound cap T (fun _ => 1) hA (by norm_num : (0 : ℝ) ≤ 1)
        (by
          intro p hp
          obtain ⟨hpCap, hpA, _hpU⟩ := Finset.mem_filter.mp hp
          have hpLe : (p : ℝ) ≤ cap := by exact_mod_cast (mem_chenPrimePrefix.mp hpCap).1
          exact Finset.mem_filter.mpr ⟨hpCap, hpA, by linarith⟩)
        (by intro p _hp; norm_num)
  have hend : |Z - W| ≤ 2 * (1 / A) := by
    apply chen_prime_window_endpoint_bound (chenPrimePrefix cap) (fun p => 1 / (p : ℝ))
      hAU (by positivity)
    intro p _hp hboundary
    have hpA : A ≤ (p : ℝ) := by
      rcases hboundary with h | h
      · rw [h]
      · rw [h]
        exact hAU.le
    have hpPos : 0 < (p : ℝ) := by linarith
    rw [abs_of_pos (div_pos zero_lt_one hpPos)]
    exact div_le_div_of_nonneg_left zero_le_one (by linarith) hpA
  change |X - W| ≤ _
  calc
    |X - W| ≤ |X - Y| + |Y - W| := abs_sub_le _ _ _
    _ ≤ |X - Y| + (|Y - Z| + |Z - W|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ (2 / A) * (Real.log (N : ℝ) / Real.log 2) + (4 / A + 2 * (1 / A)) :=
      add_le_add hcentre (add_le_add hshift hend)
    _ = _ := by ring

/-- The supplier's opposite half-open interval is exactly the genuine
Mertens interval, although its enumeration uses the ceiling rather than
the supplier's floor-plus-one. The retained upper inequality removes any
extra enumerated point. -/
theorem harmonicSupplierWindow_power_sum_eq_primeReciprocalLogInterval
    (N : ℕ) (a b : ℝ) :
    (∑ p ∈ chenPrimeHarmonicSupplierWindow (Nat.ceil ((N : ℝ) ^ b))
        ((N : ℝ) ^ a) ((N : ℝ) ^ b), 1 / (p : ℝ)) =
      primeReciprocalLogInterval N a b := by
  have hU : 0 ≤ (N : ℝ) ^ b := Real.rpow_nonneg (Nat.cast_nonneg N) b
  unfold primeReciprocalLogInterval
  apply Finset.sum_congr
  · ext p
    simp only [chenPrimeHarmonicSupplierWindow, Finset.mem_filter, mem_chenPrimePrefix,
      Finset.mem_range, rpowFloor, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨hpcap, hp⟩, hlo, hhi⟩
      exact ⟨(Nat.le_floor_iff hU).mpr hhi, hp, hlo, hhi⟩
    · rintro ⟨_hpfloor, hp, hlo, hhi⟩
      have hpcap : p ≤ Nat.ceil ((N : ℝ) ^ b) := by
        exact_mod_cast hhi.trans (Nat.le_ceil ((N : ℝ) ^ b))
      exact ⟨⟨hpcap, hp⟩, hlo, hhi⟩
  · intro p _hp
    rfl

/-- Explicit correction to the pinned reciprocal-prime interval on the
same target-dependent powers. No limiting estimate is used here. -/
theorem actualPrimeReciprocalMass_difference_le
    {N : ℕ} {a b : ℝ} (hN : 1 < N) (hab : a < b)
    (hA : 2 ≤ (N : ℝ) ^ a) :
    |actualPrimeReciprocalMass N a b - primeReciprocalLogInterval N a b| ≤
      2 * (Real.log (N : ℝ) / Real.log 2) / (N : ℝ) ^ a + 6 / (N : ℝ) ^ a := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hAU := Real.rpow_lt_rpow_of_exponent_lt hNR hab
  have h := actualPrimeReciprocalWindow_difference_le N (by omega) hA hAU
  rw [harmonicSupplierWindow_power_sum_eq_primeReciprocalLogInterval N a b] at h
  exact h

/-- For every pair of fixed positive exponents the actual target-deleted
`1/(p-1)` mass tends to the logarithmic interval mass. No restriction on
the size of b relative to one, and no parity restriction on N, is needed. -/
theorem tendsto_actualPrimeReciprocalMass {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => actualPrimeReciprocalMass N a b)
      atTop (𝓝 (Real.log (b / a))) := by
  have hlog := tendsto_nat_log_pow_div_rpow 1 ha
  have hinv := tendsto_nat_log_pow_div_rpow 0 ha
  have herr : Tendsto (fun N : ℕ =>
      2 * (Real.log (N : ℝ) / Real.log 2) / (N : ℝ) ^ a + 6 / (N : ℝ) ^ a)
      atTop (𝓝 0) := by
    have h := (hlog.const_mul (2 / Real.log 2)).add (hinv.const_mul 6)
    simp only [pow_one, pow_zero, mul_zero, zero_add] at h
    convert h using 1
    ext N
    ring
  have hbound : ∀ᶠ N : ℕ in atTop,
      |actualPrimeReciprocalMass N a b - primeReciprocalLogInterval N a b| ≤
        2 * (Real.log (N : ℝ) / Real.log 2) / (N : ℝ) ^ a + 6 / (N : ℝ) ^ a := by
    have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    filter_upwards [hpower.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_ge_atTop (2 : ℕ)] with N hA hN
    exact actualPrimeReciprocalMass_difference_le (by omega) hab hA
  have hdiff : Tendsto (fun N : ℕ =>
      actualPrimeReciprocalMass N a b - primeReciprocalLogInterval N a b)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using herr.neg) herr
    · filter_upwards [hbound] with N hN
      linarith [(abs_le.mp hN).1]
    · filter_upwards [hbound] with N hN
      exact (abs_le.mp hN).2
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (tendsto_primeReciprocalLogInterval ha hab)

end

end ImbalancedChen
