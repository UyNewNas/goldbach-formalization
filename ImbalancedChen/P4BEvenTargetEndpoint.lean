import ImbalancedChen.ActualUpperCountingInputs

/-!
# Removing the inclusive product endpoint at an even target

SOURCE ONLY / YELLOW / UNCOMPILED.

For `b ≥ 1/2`, an even ordered bad receiver is at most six. Thus every
even target `N ≥ 8` is absent from the literal half-product source, for
every real lower cutoff `T`. The proof uses the actual strict power
boundary and the prime-factor splitting theorem, which includes squares.
It requires no roughness gate, limiting estimate or analytic premise.

The result is stronger than the requested range `1/2 ≤ b < 1`: the upper
restriction on b is unnecessary for this finite endpoint fact. The exact
strict-range and filter identities below preserve the existing source.
-/

namespace ImbalancedChen.P4BEvenTargetEndpoint

noncomputable section
open Filter Topology

/-- If `b ≥ 1/2`, an even member of the actual ordered bad region has
smaller prime factor two and larger factor below four, hence size at most
six. No distinct-prime assumption excludes the prime square four. -/
theorem even_realOrderedBadReceiver_le_six
    {b : ℝ} {m : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hmEven : Even m) (hbad : RealOrderedBadReceiver b m) : m ≤ 6 := by
  obtain ⟨r, q, hr, hq, hmul, hrq, hpow⟩ := hbad
  have htwo : 2 ∣ r * q := by
    rw [← hmul]
    exact even_iff_two_dvd.mp hmEven
  have hrTwo : r = 2 := by
    rcases (prime_dvd_halfProduct_iff Nat.prime_two hr hq).mp htwo with h | h
    · exact h.symm
    · have hrLower := hr.two_le
      omega
  have hpowTwo : (q : ℝ) ^ b < 2 := by simpa only [hrTwo, Nat.cast_ofNat] using hpow
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_le
  have hqPower : (q : ℝ) ≤ ((q : ℝ) ^ b) ^ (2 : ℕ) := by
    calc
      (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (q : ℝ) ^ (b * 2) :=
        Real.rpow_le_rpow_of_exponent_le hqOne (by linarith)
      _ = ((q : ℝ) ^ b) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  have hsq : ((q : ℝ) ^ b) ^ (2 : ℕ) < (2 : ℝ) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hpowTwo (Real.rpow_nonneg (Nat.cast_nonneg q) b) (by decide)
  have hqFour : (q : ℝ) < 4 := by nlinarith only [hqPower, hsq]
  have hqFourNat : q < 4 := by exact_mod_cast hqFour
  rw [hmul, hrTwo]
  omega

/-- The inclusive target endpoint is impossible for an even target at
least eight, independently of the real lower cutoff. -/
theorem target_not_mem_realHalfProductSource
    {b T : ℝ} {N : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hEven : Even N) (hN : 8 ≤ N) :
    N ∉ realHalfProductSource b N T := by
  intro hmem
  have hsmall := even_realOrderedBadReceiver_le_six hb hEven
    (mem_realHalfProductSource.mp hmem).2.2
  omega

/-- Every actual source member has the literal strict upper endpoint at
such an even target. The lower endpoint remains the original real cutoff. -/
theorem source_member_lt_target
    {b T : ℝ} {N m : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hEven : Even N) (hN : 8 ≤ N)
    (hm : m ∈ realHalfProductSource b N T) : m < N := by
  have hmle := (mem_realHalfProductSource.mp hm).1
  have hmne : m ≠ N := by
    intro heq
    apply target_not_mem_realHalfProductSource hb hEven hN
    simpa only [heq] using hm
  omega

/-- Exact agreement with the strict `[0,N)` carrier; no endpoint atom is
discarded from the actual source in this identity. -/
theorem realHalfProductSource_eq_strict_range
    {b T : ℝ} {N : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hEven : Even N) (hN : 8 ≤ N) :
    realHalfProductSource b N T =
      (Finset.range N).filter
        (fun m : ℕ => T ≤ (m : ℝ) ∧ RealOrderedBadReceiver b m) := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨_hmle, hcut, hbad⟩ := mem_realHalfProductSource.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (source_member_lt_target hb hEven hN hm), hcut, hbad⟩
  · intro hm
    obtain ⟨hmrange, hcut, hbad⟩ := Finset.mem_filter.mp hm
    exact mem_realHalfProductSource.mpr
      ⟨(Finset.mem_range.mp hmrange).le, hcut, hbad⟩

/-- The explicit strict-target filter on the actual source is redundant. -/
theorem source_filter_lt_target_eq_self
    {b T : ℝ} {N : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hEven : Even N) (hN : 8 ≤ N) :
    (realHalfProductSource b N T).filter (fun m : ℕ => m < N) =
      realHalfProductSource b N T := by
  classical
  apply Finset.filter_eq_self.mpr
  intro m hm
  exact source_member_lt_target hb hEven hN hm

/-- At these even targets, the retained original bad receivers need only
the prime-partner filter. This removes the already impossible product
endpoint while preserving the exact additive-prime condition. -/
theorem retainedRealBadReceivers_eq_source_prime_filter
    {b T : ℝ} {N : ℕ} (hb : (1 / 2 : ℝ) ≤ b)
    (hEven : Even N) (hN : 8 ≤ N) :
    retainedRealBadReceivers b N T =
      (realHalfProductSource b N T).filter (fun m : ℕ => Nat.Prime (N - m)) := by
  classical
  rw [retainedRealBadReceivers_eq_realHalfProductSource_filter]
  apply Finset.filter_congr
  intro m hm
  have hlt := source_member_lt_target hb hEven hN hm
  simp only [hlt, true_and]

/-- Eventual manuscript-cutoff endpoint exclusion. The manuscript parameter
is arbitrary; its sign and growth are irrelevant to this finite parity fact. -/
theorem eventually_manuscript_target_not_mem
    {b : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (kappa : ℝ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      N ∉ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with N hN
  intro hEven
  exact target_not_mem_realHalfProductSource hb hEven hN

/-- Eventual exact strict-range consistency at the manuscript cutoff. -/
theorem eventually_manuscript_source_eq_strict_range
    {b : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (kappa : ℝ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) =
        (Finset.range N).filter (fun m : ℕ =>
          manuscriptHalfProductCutoff kappa N ≤ (m : ℝ) ∧
            RealOrderedBadReceiver b m) := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with N hN
  intro hEven
  exact realHalfProductSource_eq_strict_range hb hEven hN

end
end ImbalancedChen.P4BEvenTargetEndpoint
