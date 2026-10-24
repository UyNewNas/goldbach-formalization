import ImbalancedChen.CurrentMainTheorem

/-!
# Exact good-receiver reindexing of the real imbalanced count

Source-only draft, uncompiled. The finite receiver source is indexed once by
the natural receiver, independently of its factor witnesses. Complementation
`m ↦ N - m` is an actual equivalence with the accepted additive-prime source,
and the finite receiver cardinality is exactly `RealDb b N` for every real b.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Accepted prime and semiprime receivers are positive, for every exponent. -/
theorem realImbalancedReceiver_pos {b : ℝ} {m : ℕ}
    (hm : RealImbalancedReceiver b m) : 0 < m := by
  rcases hm with hprime | ⟨r, q, hr, hq, hm, _⟩
  · exact hprime.pos
  · rw [hm]
    exact mul_pos hr.pos hq.pos

/-- Good receivers with the original strict endpoint and a prime additive
partner. Positivity follows from the accepted receiver predicate itself. -/
def realImbalancedReceivers (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun m =>
    RealImbalancedReceiver b m ∧ Nat.Prime (N - m)

@[simp] theorem mem_realImbalancedReceivers {b : ℝ} {N m : ℕ} :
    m ∈ realImbalancedReceivers b N ↔
      m < N ∧ RealImbalancedReceiver b m ∧ Nat.Prime (N - m) := by
  classical
  simp only [realImbalancedReceivers, Finset.mem_filter, Finset.mem_range]

/-- An accepted additive prime gives a member of the receiver finite set. -/
theorem sub_mem_realImbalancedReceivers_of_mem_realImbalancedPrimes
    {b : ℝ} {N p : ℕ} (hp : p ∈ realImbalancedPrimes b N) :
    N - p ∈ realImbalancedReceivers b N := by
  rcases mem_realImbalancedPrimes.mp hp with ⟨hpN, hpprime, hgood⟩
  have hp0 : 0 < p := hpprime.pos
  have hinv : N - (N - p) = p := by omega
  exact mem_realImbalancedReceivers.mpr
    ⟨by omega, hgood, by simpa only [hinv] using hpprime⟩

/-- A receiver member gives an accepted additive-prime member. The receiver's
positivity is essential for the new strict endpoint `N - m < N`. -/
theorem sub_mem_realImbalancedPrimes_of_mem_realImbalancedReceivers
    {b : ℝ} {N m : ℕ} (hm : m ∈ realImbalancedReceivers b N) :
    N - m ∈ realImbalancedPrimes b N := by
  rcases mem_realImbalancedReceivers.mp hm with ⟨hmN, hgood, hpprime⟩
  have hm0 : 0 < m := realImbalancedReceiver_pos hgood
  have hinv : N - (N - m) = m := by omega
  exact mem_realImbalancedPrimes.mpr
    ⟨by omega, hpprime, by simpa only [hinv] using hgood⟩

/-- Membership in the additive-prime source is equivalent to membership of
the complement in the good-receiver source; no external endpoint hypothesis. -/
theorem mem_realImbalancedPrimes_iff_sub_mem_realImbalancedReceivers
    {b : ℝ} {N p : ℕ} :
    p ∈ realImbalancedPrimes b N ↔ N - p ∈ realImbalancedReceivers b N := by
  constructor
  · exact sub_mem_realImbalancedReceivers_of_mem_realImbalancedPrimes
  · intro hm
    have hpos : 0 < N - p :=
      realImbalancedReceiver_pos (mem_realImbalancedReceivers.mp hm).2.1
    have hinv : N - (N - p) = p := by omega
    simpa only [hinv] using
      sub_mem_realImbalancedPrimes_of_mem_realImbalancedReceivers hm

/-- The converse indexing statement also holds without a supplied endpoint. -/
theorem mem_realImbalancedReceivers_iff_sub_mem_realImbalancedPrimes
    {b : ℝ} {N m : ℕ} :
    m ∈ realImbalancedReceivers b N ↔ N - m ∈ realImbalancedPrimes b N := by
  constructor
  · exact sub_mem_realImbalancedPrimes_of_mem_realImbalancedReceivers
  · intro hp
    have hpos : 0 < N - m := (mem_realImbalancedPrimes.mp hp).2.1.pos
    have hinv : N - (N - m) = m := by omega
    simpa only [hinv] using
      sub_mem_realImbalancedReceivers_of_mem_realImbalancedPrimes hp

/-- Complementation is involutive on the accepted additive-prime source. -/
theorem sub_sub_eq_of_mem_realImbalancedPrimes {b : ℝ} {N p : ℕ}
    (hp : p ∈ realImbalancedPrimes b N) : N - (N - p) = p := by
  have hpN := (mem_realImbalancedPrimes.mp hp).1
  omega

/-- Complementation is involutive on the good-receiver source. -/
theorem sub_sub_eq_of_mem_realImbalancedReceivers {b : ℝ} {N m : ℕ}
    (hm : m ∈ realImbalancedReceivers b N) : N - (N - m) = m := by
  have hmN := (mem_realImbalancedReceivers.mp hm).1
  omega

/-- An explicit equivalence of the two finite source types, with both maps
given by natural subtraction from N and both inverse laws proved above. -/
def realImbalancedPrimeReceiverEquiv (b : ℝ) (N : ℕ) :
    {p : ℕ // p ∈ realImbalancedPrimes b N} ≃
      {m : ℕ // m ∈ realImbalancedReceivers b N} where
  toFun p := ⟨N - p.val,
    sub_mem_realImbalancedReceivers_of_mem_realImbalancedPrimes p.property⟩
  invFun m := ⟨N - m.val,
    sub_mem_realImbalancedPrimes_of_mem_realImbalancedReceivers m.property⟩
  left_inv p := by
    apply Subtype.ext
    exact sub_sub_eq_of_mem_realImbalancedPrimes p.property
  right_inv m := by
    apply Subtype.ext
    exact sub_sub_eq_of_mem_realImbalancedReceivers m.property

/-- Exact finite cardinality, proved by the complement maps in both
directions. No factor-witness count or factor-of-two adjustment occurs. -/
theorem RealDb_eq_realImbalancedReceivers_card (b : ℝ) (N : ℕ) :
    RealDb b N = (realImbalancedReceivers b N).card := by
  unfold RealDb
  refine Finset.card_bij' (fun p _ => N - p) (fun m _ => N - m)
    (fun _ hp => sub_mem_realImbalancedReceivers_of_mem_realImbalancedPrimes hp)
    (fun _ hm => sub_mem_realImbalancedPrimes_of_mem_realImbalancedReceivers hm)
    ?_ ?_
  · intro p hp
    exact sub_sub_eq_of_mem_realImbalancedPrimes hp
  · intro m hm
    exact sub_sub_eq_of_mem_realImbalancedReceivers hm

theorem realImbalancedReceivers_card_eq_RealDb (b : ℝ) (N : ℕ) :
    (realImbalancedReceivers b N).card = RealDb b N := by
  exact (RealDb_eq_realImbalancedReceivers_card b N).symm

end

end ImbalancedChen.P6
