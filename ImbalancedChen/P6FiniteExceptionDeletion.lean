import ImbalancedChen.RationalPowers
import ImbalancedChen.CurrentMainTheorem
import ImbalancedChen.SingularSeries

/-!
# P6: deletion of finitely many genuine real-exponent representations

SOURCE-ONLY DRAFT, UNCOMPILED. No analytic count bound is asserted here.
The supplied lower inequality concerns the actual `RealDb` count. The only
asymptotic theorem used below is the existing divergence of the concrete
`singularNormalization`; no count-divergence theorem is imported or reproved.

The finite sets index additive primes, so all cardinalities count distinct
representations once per additive prime, independently of factor witnesses.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- The genuine good additive primes remaining after deletion of `E`. -/
def retainedRealPrimes (b : ℝ) (N : ℕ) (E : Finset ℕ) : Finset ℕ := by
  classical
  exact realImbalancedPrimes b N \ E

@[simp] theorem mem_retainedRealPrimes {b : ℝ} {N p : ℕ} {E : Finset ℕ} :
    p ∈ retainedRealPrimes b N E ↔
      p ∈ realImbalancedPrimes b N ∧ p ∉ E := by
  classical
  exact Finset.mem_sdiff

/-- An exact partition: only exceptional primes already in the good set
are actually removed. -/
theorem realImbalancedPrimes_partition (b : ℝ) (N : ℕ) (E : Finset ℕ) :
    realImbalancedPrimes b N =
      retainedRealPrimes b N E ∪ (realImbalancedPrimes b N ∩ E) := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hpE : p ∈ E
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hp, hpE⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (mem_retainedRealPrimes.mpr ⟨hp, hpE⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mem_retainedRealPrimes.mp hp).1
    · exact (Finset.mem_inter.mp hp).1

/-- Retained and actually deleted good primes are disjoint. -/
theorem retainedRealPrimes_disjoint_deleted
    (b : ℝ) (N : ℕ) (E : Finset ℕ) :
    Disjoint (retainedRealPrimes b N E) (realImbalancedPrimes b N ∩ E) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpRet hpDel
  exact (mem_retainedRealPrimes.mp hpRet).2 (Finset.mem_inter.mp hpDel).2

/-- Exact counting identity for finite deletion of the actual `RealDb` set. -/
theorem RealDb_eq_retained_card_add_deleted_card
    (b : ℝ) (N : ℕ) (E : Finset ℕ) :
    RealDb b N = (retainedRealPrimes b N E).card +
      (realImbalancedPrimes b N ∩ E).card := by
  classical
  change (realImbalancedPrimes b N).card = _
  calc
    (realImbalancedPrimes b N).card =
        (retainedRealPrimes b N E ∪ (realImbalancedPrimes b N ∩ E)).card :=
      congrArg Finset.card (realImbalancedPrimes_partition b N E)
    _ = _ := Finset.card_union_of_disjoint
      (retainedRealPrimes_disjoint_deleted b N E)

/-- Deleting `E` costs at most its cardinality, even if some of its entries
are composite or never occur in the good set. -/
theorem RealDb_le_retained_card_add_exception_card
    (b : ℝ) (N : ℕ) (E : Finset ℕ) :
    RealDb b N ≤ (retainedRealPrimes b N E).card + E.card := by
  classical
  have hDel : (realImbalancedPrimes b N ∩ E).card ≤ E.card := by
    apply Finset.card_le_card
    intro p hp
    exact (Finset.mem_inter.mp hp).2
  have hPart := RealDb_eq_retained_card_add_deleted_card b N E
  omega

/-- The same genuine-count loss estimate in the real coefficient field. -/
theorem RealDb_cast_le_retained_card_add_exception_card
    (b : ℝ) (N : ℕ) (E : Finset ℕ) :
    (RealDb b N : ℝ) ≤ (retainedRealPrimes b N E).card + (E.card : ℝ) := by
  exact_mod_cast RealDb_le_retained_card_add_exception_card b N E

/-- A useful finite lower-bound transfer, without asymptotic assumptions. -/
theorem retained_card_cast_ge_sub_exception_card
    {b lower : ℝ} {N : ℕ} {E : Finset ℕ}
    (hLower : lower ≤ (RealDb b N : ℝ)) :
    lower - (E.card : ℝ) ≤ (retainedRealPrimes b N E).card := by
  have hLoss := RealDb_cast_le_retained_card_add_exception_card b N E
  linarith

/-- More good additive primes than exceptions force a surviving prime. -/
theorem retainedRealPrimes_nonempty_of_exception_card_lt
    {b : ℝ} {N : ℕ} {E : Finset ℕ}
    (hCount : E.card < RealDb b N) :
    (retainedRealPrimes b N E).Nonempty := by
  classical
  apply Finset.card_pos.mp
  have hLoss := RealDb_le_retained_card_add_exception_card b N E
  omega

/-- A surviving prime has the literal manuscript representation and avoids
`E`. The natural subtraction disappears using genuine good-set membership. -/
theorem representation_of_mem_retainedRealPrimes
    {b : ℝ} {N p : ℕ} {E : Finset ℕ}
    (hb : 0 ≤ b) (hp : p ∈ retainedRealPrimes b N E) :
    ∃ r q : ℕ, p ∉ E ∧ p < N ∧ Nat.Prime p ∧
      (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
      N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  obtain ⟨hGood, hAvoid⟩ := mem_retainedRealPrimes.mp hp
  obtain ⟨r, q, hpPrime, hr, hq, hEq, hPow⟩ :=
    exists_representation_of_mem_realImbalancedPrimes hb hGood
  exact ⟨r, q, hAvoid, (mem_realImbalancedPrimes.mp hGood).1,
    hpPrime, hr, hq, hEq, hPow⟩

/-- A genuine eventual lower inequality absorbs any uniformly bounded
finite deletion. This uses normalization growth directly, rather than an
assumption that the desired retained set is eventually nonempty. -/
theorem eventually_retained_nonempty_of_bounded_deletion
    {b delta : ℝ} (hdelta : 0 < delta)
    {exceptions : ℕ → Finset ℕ} {K : ℕ}
    (hExceptions : ∀ N : ℕ, (exceptions N).card ≤ K)
    (hLower : ∀ᶠ N : ℕ in Filter.atTop, Even N →
      delta * singularNormalization N ≤ (RealDb b N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (retainedRealPrimes b N (exceptions N)).Nonempty := by
  have hGrowth : ∀ᶠ N : ℕ in Filter.atTop,
      (K : ℝ) / delta < singularNormalization N :=
    tendsto_singularNormalization_atTop.eventually
      (Filter.eventually_gt_atTop ((K : ℝ) / delta))
  filter_upwards [hGrowth, hLower] with N hGrowthN hLowerN
  intro hEven
  have hLarge : (K : ℝ) < delta * singularNormalization N := by
    have h := (div_lt_iff₀ hdelta).mp hGrowthN
    nlinarith
  have hCountR : (K : ℝ) < (RealDb b N : ℝ) :=
    hLarge.trans_le (hLowerN hEven)
  have hCount : K < RealDb b N := by exact_mod_cast hCountR
  exact retainedRealPrimes_nonempty_of_exception_card_lt
    ((hExceptions N).trans_lt hCount)

/-- Fixed finite additive-prime exceptions are eventually avoidable under
an explicit positive lower bound for the actual normalized count. -/
theorem eventually_retained_nonempty_of_lower_bound
    {b delta : ℝ} (hdelta : 0 < delta) (E : Finset ℕ)
    (hLower : ∀ᶠ N : ℕ in Filter.atTop, Even N →
      delta * singularNormalization N ≤ (RealDb b N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (retainedRealPrimes b N E).Nonempty := by
  exact eventually_retained_nonempty_of_bounded_deletion hdelta
    (exceptions := fun _ => E) (K := E.card) (fun _ => le_rfl) hLower

/-- Finite-exception endpoint in literal factor-witness form, including the
prime-receiver case `r = 1`. The analytic input remains explicit. -/
theorem eventually_representation_avoiding_finite_of_lower_bound
    {b delta : ℝ} (hb : 0 ≤ b) (hdelta : 0 < delta) (E : Finset ℕ)
    (hLower : ∀ᶠ N : ℕ in Filter.atTop, Even N →
      delta * singularNormalization N ≤ (RealDb b N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      ∃ p r q : ℕ, p ∉ E ∧ p < N ∧ Nat.Prime p ∧
        (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  filter_upwards [eventually_retained_nonempty_of_lower_bound hdelta E hLower]
    with N hN
  intro hEven
  obtain ⟨p, hp⟩ := hN hEven
  obtain ⟨r, q, hRest⟩ := representation_of_mem_retainedRealPrimes hb hp
  exact ⟨p, r, q, hRest⟩

end

end ImbalancedChen.P6
