import ImbalancedChen.ActualRosserBoundaryExpansion
import ImbalancedChen.ActualPrimeBoxMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Order.WellFounded

/-!
# Arbitrary fixed odd prime boxes in the actual Rosser boundary

A decreasing tuple of length `2*k+1` is sent to its least prime and the
finset of the other `2*k` primes. Explicit exponent gates give every
alternating cubic prefix, the active total product, and the terminal
crossing at the literal natural level `ceil (N ^ beta)`. The zero-depth
case has an empty tail; positive `beta` supplies its active product test.

The tail cardinality records the rank, and strict order makes the boundary
map injective even across different boxes of the same rank. These facts
allow finite families and finite collections of ranks to enter one positive
boundary expansion without repeating its constant term.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory

/-- The primes preceding the terminal least coordinate. -/
def actualRosserOddTail {k : ℕ} (p : Fin (2 * k + 1) → ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin (2 * k) => p i.castSucc)

/-- The actual terminal-prime/boundary-tail map. -/
def actualRosserOddBoundaryMap {k : ℕ} (p : Fin (2 * k + 1) → ℕ) :
    Sigma (fun _ : ℕ => Finset ℕ) :=
  ⟨p (Fin.last (2 * k)), actualRosserOddTail p⟩

/-- Distinct tuple labels preserve the exact tail rank. -/
theorem actualRosserOddTail_card {k : ℕ} {p : Fin (2 * k + 1) → ℕ}
    (hp : Function.Injective p) : (actualRosserOddTail p).card = 2 * k := by
  rw [actualRosserOddTail, Finset.card_image_of_injective]
  · simp
  · exact hp.comp (Fin.castSucc_injective (2 * k))

/-- Product weights on the actual tail have no multiplicities. -/
theorem actualRosserOddTail_prod {k : ℕ} {p : Fin (2 * k + 1) → ℕ}
    (hp : Function.Injective p) (g : ℕ → ℝ) :
    (∏ r ∈ actualRosserOddTail p, g r) = ∏ i : Fin (2 * k), g (p i.castSucc) := by
  rw [actualRosserOddTail, Finset.prod_image]
  exact fun _ _ _ _ h => Fin.castSucc_injective (2 * k) (hp h)

theorem actualRosserOddTail_range {k : ℕ} (p : Fin (2 * k + 1) → ℕ) :
    Set.range p = (↑(actualRosserOddTail p) : Set ℕ) ∪ {p (Fin.last (2 * k))} := by
  ext r
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · exact Or.inr rfl
  · rintro (hr | hr)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨i.castSucc, rfl⟩
    · exact ⟨Fin.last (2 * k), hr.symm⟩

/-- The map is injective on every collection of decreasing tuples of one
fixed rank, including the empty-tail rank. -/
theorem actualRosserOddBoundaryMap_injOn_strictAnti {k : ℕ}
    (T : Finset (Fin (2 * k + 1) → ℕ)) (hT : ∀ p ∈ T, StrictAnti p) :
    Set.InjOn (actualRosserOddBoundaryMap (k := k)) (T : Set (Fin (2 * k + 1) → ℕ)) := by
  intro p hp r hr heq
  have hq : p (Fin.last (2 * k)) = r (Fin.last (2 * k)) := congrArg Sigma.fst heq
  have hs : actualRosserOddTail p = actualRosserOddTail r :=
    congrArg (fun z : Sigma (fun _ : ℕ => Finset ℕ) => z.2) heq
  apply ((hT p hp).range_inj (hT r hr)).mp
  rw [actualRosserOddTail_range p, actualRosserOddTail_range r, hs, hq]

/-- Equal actual boundary tails from injective tuples force equal ranks.
This is the disjointness certificate needed before combining different layers. -/
theorem actualRosserOddTail_rank_eq {k l : ℕ}
    {p : Fin (2 * k + 1) → ℕ} {r : Fin (2 * l + 1) → ℕ}
    (hp : Function.Injective p) (hr : Function.Injective r)
    (heq : actualRosserOddTail p = actualRosserOddTail r) : k = l := by
  have hc := congrArg Finset.card heq
  rw [actualRosserOddTail_card hp, actualRosserOddTail_card hr] at hc
  omega

private theorem odd_box_upper_le {k : ℕ} {a b : Fin (2 * k + 1) → ℝ} {u : ℝ}
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin (2 * k), b i.succ ≤ a i.castSucc) (hbu : b 0 ≤ u) :
    ∀ i, b i ≤ u := by
  have hb : Antitone b := Fin.antitone_iff_succ_le.mpr
    (fun i => (hsep i).trans (hab i.castSucc).le)
  exact fun i => (hb (Fin.zero_le i)).trans hbu

/-- All prefix tests and the terminal crossing are verified at the same
literal `ceil (N ^ beta)` used by the actual small Rosser coefficient.
Only finite geometric inequalities are assumed; no density estimate is used. -/
theorem actualRosserOddBox_mem_boundary
    (k N cap : ℕ) (hN : 1 < N) (a b : Fin (2 * k + 1) → ℝ) (u beta : ℝ)
    (hbeta : 0 < beta) (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin (2 * k), b i.succ ≤ a i.castSucc)
    (hbu : b 0 ≤ u)
    (hprod : (∑ i : Fin (2 * k), b i.castSucc) ≤ beta)
    (hprefix : ∀ i : Fin (2 * k), Even i.val →
      (∑ j : Fin (2 * k) with j.val < i.val, b j.castSucc) + 3 * b i.castSucc ≤ beta)
    (hshell : beta ≤ (∑ i : Fin (2 * k), a i.castSucc) +
      3 * a (Fin.last (2 * k)))
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ))
    {p : Fin (2 * k + 1) → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b) :
    p (Fin.last (2 * k)) ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) ∧
      actualRosserOddTail p ∈ actualUpperRosserBoundarySets N cap
        ((N : ℝ) ^ u) ((N : ℝ) ^ beta) (p (Fin.last (2 * k))) ∧
      (actualRosserOddTail p).card = 2 * k := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hm := mem_actualPrimeBoxTuples_iff.mp hp
  have hanti := actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) hsep hp
  have hP (i : Fin (2 * k + 1)) :
      p i ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) := by
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hcap]
    exact ⟨(hm i).1, (hm i).2.1, (hm i).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le (odd_box_upper_le hab hsep hbu i))⟩
  have hpPos (i : Fin (2 * k + 1)) : (0 : ℝ) < p i := by
    exact_mod_cast (hm i).1.pos
  have hprodLE (S : Finset (Fin (2 * k))) :
      (∏ i ∈ S, (p i.castSucc : ℝ)) ≤
        (N : ℝ) ^ (∑ i ∈ S, b i.castSucc) := by
    rw [Real.rpow_sum_of_pos hNpos]
    exact Finset.prod_le_prod (fun i _ => (hpPos _).le)
      (fun i _ => (hm i.castSucc).2.2.2.le)
  have htotalReal : (∏ i : Fin (2 * k), (p i.castSucc : ℝ)) < (N : ℝ) ^ beta := by
    by_cases hk : k = 0
    · subst k
      simpa using Real.one_lt_rpow hNreal hbeta
    · calc
        (∏ i : Fin (2 * k), (p i.castSucc : ℝ)) <
            ∏ i : Fin (2 * k), (N : ℝ) ^ b i.castSucc := by
          exact Finset.prod_lt_prod_of_nonempty (fun i _ => hpPos _)
            (fun i _ => (hm i.castSucc).2.2.2)
            ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        _ = (N : ℝ) ^ (∑ i : Fin (2 * k), b i.castSucc) :=
          (Real.rpow_sum_of_pos hNpos _ _).symm
        _ ≤ (N : ℝ) ^ beta := Real.rpow_le_rpow_of_exponent_le hNreal.le hprod
  have hprefixReal (i : Fin (2 * k)) (hi : Even i.val) :
      (∏ j : Fin (2 * k) with j.val < i.val, (p j.castSucc : ℝ)) *
          (p i.castSucc : ℝ) ^ 3 < (N : ℝ) ^ beta := by
    have hcube : (p i.castSucc : ℝ) ^ 3 < ((N : ℝ) ^ b i.castSucc) ^ 3 :=
      pow_lt_pow_left₀ (hm i.castSucc).2.2.2 (hpPos _).le (by decide)
    calc
      _ ≤ ((N : ℝ) ^ (∑ j : Fin (2 * k) with j.val < i.val, b j.castSucc)) *
          (p i.castSucc : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (hprodLE _) (by positivity)
      _ < ((N : ℝ) ^ (∑ j : Fin (2 * k) with j.val < i.val, b j.castSucc)) *
          ((N : ℝ) ^ b i.castSucc) ^ 3 :=
        mul_lt_mul_of_pos_left hcube (Real.rpow_pos_of_pos hNpos _)
      _ = (N : ℝ) ^ ((∑ j : Fin (2 * k) with j.val < i.val, b j.castSucc) +
          3 * b i.castSucc) := by
        rw [Real.rpow_add hNpos, show 3 * b i.castSucc = b i.castSucc * (3 : ℕ) by ring,
          Real.rpow_mul_natCast hNpos.le]
      _ ≤ (N : ℝ) ^ beta := Real.rpow_le_rpow_of_exponent_le hNreal.le (hprefix i hi)
  have hshellReal : (N : ℝ) ^ beta ≤
      (∏ i : Fin (2 * k), (p i.castSucc : ℝ)) * (p (Fin.last (2 * k)) : ℝ) ^ 3 := by
    calc
      (N : ℝ) ^ beta ≤ (N : ℝ) ^ ((∑ i : Fin (2 * k), a i.castSucc) +
          3 * a (Fin.last (2 * k))) :=
        Real.rpow_le_rpow_of_exponent_le hNreal.le hshell
      _ = (∏ i : Fin (2 * k), (N : ℝ) ^ a i.castSucc) *
          ((N : ℝ) ^ a (Fin.last (2 * k))) ^ 3 := by
        rw [Real.rpow_add hNpos, Real.rpow_sum_of_pos hNpos,
          show 3 * a (Fin.last (2 * k)) = a (Fin.last (2 * k)) * (3 : ℕ) by ring,
          Real.rpow_mul_natCast hNpos.le]
      _ ≤ _ := mul_le_mul
        (Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hNpos _).le)
          (fun i _ => (hm i.castSucc).2.2.1))
        (pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _)
          (hm (Fin.last (2 * k))).2.2.1 3) (by positivity) (by positivity)
  let l := List.ofFn (fun i : Fin (2 * k) => p i.castSucc)
  have hllen : l.length = 2 * k := List.length_ofFn
  have hlprod : (l.prod : ℝ) = ∏ i : Fin (2 * k), (p i.castSucc : ℝ) := by
    simp only [l, List.prod_ofFn, Nat.cast_prod]
  have hltake (r : ℕ) : ((l.take r).prod : ℝ) =
      ∏ i : Fin (2 * k) with i.val < r, (p i.castSucc : ℝ) := by
    simp only [l, List.prod_take_ofFn, Nat.cast_prod]
  have hlget (i : Fin l.length) :
      (l.get i : ℝ) = (p (Fin.cast hllen i).castSucc : ℝ) := by
    simp only [l, List.get_ofFn]
  have hlinj : Function.Injective (fun i : Fin (2 * k) => p i.castSucc) :=
    hanti.injective.comp (Fin.castSucc_injective (2 * k))
  have hlsorted : l.SortedGT := by
    apply List.sortedGT_iff_pairwise.mpr
    exact List.pairwise_ofFn.mpr (fun _ _ hij => hanti (Fin.castSucc_lt_castSucc_iff.mpr hij))
  have hlfinset : l.toFinset = actualRosserOddTail p := by
    ext r
    simp only [l, List.mem_toFinset, List.mem_ofFn, actualRosserOddTail,
      Finset.mem_image, Finset.mem_univ, true_and]
  have hsort : (actualRosserOddTail p).sort (· ≥ ·) = l := by
    rw [← hlfinset]
    exact (List.toFinset_sort (r := (· ≥ ·)) (List.nodup_ofFn.mpr hlinj)).mpr
      hlsorted.sortedGE.pairwise
  have hchain : LinearSieve.UpperRosserBoundaryChain (Nat.ceil ((N : ℝ) ^ beta))
      (p (Fin.last (2 * k))) l := by
    refine ⟨hlsorted, ?_, ?_, ?_, ?_⟩
    · rw [hllen]
      exact ⟨k, by omega⟩
    · apply Nat.lt_ceil.mpr
      rw [hlprod]
      exact htotalReal
    · intro i hi
      apply Nat.lt_ceil.mpr
      rw [Nat.cast_mul, Nat.cast_pow, hltake, hlget]
      exact hprefixReal (Fin.cast hllen i) hi
    · apply Nat.ceil_le.mpr
      rw [Nat.cast_mul, Nat.cast_pow, hlprod]
      exact hshellReal
  have hqnot : p (Fin.last (2 * k)) ∉ actualRosserOddTail p := by
    intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    exact (Fin.castSucc_ne_last i) (hanti.injective hi)
  have hqmin : ∀ r ∈ actualRosserOddTail p, p (Fin.last (2 * k)) ≤ r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hanti i.castSucc_lt_last).le
  have hboundary : LinearSieve.UpperRosserBoundarySet (Nat.ceil ((N : ℝ) ^ beta))
      (p (Fin.last (2 * k))) (actualRosserOddTail p) := by
    apply (LinearSieve.upperRosserBoundarySet_iff_sorted_chain hqnot
      (hm (Fin.last (2 * k))).1 hqmin).mpr
    rwa [hsort]
  refine ⟨hP _, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hboundary⟩,
    actualRosserOddTail_card hanti.injective⟩
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_filter.mpr ⟨hP _, hanti i.castSucc_lt_last⟩

end

end ImbalancedChen
