import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.ActualPrimeBoxMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.FinRange
import Mathlib.Order.WellFounded

/-!
# Fixed even prime boxes in the actual lower Rosser boundary

A decreasing tuple of length `2*k+2` is sent to its least prime and the
finset of the other `2*k+1` primes. Odd-index cubic tests and the terminal
crossing are proved at the literal natural level `ceil (N ^ beta)`.
The lowest rank is a genuine two-prime box with a singleton boundary tail;
it has no internal cubic test. Tail cardinality separates different ranks.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory

/-- The primes preceding the terminal least coordinate. -/
def actualRosserEvenTail {k : ℕ} (p : Fin (2 * k + 2) → ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : Fin (2 * k + 1) => p i.castSucc)

/-- The actual terminal-prime/boundary-tail map. -/
def actualRosserEvenBoundaryMap {k : ℕ} (p : Fin (2 * k + 2) → ℕ) :
    Sigma (fun _ : ℕ => Finset ℕ) :=
  ⟨p (Fin.last (2 * k + 1)), actualRosserEvenTail p⟩

/-- Distinct tuple labels preserve the exact tail rank. -/
theorem actualRosserEvenTail_card {k : ℕ} {p : Fin (2 * k + 2) → ℕ}
    (hp : Function.Injective p) : (actualRosserEvenTail p).card = 2 * k + 1 := by
  rw [actualRosserEvenTail, Finset.card_image_of_injective]
  · simp
  · exact hp.comp (Fin.castSucc_injective (2 * k + 1))

/-- Product weights on the actual tail have no multiplicities. -/
theorem actualRosserEvenTail_prod {k : ℕ} {p : Fin (2 * k + 2) → ℕ}
    (hp : Function.Injective p) (g : ℕ → ℝ) :
    (∏ r ∈ actualRosserEvenTail p, g r) = ∏ i : Fin (2 * k + 1), g (p i.castSucc) := by
  rw [actualRosserEvenTail, Finset.prod_image]
  exact fun _ _ _ _ h => Fin.castSucc_injective (2 * k + 1) (hp h)

theorem actualRosserEvenTail_range {k : ℕ} (p : Fin (2 * k + 2) → ℕ) :
    Set.range p = (↑(actualRosserEvenTail p) : Set ℕ) ∪ {p (Fin.last (2 * k + 1))} := by
  ext r
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    · exact Or.inr rfl
  · rintro (hr | hr)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨i.castSucc, rfl⟩
    · exact ⟨Fin.last (2 * k + 1), hr.symm⟩

/-- The map is injective on every collection of decreasing tuples of one
fixed rank, including the singleton-tail rank. -/
theorem actualRosserEvenBoundaryMap_injOn_strictAnti {k : ℕ}
    (T : Finset (Fin (2 * k + 2) → ℕ)) (hT : ∀ p ∈ T, StrictAnti p) :
    Set.InjOn (actualRosserEvenBoundaryMap (k := k)) (T : Set (Fin (2 * k + 2) → ℕ)) := by
  intro p hp r hr heq
  have hq : p (Fin.last (2 * k + 1)) = r (Fin.last (2 * k + 1)) := congrArg Sigma.fst heq
  have hs : actualRosserEvenTail p = actualRosserEvenTail r :=
    congrArg (fun z : Sigma (fun _ : ℕ => Finset ℕ) => z.2) heq
  apply ((hT p hp).range_inj (hT r hr)).mp
  rw [actualRosserEvenTail_range p, actualRosserEvenTail_range r, hs, hq]

/-- Equal actual boundary tails from injective tuples force equal ranks.
This is the disjointness certificate needed before combining different layers. -/
theorem actualRosserEvenTail_rank_eq {k l : ℕ}
    {p : Fin (2 * k + 2) → ℕ} {r : Fin (2 * l + 2) → ℕ}
    (hp : Function.Injective p) (hr : Function.Injective r)
    (heq : actualRosserEvenTail p = actualRosserEvenTail r) : k = l := by
  have hc := congrArg Finset.card heq
  rw [actualRosserEvenTail_card hp, actualRosserEvenTail_card hr] at hc
  omega

private theorem even_box_upper_le {k : ℕ} {a b : Fin (2 * k + 2) → ℝ} {u : ℝ}
    (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin (2 * k + 1), b i.succ ≤ a i.castSucc) (hbu : b 0 ≤ u) :
    ∀ i, b i ≤ u := by
  have hb : Antitone b := Fin.antitone_iff_succ_le.mpr
    (fun i => (hsep i).trans (hab i.castSucc).le)
  exact fun i => (hb (Fin.zero_le i)).trans hbu

/-- All prefix tests and the terminal crossing are verified at the same
literal `ceil (N ^ beta)` used by the actual small Rosser coefficient.
Only finite geometric inequalities are assumed; no density estimate is used. -/
theorem actualRosserEvenBox_mem_boundary
    (k N cap : ℕ) (hN : 1 < N) (a b : Fin (2 * k + 2) → ℝ) (u beta : ℝ)
    (_hbeta : 0 < beta) (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin (2 * k + 1), b i.succ ≤ a i.castSucc)
    (hbu : b 0 ≤ u)
    (hprod : (∑ i : Fin (2 * k + 1), b i.castSucc) ≤ beta)
    (hprefix : ∀ i : Fin (2 * k + 1), Odd i.val →
      (∑ j : Fin (2 * k + 1) with j.val < i.val, b j.castSucc) + 3 * b i.castSucc ≤ beta)
    (hshell : beta ≤ (∑ i : Fin (2 * k + 1), a i.castSucc) +
      3 * a (Fin.last (2 * k + 1)))
    (hcap : (N : ℝ) ^ u ≤ (cap : ℝ))
    {p : Fin (2 * k + 2) → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b) :
    p (Fin.last (2 * k + 1)) ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) ∧
      actualRosserEvenTail p ∈
        (((actualSmallPrimeFinset N cap ((N : ℝ) ^ u)).filter
          (fun q => p (Fin.last (2 * k + 1)) < q)).powerset.filter
            (LinearSieve.LowerRosserBoundarySet (Nat.ceil ((N : ℝ) ^ beta))
              (p (Fin.last (2 * k + 1))))) ∧
      (actualRosserEvenTail p).card = 2 * k + 1 := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  have hm := mem_actualPrimeBoxTuples_iff.mp hp
  have hanti := actualPrimeBoxTuples_strictAnti (by omega : 1 ≤ N) hsep hp
  have hP (i : Fin (2 * k + 2)) :
      p i ∈ actualSmallPrimeFinset N cap ((N : ℝ) ^ u) := by
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hcap]
    exact ⟨(hm i).1, (hm i).2.1, (hm i).2.2.2.trans_le
      (Real.rpow_le_rpow_of_exponent_le hNreal.le (even_box_upper_le hab hsep hbu i))⟩
  have hpPos (i : Fin (2 * k + 2)) : (0 : ℝ) < p i := by
    exact_mod_cast (hm i).1.pos
  have hprodLE (S : Finset (Fin (2 * k + 1))) :
      (∏ i ∈ S, (p i.castSucc : ℝ)) ≤
        (N : ℝ) ^ (∑ i ∈ S, b i.castSucc) := by
    rw [Real.rpow_sum_of_pos hNpos]
    exact Finset.prod_le_prod (fun i _ => (hpPos _).le)
      (fun i _ => (hm i.castSucc).2.2.2.le)
  have htotalReal : (∏ i : Fin (2 * k + 1), (p i.castSucc : ℝ)) < (N : ℝ) ^ beta := by
    calc
      (∏ i : Fin (2 * k + 1), (p i.castSucc : ℝ)) <
          ∏ i : Fin (2 * k + 1), (N : ℝ) ^ b i.castSucc := by
        exact Finset.prod_lt_prod_of_nonempty (fun i _ => hpPos _)
          (fun i _ => (hm i.castSucc).2.2.2)
          ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      _ = (N : ℝ) ^ (∑ i : Fin (2 * k + 1), b i.castSucc) :=
        (Real.rpow_sum_of_pos hNpos _ _).symm
      _ ≤ (N : ℝ) ^ beta := Real.rpow_le_rpow_of_exponent_le hNreal.le hprod
  have hprefixReal (i : Fin (2 * k + 1)) (hi : Odd i.val) :
      (∏ j : Fin (2 * k + 1) with j.val < i.val, (p j.castSucc : ℝ)) *
          (p i.castSucc : ℝ) ^ 3 < (N : ℝ) ^ beta := by
    have hcube : (p i.castSucc : ℝ) ^ 3 < ((N : ℝ) ^ b i.castSucc) ^ 3 :=
      pow_lt_pow_left₀ (hm i.castSucc).2.2.2 (hpPos _).le (by decide)
    calc
      _ ≤ ((N : ℝ) ^ (∑ j : Fin (2 * k + 1) with j.val < i.val, b j.castSucc)) *
          (p i.castSucc : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (hprodLE _) (by positivity)
      _ < ((N : ℝ) ^ (∑ j : Fin (2 * k + 1) with j.val < i.val, b j.castSucc)) *
          ((N : ℝ) ^ b i.castSucc) ^ 3 :=
        mul_lt_mul_of_pos_left hcube (Real.rpow_pos_of_pos hNpos _)
      _ = (N : ℝ) ^ ((∑ j : Fin (2 * k + 1) with j.val < i.val, b j.castSucc) +
          3 * b i.castSucc) := by
        rw [Real.rpow_add hNpos, show 3 * b i.castSucc = b i.castSucc * (3 : ℕ) by ring,
          Real.rpow_mul_natCast hNpos.le]
      _ ≤ (N : ℝ) ^ beta := Real.rpow_le_rpow_of_exponent_le hNreal.le (hprefix i hi)
  have hshellReal : (N : ℝ) ^ beta ≤
      (∏ i : Fin (2 * k + 1), (p i.castSucc : ℝ)) * (p (Fin.last (2 * k + 1)) : ℝ) ^ 3 := by
    calc
      (N : ℝ) ^ beta ≤ (N : ℝ) ^ ((∑ i : Fin (2 * k + 1), a i.castSucc) +
          3 * a (Fin.last (2 * k + 1))) :=
        Real.rpow_le_rpow_of_exponent_le hNreal.le hshell
      _ = (∏ i : Fin (2 * k + 1), (N : ℝ) ^ a i.castSucc) *
          ((N : ℝ) ^ a (Fin.last (2 * k + 1))) ^ 3 := by
        rw [Real.rpow_add hNpos, Real.rpow_sum_of_pos hNpos,
          show 3 * a (Fin.last (2 * k + 1)) = a (Fin.last (2 * k + 1)) * (3 : ℕ) by ring,
          Real.rpow_mul_natCast hNpos.le]
      _ ≤ _ := mul_le_mul
        (Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hNpos _).le)
          (fun i _ => (hm i.castSucc).2.2.1))
        (pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le _)
          (hm (Fin.last (2 * k + 1))).2.2.1 3) (by positivity) (by positivity)
  let l := List.ofFn (fun i : Fin (2 * k + 1) => p i.castSucc)
  have hlinj : Function.Injective (fun i : Fin (2 * k + 1) => p i.castSucc) :=
    hanti.injective.comp (Fin.castSucc_injective (2 * k + 1))
  have hlsorted : l.SortedGT := by
    apply List.sortedGT_iff_pairwise.mpr
    exact List.pairwise_ofFn.mpr (fun _ _ hij => hanti (Fin.castSucc_lt_castSucc_iff.mpr hij))
  have hlfinset : l.toFinset = actualRosserEvenTail p := by
    ext r
    simp only [l, List.mem_toFinset, List.mem_ofFn, actualRosserEvenTail,
      Finset.mem_image, Finset.mem_univ, true_and]
  have hsort : (actualRosserEvenTail p).sort (· ≥ ·) = l := by
    rw [← hlfinset]
    exact (List.toFinset_sort (r := (· ≥ ·)) (List.nodup_ofFn.mpr hlinj)).mpr
      hlsorted.sortedGE.pairwise
  have hchain : LinearSieve.LowerRosserBoundaryChain (Nat.ceil ((N : ℝ) ^ beta))
      (p (Fin.last (2 * k + 1))) l := by
    refine ⟨hlsorted, ?_, ?_, ?_, ?_⟩
    · simp [l]
    · apply Nat.lt_ceil.mpr
      simpa only [l, List.prod_ofFn, Nat.cast_prod] using htotalReal
    · intro i hi
      have hil : i.val < 2 * k + 1 := by simpa [l] using i.isLt
      apply Nat.lt_ceil.mpr
      simp only [l, List.prod_take_ofFn, List.get_ofFn,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
      convert hprefixReal ⟨i.val, hil⟩ (Nat.odd_iff.mpr (Nat.not_even_iff.mp hi)) using 1
      all_goals rfl
    · apply Nat.ceil_le.mpr
      simpa only [l, List.prod_ofFn, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow] using hshellReal
  have hqnot : p (Fin.last (2 * k + 1)) ∉ actualRosserEvenTail p := by
    intro hq
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    exact (Fin.castSucc_ne_last i) (hanti.injective hi)
  have hqmin : ∀ r ∈ actualRosserEvenTail p, p (Fin.last (2 * k + 1)) ≤ r := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hanti i.castSucc_lt_last).le
  have hboundary : LinearSieve.LowerRosserBoundarySet (Nat.ceil ((N : ℝ) ^ beta))
      (p (Fin.last (2 * k + 1))) (actualRosserEvenTail p) := by
    apply (LinearSieve.lowerRosserBoundarySet_iff_sorted_chain hqnot
      (hm (Fin.last (2 * k + 1))).1 hqmin).mpr
    rwa [hsort]
  refine ⟨hP _, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hboundary⟩,
    actualRosserEvenTail_card hanti.injective⟩
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact Finset.mem_filter.mpr ⟨hP _, hanti i.castSucc_lt_last⟩

end

end ImbalancedChen
