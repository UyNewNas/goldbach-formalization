import ImbalancedChen.P2Historical246SuccessorParentWindow
import ImbalancedChen.P2OriginalW2CountTupleReindex

/-!
SOURCE ONLY / UNEVALUATED. For an actual generated successor, identify
its inherited ceiling with its last appended prime and rewrite the H246
pair ceiling exception as a strict-order prime comparison. Equality at
the ceiling remains an exception. No exception sum is estimated here.
-/
namespace ImbalancedChen.P2Historical246SuccessorPrimeCeiling

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization
open P2Historical246PairCarrierPartition P2Historical246BoundedPairBridge
open P2Historical246SuccessorParentWindow P2OriginalHalfOpenProfileCarrier
open P2OriginalW2CountTupleReindex P2OriginalProfileThetaNormalization
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- The actual successor ceiling is the physical log exponent of a
specific prime in the same labelled tuple. -/
theorem successor_ceiling_is_prime {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c := by
  have hf := (advance m choice).source_facts hN he (advance_boxRows m choice hm) ht
  have hdiv (i : Fin (advance m choice).rank) : (t i).val ∣ parentProduct (oldWord t) := by
    rw [oldWord_product]
    unfold Part3.labelledProduct
    exact Finset.dvd_prod_of_mem (fun j => (t j).val) (Finset.mem_univ i)
  cases choice with
  | inl rule =>
      refine ⟨(t (Fin.last m.rank)).val, (hf.1 _).1, hdiv _, ?_⟩
      rfl
  | inr p =>
      rcases p with ⟨bank,piece⟩
      refine ⟨(t (Fin.last (m.rank+1))).val, (hf.1 _).1, hdiv _, ?_⟩
      rfl

/-- For positive primes, the physical logarithmic ceiling is exactly
the strict comparison of the original integer primes. -/
theorem physicalPrime_lt_iff {N a c : ℕ} (hN : 1 < N) (ha : 0 < a) (hc : 0 < c) :
    physicalPrime N a < physicalPrime N c ↔ a < c := by
  have h := normalizedLog_order hN (show (0 : ℝ) < 1 by norm_num) ![a,c] (by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hc)
  simpa [normalizedLog,actualPrimeTupleLog,physicalPrime] using h

/-- Each actual half-open pair already has small<large. For its inherited
prime ceiling, both strict physical-ceiling tests are therefore
equivalent to large<ceilingPrime. -/
theorem halfCarrier_orderedCeiling_iff {N c : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L) (hc : c.Prime)
    (j : Fin 36) (k : Fin 4) {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    orderedCeiling N (physicalPrime N c) p ↔ p 1 < c := by
  have hm := (pair_count_carrier_membership hN hd hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k p).mp hp
  have horder : p 0 < p 1 := hm.2.1
  have hbox := (Finset.mem_filter.mp hp).1
  have hp0 : 0 < p 0 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 0).1.pos
  have hp1 : 0 < p 1 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 1).1.pos
  have h0 := physicalPrime_lt_iff hN hp0 hc.pos
  have h1 := physicalPrime_lt_iff hN hp1 hc.pos
  unfold orderedCeiling
  constructor
  · intro h
    exact h1.mp h.2.2
  · intro h
    exact ⟨horder,h0.mpr (horder.trans h),h1.mpr h⟩

/-- Equality with the inherited prime is a genuine prefix collision:
its occurrence is retained in the earlier coprimality-failure bucket. -/
theorem equal_ceiling_not_bothCoprime {N c : ℕ} {old : List ℕ} {p : Pair}
    (hc : c.Prime) (hdiv : c ∣ parentProduct old) (heq : p 1 = c) :
    ¬ bothCoprime N old p := by
  intro hcop
  have hcnd : c ∣ N*parentProduct old := by
    obtain ⟨v,hv⟩ := hdiv
    refine ⟨N*v,?_⟩
    rw [hv]
    ring
  have hcc : c.Coprime (N*parentProduct old) := by simpa only [heq] using hcop.2
  have hc1 : c ∣ 1 := by
    have hg := Nat.dvd_gcd (dvd_refl c) hcnd
    change Nat.gcd c (N*parentProduct old) = 1 at hcc
    simpa only [hcc] using hg
  exact hc.ne_one (Nat.dvd_one.mp hc1)

theorem equal_ceiling_in_prefix_collision {N c : ℕ} {Q L chi : ℝ}
    {old : List ℕ} {j : Fin 36} {k : Fin 4} {p : Pair}
    (hc : c.Prime) (hdiv : c ∣ parentProduct old)
    (hp : p ∈ halfCarrier N L j k) (hi : interior N L j k p)
    (hparent : parentWindow N Q old chi) (heq : p 1 = c) :
    p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
      parentWindow N Q old chi ∧ ¬ bothCoprime N old p) := by
  exact Finset.mem_filter.mpr ⟨hp,hi,hparent,equal_ceiling_not_bothCoprime hc hdiv heq⟩

/-- The previously retained order/ceiling bucket is exactly the tuples
whose large prime is strictly above the actual ceiling prime. Equality
is retained in the prior prefix-collision class, never erased. -/
theorem ceiling_reject_filter_eq {N c : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L) (hc : c.Prime)
    (hdiv : c ∣ parentProduct old)
    (j : Fin 36) (k : Fin 4) :
    (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
      parentWindow N Q old (physicalPrime N c) ∧ bothCoprime N old p ∧
      ¬ orderedCeiling N (physicalPrime N c) p) =
    (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
      parentWindow N Q old (physicalPrime N c) ∧ bothCoprime N old p ∧ c < p 1) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp,hi,hparent,hcop,hfail⟩
    have hiff := halfCarrier_orderedCeiling_iff hN hd hL hQ hc j k hp
    refine ⟨hp,hi,hparent,hcop,?_⟩
    have hge : c ≤ p 1 := Nat.le_of_not_gt (fun hlt => hfail (hiff.mpr hlt))
    have hne : p 1 ≠ c := fun heq => (equal_ceiling_not_bothCoprime hc hdiv heq) hcop
    omega
  · rintro ⟨hp,hi,hparent,hcop,hgt⟩
    have hiff := halfCarrier_orderedCeiling_iff hN hd hL hQ hc j k hp
    refine ⟨hp,hi,hparent,hcop,?_⟩
    intro hceiling
    have hlt := hiff.mp hceiling
    omega

/-- The actual 246th row and its four ordered lanes retain the true old
H table, Q and all remaining signed terms. Only the ceiling predicate is
rewritten as the explicit integer-prime exception. -/
theorem successor_h246_tagged_prime_ceiling {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ c : ℕ, c.Prime ∧ c ∣ parentProduct (oldWord t) ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t = physicalPrime N c ∧
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
        (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        ∀ k : Fin 4,
          let Q := (N : ℝ)^nu
          let old := oldWord t
          let L := residualExponent N (parentProduct old) nu
          let chi := physicalPrime N c
          let S := halfCarrier N L j k
          let F := oldPairAtom N Q L (parentProduct old) j k
          pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
            (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
            (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
              ¬ bothCoprime N old p), F p) +
            (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
              bothCoprime N old p ∧ c < p 1), F p) +
            (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p)) := by
  obtain ⟨c,hc,hdiv,hchi⟩ := successor_ceiling_is_prime hN he m choice hm ht
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  obtain ⟨j,hp,hn,hlanes,hprofile⟩ := successor_h246_tagged_parent_free hN he hnu m choice hm ht hb
  refine ⟨c,hc,hdiv,hchi,j,hp,hn,hlanes,?_⟩
  intro k
  have h := hprofile k
  simp only [hchi] at h
  rw [ceiling_reject_filter_eq hN hd hL hQ hc hdiv j k] at h
  exact h

end
end ImbalancedChen.P2Historical246SuccessorPrimeCeiling
