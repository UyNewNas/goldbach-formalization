import ImbalancedChen.P2EnhancedReceiverRoughPurification
import ImbalancedChen.P2EnhancedCollisionWeightedBudget
import MathlibNt.Wu2008DoubleSieve.LocalProductTail

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The new repeat and center events, while the receiver is still prime.
The complete divisor is d*l.prod. A center fibre retains the WHOLE list,
not its product image. P's purification and the previous collision
payment are imported, not re-proved. Arbitrary z and filtered subfamilies
allow the original bad-Gamma5 gate with its inherited cutoff as well.
-/

namespace ImbalancedChen.P2EnhancedExactExceptionFinite
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedReceiverRoughPurification P2EnhancedSwitchedUnsiftedSource
open P2EnhancedCollisionWeightedBudget P2EnhancedOrderedReciprocalBudget
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open scoped Classical BigOperators

/-- The existing exact floor estimate also covers D>N: every floor is zero. -/
theorem repeat_card_power {N d D : ℕ} {eta z : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hD : 0 < D) (hdD : d ∣ D)
    (heta : 0 < eta)
    (hrough : ∀ p ∈ D.primeFactors, (N : ℝ)^eta ≤ (p : ℝ)) :
    ((repeatReceiver N d D z).card : ℝ) ≤
      (1/eta)*(N : ℝ)/((D : ℝ)*(N : ℝ)^eta) := by
  have hf : ((repeatReceiver N d D z).card : ℝ) ≤
      ∑ p ∈ D.primeFactors, ((N/(D*p) : ℕ) : ℝ) := by
    exact_mod_cast repeat_card_le_floor hN he hD hdD
  by_cases hDN : D ≤ N
  · exact hf.trans (omega3_bad_floor_sum_le (by omega) hD hDN heta hrough)
  · have hz : (∑ p ∈ D.primeFactors, ((N/(D*p) : ℕ) : ℝ)) = 0 := by
      apply sum_eq_zero
      intro p hp
      have hp1 := (Nat.prime_of_mem_primeFactors hp).one_lt.le
      have hlarge : N < D*p := (Nat.lt_of_not_ge hDN).trans_le
        (by simpa using Nat.mul_le_mul_left D hp1)
      rw [Nat.div_eq_of_lt hlarge, Nat.cast_zero]
    rw [hz] at hf
    exact hf.trans (by positivity)

/-- Sum the actual repeat event, preserving 1/d and every ordered label. -/
theorem repeat_sum_le {N d M r : ℕ} {eta a f : ℝ}
    (S : Finset (List ℕ)) (z : List ℕ → ℝ)
    (hS : S ⊆ secondFunctionalMotherTuples (primeWindow M a f) r)
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hold : ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ a) (hupper : f ≤ (N : ℝ)) :
    (∑ l ∈ S, ((repeatReceiver N d (d*l.prod) (z l)).card : ℝ)) ≤
      collisionScale N d eta * (1+Real.log N)^r := by
  have hscale := collisionScale_nonneg N d heta
  calc
    _ ≤ ∑ l ∈ S, collisionScale N d eta * (1/(l.prod : ℝ)) := by
      apply sum_le_sum
      intro l hl
      have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (hS hl)
      have hp : 0 < l.prod := List.prod_pos
        (fun p hp => (mem_primeWindow.mp (ht.2.2 p hp)).1.pos)
      have h := repeat_card_power (z := z l) hN he (mul_pos hd hp)
        (dvd_mul_right d l.prod) heta (complete_product_rough hd hold hcut (hS hl))
      convert h using 1
      simp only [collisionScale, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) r,
        collisionScale N d eta * (1/(l.prod : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => mul_nonneg hscale (by positivity))
    _ = collisionScale N d eta *
        ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) r,
          1/(l.prod : ℝ) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tuple_reciprocal_le_power _ _ (window_reciprocal_budget N M a f hupper)) hscale

/-- For ONE prime receiver, the complete ordered list injects into its
large prime-divisor coordinates. No unweighted product image is used. -/
theorem center_fibre_le {N d M r ell : ℕ} {eta a f : ℝ}
    (S : Finset (List ℕ)) (z : List ℕ → ℝ)
    (hS : S ⊆ secondFunctionalMotherTuples (primeWindow M a f) r)
    (hN : 4 ≤ N) (he : Even N) (heta : 0 < eta)
    (hcut : (N : ℝ)^eta ≤ a) :
    (((S.filter (fun l => ell ∈ centerReceiver N d (d*l.prod) (z l))).card) : ℝ) ≤
      (1/eta)^r := by
  let F := S.filter (fun l => ell ∈ centerReceiver N d (d*l.prod) (z l))
  change (F.card : ℝ) ≤ _
  by_cases hF : F.Nonempty
  · obtain ⟨l, hl⟩ := hF
    have hlt := receiver_lt hN he (mem_filter.mp (mem_filter.mp hl).2).1
    apply omega3_prime_labels_card_le F (coordinates r) ?_ (by omega)
      (Nat.sub_pos_of_lt hlt) (Nat.sub_le N ell) heta
    · intro l hl l' hl' hcoords
      exact HighNonunit.list_eq_of_getD
        ((secondFunctionalMother_tuple_mem _ _ _).mp (hS (mem_filter.mp hl).1)).1
        ((secondFunctionalMother_tuple_mem _ _ _).mp (hS (mem_filter.mp hl').1)).1 hcoords
    · intro l hl j
      obtain ⟨hlS, hell⟩ := mem_filter.mp hl
      have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (hS hlS)
      have hj : j.val < l.length := by rw [ht.1]; exact j.isLt
      have hmem : coordinates r l j ∈ l := by
        change l.getD j.val 0 ∈ l
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hw := mem_primeWindow.mp (ht.2.2 _ hmem)
      have hdiv : d*l.prod ∣ N-ell :=
        (mem_filter.mp (mem_filter.mp hell).1).2.2.1
      exact ⟨hw.1, ((List.dvd_prod hmem).trans (dvd_mul_left l.prod d)).trans hdiv,
        hcut.trans hw.2.2.1⟩
  · rw [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero]
    positivity

/-- Regroup the incidence relation by receiver before applying the
native multiplicity estimate. Each labelled list remains a summand. -/
theorem center_sum_le {N d M r : ℕ} {eta a f : ℝ}
    (S : Finset (List ℕ)) (z : List ℕ → ℝ)
    (hS : S ⊆ secondFunctionalMotherTuples (primeWindow M a f) r)
    (hN : 4 ≤ N) (he : Even N) (heta : 0 < eta)
    (hcut : (N : ℝ)^eta ≤ a) :
    (∑ l ∈ S, ((centerReceiver N d (d*l.prod) (z l)).card : ℝ)) ≤
      (1/eta)^r * Real.log N / Real.log 2 := by
  have hNpos : 0 < N := by omega
  have hrow (l : List ℕ) :
      ((centerReceiver N d (d*l.prod) (z l)).card : ℝ) =
        ∑ ell ∈ N.primeFactors,
          if ell ∈ centerReceiver N d (d*l.prod) (z l) then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    have hf : N.primeFactors.filter
        (fun ell => ell ∈ centerReceiver N d (d*l.prod) (z l)) =
        centerReceiver N d (d*l.prod) (z l) := by
      ext ell
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨center_subset_primeFactors hNpos h, h⟩⟩
    rw [hf]
    simp
  have hcard : (N.primeFactors.card : ℝ) ≤ Real.log N / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (primeFactors_card_mul_log_two_le N hNpos)
  calc
    _ = ∑ ell ∈ N.primeFactors,
        (((S.filter (fun l => ell ∈ centerReceiver N d (d*l.prod) (z l))).card) : ℝ) := by
      simp_rw [hrow]
      rw [sum_comm]
      apply sum_congr rfl
      intro ell _
      rw [← sum_filter]
      simp
    _ ≤ ∑ _ell ∈ N.primeFactors, (1/eta)^r :=
      sum_le_sum (fun ell _ => center_fibre_le S z hS hN he heta hcut)
    _ = (1/eta)^r * (N.primeFactors.card : ℝ) := by simp [mul_comm]
    _ ≤ (1/eta)^r * (Real.log N / Real.log 2) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = _ := by ring

/-- Both original word events, separately, at their literal labels. -/
theorem word_errors_le {N d : ℕ} {Q eta : ℝ} (cs : List ℕ)
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hQ : Q ≤ (N : ℝ)) (hR : 1 ≤ Q/(d : ℝ))
    (hold : ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q d (227/50)) :
    repeatWordMass N Q d cs ≤ collisionScale N d eta * (1+Real.log N)^cs.length ∧
    centerWordMass N Q d cs ≤ (1/eta)^cs.length * Real.log N / Real.log 2 := by
  exact ⟨repeat_sum_le (labels N Q d cs) (fun l => l.getD (l.length-2) 0)
    (filter_subset _ _) hN he hd heta hold hcut (seed_cutoff_le_N hd hQ hR),
    center_sum_le (labels N Q d cs) (fun l => l.getD (l.length-2) 0)
    (filter_subset _ _) hN he heta hcut⟩

def badPairRepeat (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ (pairLabels N Q d).filter (badPair Q d),
    ((repeatReceiver N d (d*l.prod) (cutoff Q d (227/50))).card : ℝ)

def badPairCenter (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ (pairLabels N Q d).filter (badPair Q d),
    ((centerReceiver N d (d*l.prod) (cutoff Q d (227/50))).card : ℝ)

/-- Bad Gamma5 is kept as its own equality-inclusive filtered pair family. -/
theorem badPair_errors_le {N d : ℕ} {Q eta : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hQ : Q ≤ (N : ℝ)) (hR : 1 ≤ Q/(d : ℝ))
    (hold : ∀ p ∈ d.primeFactors, (N : ℝ)^eta ≤ (p : ℝ))
    (hcut : (N : ℝ)^eta ≤ cutoff Q d (227/50)) :
    badPairRepeat N Q d ≤ collisionScale N d eta * (1+Real.log N)^2 ∧
    badPairCenter N Q d ≤ (1/eta)^2 * Real.log N / Real.log 2 := by
  have hord := P2EnhancedTwentyOneSameQWeighted.cutoff_order Q d hR
  have hupper := (hord.2.2.1.trans hord.2.2.2).trans (seed_cutoff_le_N hd hQ hR)
  exact ⟨repeat_sum_le ((pairLabels N Q d).filter (badPair Q d))
    (fun _ => cutoff Q d (227/50)) (filter_subset _ _)
    hN he hd heta hold hcut hupper,
    center_sum_le ((pairLabels N Q d).filter (badPair Q d))
    (fun _ => cutoff Q d (227/50)) (filter_subset _ _) hN he heta hcut⟩

end
end ImbalancedChen.P2EnhancedExactExceptionFinite
