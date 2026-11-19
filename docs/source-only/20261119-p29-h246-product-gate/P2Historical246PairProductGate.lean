import ImbalancedChen.P2Historical246BoundedPairBridge
import ImbalancedChen.P2OriginalW2CountTupleReindex

/-!
SOURCE ONLY / UNEVALUATED. The actual half-open W2 pair box already has
its original physical square gates. At the same Q these gates pay its
ordinary child product cutoff. No other exceptional lane is removed.
-/
namespace ImbalancedChen.P2Historical246PairProductGate

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2Historical246PairCarrierPartition
open P2OriginalHalfOpenProfileCarrier P2OriginalW2CountTupleReindex
open P2OriginalProfileThetaNormalization P2Historical246BoundedPairBridge
open P2W2PhysicalChildFeedback
open P5OriginalActionMassBound
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- The ORIGINAL selected-square and full-square gates hold for the
actual half-open box, before any prefix, ceiling or history filtering. -/
theorem halfCarrier_original_pair_gates {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    PairGate Q (parentProduct old) (p 0) (p 1) := by
  have hm := (pair_count_carrier_membership hN hd hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k p).mp hp
  exact hm.2.2

/-- The original strict square gate d*small^2*large<Q pays the strict
product gate d*large*small<Q because the small coordinate is prime. -/
theorem halfCarrier_productGate {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) {p : Pair} (hp : p ∈ halfCarrier N L j k) :
    productGate Q old p := by
  have hgate := halfCarrier_original_pair_gates hN hd hL hQ j k hp
  have hbox := (Finset.mem_filter.mp hp).1
  have hprime := ((mem_actualPrimeBoxTuples_iff.mp hbox) 0).1
  have hp0 : (1 : ℝ) ≤ p 0 := by exact_mod_cast hprime.one_lt.le
  have hp_sq : (p 0 : ℝ) ≤ (p 0 : ℝ)^2 := by nlinarith [sq_nonneg ((p 0 : ℝ)-1)]
  have hm := mul_le_mul_of_nonneg_left hp_sq
    (show 0 ≤ (parentProduct old : ℝ)*(p 1 : ℝ) by positivity)
  unfold PairGate at hgate
  unfold productGate
  simp only [Nat.cast_mul]
  nlinarith only [hm,hgate.2]

/-- The product-cutoff rejection bucket in the earlier six-way
partition is empty, not merely small. All other buckets are retained. -/
theorem product_reject_empty {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) :
    (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
      parentWindow N Q old chi ∧ bothCoprime N old p ∧ orderedCeiling N chi p ∧
      ¬ productGate Q old p) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨hS,_,_,_,_,hbad⟩ := Finset.mem_filter.mp hp
  exact hbad (halfCarrier_productGate hN hd hL hQ j k hS)

/-- The exact original generation-246 profile atom has zero sum on this
one bucket for each of the four separately tagged historical lanes. -/
theorem generation246_tagged_product_reject_zero
    {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ k : Fin 4,
        (∑ p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
          parentWindow N Q old chi ∧ bothCoprime N old p ∧ orderedCeiling N chi p ∧
          ¬ productGate Q old p),
          oldPairAtom N Q L (parentProduct old) j k p) = 0 := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hp,hn,hlanes,?_⟩
  intro k
  rw [product_reject_empty hN hd hL hQ j k]
  simp


/-- The original generation-246 pair-profile now has only its four
remaining explicit exception terms plus the genuine child-carrier sum.
No exceptional term is discarded or bounded here. -/
theorem generation246_pair_profile_without_product_reject
    {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) :
    pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
      let S := halfCarrier N L j k
      let F := oldPairAtom N Q L (parentProduct old) j k
      (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ ¬ parentWindow N Q old chi), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        ¬ bothCoprime N old p), F p) +
      (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
        bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
      (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p)) := by
  have h := generation246_pair_profile_partition N Q L chi old j k
  simp only [product_reject_empty hN hd hL hQ j k, Finset.sum_empty, add_zero] at h
  have ha := active_sum_eq_pairChildren hN hd hL hQ j k
    (oldPairAtom N Q L (parentProduct old) j k)
  change (∑ p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
    parentWindow N Q old chi ∧ bothCoprime N old p ∧ orderedCeiling N chi p ∧
    productGate Q old p), oldPairAtom N Q L (parentProduct old) j k p) = _ at ha
  rw [ha] at h
  exact h

/-- Select the actual 246th row once; its four original pair lanes use
this identity with the same row parameters and the same old H array. -/
theorem generation246_tagged_profile_without_product_reject
    {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ k : Fin 4,
        pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
          let S := halfCarrier N L j k
          let F := oldPairAtom N Q L (parentProduct old) j k
          (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ ¬ parentWindow N Q old chi), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            ¬ bothCoprime N old p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
          (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p)) := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  exact ⟨j,hp,hn,hlanes,fun k =>
    generation246_pair_profile_without_product_reject hN hd hL hQ j k⟩

end
end ImbalancedChen.P2Historical246PairProductGate
