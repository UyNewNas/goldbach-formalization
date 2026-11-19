import ImbalancedChen.P2Historical246RepeatedCeilingBook

/-! SOURCE ONLY / UNEVALUATED. Insert the paid ceiling-equality slice
into the actual H246 W2 pair-profile partition. Every other exception
and the actual child-carrier term remain explicit. -/
namespace ImbalancedChen.P2Historical246RepeatedCeilingDecomposition
noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246PairProductGate
open P2Historical246BoundedPairBridge P5OriginalActionMassBound
open P2Historical246SuccessorParentWindow P2Historical246SuccessorPrimeCeiling
open P2Historical246RepeatedCeilingSum P2Historical246RepeatedCeilingBook
open P2OriginalProfileThetaNormalization P2OriginalChildPhysicalNormalization
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- The remainder is a literal disjoint complement, with no fresh-prime
assumption: repetitions against earlier prefix primes remain here. -/
def otherCollision (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (c : ℕ) : Finset Pair :=
  (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
    parentWindow N Q old chi ∧ ¬ bothCoprime N old p ∧ p 1 ≠ c)

theorem prefix_collision_split (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) (c : ℕ) (F : Pair → ℝ) :
    (∑ p ∈ (halfCarrier N L j k).filter (fun p => interior N L j k p ∧
       parentWindow N Q old chi ∧ ¬ bothCoprime N old p), F p) =
    (∑ p ∈ equalityCollision N Q L chi old j k c, F p) +
    (∑ p ∈ otherCollision N Q L chi old j k c, F p) := by
  unfold equalityCollision otherCollision
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hi : interior N L j k p <;>
    by_cases hpw : parentWindow N Q old chi <;>
    by_cases hcop : bothCoprime N old p <;>
    by_cases hc : p 1 = c <;> simp [hi,hpw,hcop,hc]

/-- The part that remains after removing the equality-ceiling slice:
wall, all other prefix collisions, strict ceiling and literal children. -/
def laneRemainder (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  let c := ceilingPrime N m choice t
  let S := halfCarrier N L j k
  let F := oldPairAtom N Q L (parentProduct old) j k
  (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
  (∑ p ∈ otherCollision N Q L chi old j k c, F p) +
  (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
      bothCoprime N old p ∧ c < p 1), F p) +
  (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p))

def laneFull (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  pairThetaOldProfile N ((N : ℝ)^nu)
    (residualExponent N (parentProduct (oldWord t)) nu)
    (parentProduct (oldWord t)) (originalW2At j) k (outputAt 246 true)

/-- Exact same-Q signed partition for each actual successor tuple and
archived lane. No remaining error term is assumed or erased. -/
theorem laneFull_eq_slice_add_remainder {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) (j : Fin 36) (k : Fin 4) :
    laneFull N nu m choice t j k =
      laneSlice N nu m choice t j k + laneRemainder N nu m choice t j k := by
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  obtain ⟨hc,hdiv,hchi⟩ := ceilingPrime_spec hN he m choice hm ht
  have h := generation246_pair_profile_without_product_reject hN hd hL hQ j k
    (chi := (advance m choice).history.ceiling (advance m choice).ceiling t)
  dsimp only at h
  rw [successor_parent_reject_empty hN he hnu m choice hm ht j k] at h
  simp only [Finset.sum_empty, add_zero] at h
  have hcfilter := ceiling_reject_filter_eq hN hd hL hQ hc hdiv j k
  rw [← hchi] at hcfilter
  rw [hcfilter] at h
  rw [prefix_collision_split N ((N : ℝ)^nu)
    (residualExponent N (parentProduct (oldWord t)) nu)
    ((advance m choice).history.ceiling (advance m choice).ceiling t)
    (oldWord t) j k (ceilingPrime N m choice t)
    (oldPairAtom N ((N : ℝ)^nu)
      (residualExponent N (parentProduct (oldWord t)) nu)
      (parentProduct (oldWord t)) j k)] at h
  dsimp [laneFull, laneSlice, laneRemainder]
  linarith only [h]

def bookFull {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, laneFull N nu (marks a) (choices a) t j k)/5)

def bookRemainder {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, laneRemainder N nu (marks a) (choices a) t j k)/5)

/-- Book-level equality retains external labels, all four occurrences,
the sign, and the one original /5. -/
theorem bookFull_eq_slice_add_remainder {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice)
    (hm : ∀ a ∈ A, (marks a).BoxRows nu eta horizon) (j : Fin 36) :
    bookFull A marks choices N nu j = bookSlice A marks choices N nu j +
      bookRemainder A marks choices N nu j := by
  unfold bookFull bookSlice bookRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hlane : (∑ k : Fin 4, laneFull N nu (marks a) (choices a) t j k) =
      (∑ k : Fin 4, laneSlice N nu (marks a) (choices a) t j k) +
      (∑ k : Fin 4, laneRemainder N nu (marks a) (choices a) t j k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact laneFull_eq_slice_add_remainder hN he hnu (marks a) (choices a) (hm a ha) ht j k
  rw [hlane]
  ring

/-- The previous marked-Theta estimate now applies to the difference
between the actual pair profile and the explicit remainder. -/
theorem tagged_book_profile_remove_equal_ceiling {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |bookFull A marks choices N nu j - bookRemainder A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  obtain ⟨T,hT,hpay⟩ := tagged_book_equal_ceiling_payment he heps horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  obtain ⟨j,hp,hn,hlanes,hbound⟩ := hpay N hN nu hnu I A marks choices hm b hb
  refine ⟨j,hp,hn,hlanes,?_⟩
  rw [bookFull_eq_slice_add_remainder (by omega) he hnu I A marks choices hm j]
  simpa only [add_sub_cancel_right] using hbound

end
end ImbalancedChen.P2Historical246RepeatedCeilingDecomposition
