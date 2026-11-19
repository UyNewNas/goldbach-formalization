import ImbalancedChen.P2Historical246AllWallBook
import ImbalancedChen.P2Historical246RepeatedCeilingDecomposition

/-! SOURCE ONLY / UNEVALUATED. Same actual H246 row, same Q and marked
Theta: jointly bound the lower-wall and equal-ceiling collision slices.
All remaining exceptional buckets and the genuine child carrier remain
explicit; no global reserve or H247 endpoint is discharged. -/
namespace ImbalancedChen.P2Historical246JointWallCeiling
noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2Historical246PairCarrierPartition P2Historical246BoundedPairBridge
open P2Historical246RepeatedCeilingBook P2Historical246RepeatedCeilingDecomposition
open P2Historical246AllWallBook P2OriginalChildPhysicalNormalization
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- These are exactly the remaining prefix collision, strict-ceiling
rejection and literal child carrier, at the actual chosen parent. -/
def laneAfterTwo (N : ℕ) (nu : ℝ) (m : Mark) (choice : SuccessorChoice)
    (t : Fin (advance m choice).rank → Fin (N+1)) (j : Fin 36) (k : Fin 4) : ℝ :=
  let old := oldWord t
  let Q := (N : ℝ)^nu
  let L := residualExponent N (parentProduct old) nu
  let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
  let c := ceilingPrime N m choice t
  let S := halfCarrier N L j k
  let F := oldPairAtom N Q L (parentProduct old) j k
  (∑ p ∈ otherCollision N Q L chi old j k c, F p) +
  (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
      bothCoprime N old p ∧ c < p 1), F p) +
  (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p))

theorem laneRemainder_eq_wall_add_after (N : ℕ) (nu : ℝ) (m : Mark)
    (choice : SuccessorChoice) (t : Fin (advance m choice).rank → Fin (N+1))
    (j : Fin 36) (k : Fin 4) :
    laneRemainder N nu m choice t j k =
      laneWall N nu m choice t j k + laneAfterTwo N nu m choice t j k := by
  dsimp [laneRemainder,laneWall,laneAfterTwo,wallCarrier]
  ring

def bookAfterTwo {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, laneAfterTwo N nu (marks a) (choices a) t j k)/5)

theorem bookRemainder_eq_wall_add_after {I : Type*} (A : Finset I)
    (marks : I → Mark) (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) :
    bookRemainder A marks choices N nu j = wallBook A marks choices N nu j +
      bookAfterTwo A marks choices N nu j := by
  unfold bookRemainder wallBook bookAfterTwo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h : (∑ k : Fin 4, laneRemainder N nu (marks a) (choices a) t j k) =
      (∑ k : Fin 4, laneWall N nu (marks a) (choices a) t j k) +
      (∑ k : Fin 4, laneAfterTwo N nu (marks a) (choices a) t j k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact laneRemainder_eq_wall_add_after N nu (marks a) (choices a) t j k
  rw [h]
  ring

/-- Algebraic exactness before any estimates. Both disjoint slices are
subtracted once; no claim is made about the remaining sum. -/
theorem bookFull_sub_after_eq_two_slices {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice)
    (hm : ∀ a ∈ A, (marks a).BoxRows nu eta horizon) (j : Fin 36) :
    bookFull A marks choices N nu j - bookAfterTwo A marks choices N nu j =
      wallBook A marks choices N nu j + bookSlice A marks choices N nu j := by
  have h := bookFull_eq_slice_add_remainder hN he hnu I A marks choices hm j
  have h' := bookRemainder_eq_wall_add_after A marks choices N nu j
  linarith only [h,h']
/-- Literal two-slice book: all path labels, actual tuples and ordered
pair occurrences retained; original one /5 remains outside the sum. -/
def bookTwoSlices {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) : ℝ :=
  ∑ a ∈ A, ∑ t ∈ (advance (marks a) (choices a)).source N nu,
    (advance (marks a) (choices a)).weight *
      ((∑ k : Fin 4, (laneWall N nu (marks a) (choices a) t j k +
        laneSlice N nu (marks a) (choices a) t j k))/5)

theorem bookTwoSlices_eq {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) (j : Fin 36) :
    bookTwoSlices A marks choices N nu j = wallBook A marks choices N nu j +
      bookSlice A marks choices N nu j := by
  unfold bookTwoSlices wallBook bookSlice
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_add_distrib]
  ring

/-- One shared threshold and one actual j: the union of the already
separated wall and equal-ceiling buckets costs at most epsilon times
the SAME labelled-source Theta. The remaining buckets stay visible. -/
theorem tagged_book_remove_wall_and_equal_ceiling {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧
        b.2.pairRows.length = 4 ∧ (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        |bookFull A marks choices N nu j - bookAfterTwo A marks choices N nu j| ≤
          epsilon * Theta N ((N : ℝ)^nu)
            (sourceSupport A next N nu) (sourceSigma A next N nu) := by
  have heps' : 0 < (5*epsilon/8 : ℝ) := by positivity
  obtain ⟨Tw,hTw,hwall⟩ := successor_all_wall_uniform he heps' horizon
  obtain ⟨Tc,hTc,hceiling⟩ := successor_equal_ceiling_all_rows_uniform he heps' horizon
  refine ⟨max Tw Tc, le_trans hTw (le_max_left _ _), ?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  have hN1 : 1 < N := by omega
  let next := fun a => advance (marks a) (choices a)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hpoint (a : I) (ha : a ∈ A) (t : Fin (next a).rank → Fin (N+1))
      (ht : t ∈ (next a).source N nu) :
      |(∑ k : Fin 4, (laneWall N nu (marks a) (choices a) t j k +
        laneSlice N nu (marks a) (choices a) t j k))/5| ≤
        epsilon * thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
    obtain ⟨hc,hdiv,hchi⟩ := ceilingPrime_spec hN1 he (marks a) (choices a) (hm a ha) ht
    have hk (k : Fin 4) :
        |laneWall N nu (marks a) (choices a) t j k +
          laneSlice N nu (marks a) (choices a) t j k| ≤
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
      have hw := hwall N (le_trans (le_max_left _ _) hN) nu hnu
        (marks a) (choices a) (hm a ha) t ht j k
      have hs := hceiling N (le_trans (le_max_right _ _) hN) nu hnu
        (marks a) (choices a) (hm a ha) t ht
        (ceilingPrime N (marks a) (choices a) t) hc hdiv hchi j k
      calc
        |laneWall N nu (marks a) (choices a) t j k +
          laneSlice N nu (marks a) (choices a) t j k| ≤
            |laneWall N nu (marks a) (choices a) t j k| +
              |laneSlice N nu (marks a) (choices a) t j k| := abs_add _ _
        _ ≤ (5*epsilon/8)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) +
            (5*epsilon/8)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) :=
              add_le_add hw hs
        _ = _ := by ring
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    calc
      |∑ k : Fin 4, (laneWall N nu (marks a) (choices a) t j k +
        laneSlice N nu (marks a) (choices a) t j k)| ≤
          ∑ k : Fin 4, |laneWall N nu (marks a) (choices a) t j k +
            laneSlice N nu (marks a) (choices a) t j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 4,
          (5*epsilon/4)*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)) := by
            exact Finset.sum_le_sum (fun k _ => hk k)
      _ = (epsilon*thetaAtom N ((N : ℝ)^nu) (parentProduct (oldWord t)))*5 := by
            simp [Fin.sum_univ_succ] <;> ring
  have hbook : |bookTwoSlices A marks choices N nu j| ≤
      epsilon * Theta N ((N : ℝ)^nu)
        (sourceSupport A next N nu) (sourceSigma A next N nu) := by
    calc
      |bookTwoSlices A marks choices N nu j| ≤
          ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
            (next a).weight * (epsilon * thetaAtom N ((N : ℝ)^nu)
              (parentProduct (oldWord t))) := by
        unfold bookTwoSlices
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro a ha
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro t ht
        have hw : 0 ≤ (next a).weight := by
          exact mul_nonneg (advance_boxRows (marks a) (choices a) (hm a ha)).2.2.2.2
            (next a).history.scalar_nonneg
        rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hpoint a ha t ht) hw
      _ = epsilon * Theta N ((N : ℝ)^nu)
          (sourceSupport A next N nu) (sourceSigma A next N nu) := by
        rw [source_Theta_exact, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [oldWord_product]
        ring
  rw [bookFull_sub_after_eq_two_slices hN1 he hnu I A marks choices hm j]
  rw [← bookTwoSlices_eq]
  exact hbook

end
end ImbalancedChen.P2Historical246JointWallCeiling
