import ImbalancedChen.P4AActualSixthFrozenEighthAdmission
import ImbalancedChen.P2OriginalDescendingEighthLogSemantics

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original eighth residual requires H7 < the ACTUAL inherited sixth
exponent. An upper comparison R6 cannot establish that lower bound. This
module derives the precise natural cubic test from actual seventh-history
admission, then transports it to the eight processing-order log coordinates.
No H7 premise, copied historical cap, accepted-row statistic, or numerical
endpoint is used. The complete selected sixth policy and 87-domain payload
remain distinct missing data.
-/
namespace ImbalancedChen.P4AActualEighthInheritedHistoryGuard

noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AActualSixthFrozenEighthAdmission

/-- At an odd-length increasing prime history the minimum label sees the
whole set in the provider's odd-prefix cube test. -/
theorem odd_history_own_cube
    (Q : ℝ) (q : ℕ) (pre : List ℕ)
    (hsort : (q :: pre).Pairwise (· < ·))
    (hodd : ¬Even (q :: pre).length)
    (hadm : ordinaryRosserPrefixAdmissible false Q (q :: pre)) :
    (((q :: pre).prod : ℕ) : ℝ) * (q : ℝ) ^ 2 < Q := by
  have hfilter : (q :: pre).toFinset.filter (fun p => q ≤ p) =
      (q :: pre).toFinset := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    rcases List.mem_cons.mp (List.mem_toFinset.mp hp) with rfl | hp
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hsort).1 p hp).le
  have hcard : ¬Even (((q :: pre).toFinset.filter (fun p => q ≤ p)).card) := by
    rw [hfilter, List.toFinset_card_of_nodup hsort.nodup]
    exact hodd
  have hu : LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet Q (q :: pre).toFinset := hadm.2
  have hc := hu q (by simp) hcard
  have hprod : ((q :: pre).toFinset.prod id : ℕ) = (q :: pre).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hsort.nodup
  simpa only [hfilter, hprod] using hc

/-- Literal seventh own-cube behind the actual eighth frontier. Its level
is the very sixth level used by the parent policy, for every presieve w. -/
theorem actual_seventh_cube_lt_level
    (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8 (sixthPolicy parent Q6)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    (((rosserAncestor 7 state.selectedPrefix).prod : ℕ) : ℝ) *
        ((rosserAncestor 7 state.selectedPrefix).headD 0 : ℝ) ^ 2 <
      Q6 (rosserAncestor 6 state.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 8 _ h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) state hs
  have hadm := actual_rank_eight_seventh_admissible parent Q6 N cap w z h state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8
    (sixthPolicy parent Q6) h (roughPrimeUniverse N cap w z) state hs
  have hsort : state.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hasort : (rosserAncestor 7 state.selectedPrefix).Pairwise (· < ·) :=
    hsort.drop
  have halen : (rosserAncestor 7 state.selectedPrefix).length = 7 := by
    simp only [rosserAncestor_length, hlen]
    decide
  cases ha : rosserAncestor 7 state.selectedPrefix with
  | nil => simp [ha] at halen
  | cons q pre =>
      have hc := odd_history_own_cube (Q6 (rosserAncestor 6 state.selectedPrefix)) q pre
        (by simpa only [ha] using hasort)
        (by rw [← ha, halen]; decide)
        (by simpa only [ha] using hadm)
      simpa only [ha, List.headD_cons] using hc

/-- The precise original H7 affine form is below the ACTUAL inherited
exponent; no comparison-envelope or historical-history hypothesis occurs. -/
theorem actual_log_history7_lt_current
    (parent : Bool → List ℕ → Bool) (lambda6 : List ℕ → ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8
      (sixthPolicy parent (fun pre => (N : ℝ) ^ lambda6 pre))
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    P2OriginalDescendingEighthLogSemantics.history7
        (primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix) <
      lambda6 (rosserAncestor 6 state.selectedPrefix) := by
  let a := rosserAncestor 7 state.selectedPrefix
  have hlen := firstExitDepthFrontier_selected_length 8 _ h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) state hs
  have ha : a.length = 7 := by
    simp only [a, rosserAncestor_length, hlen]
    decide
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8
    (sixthPolicy parent (fun pre => (N : ℝ) ^ lambda6 pre)) h
    (roughPrimeUniverse N cap w z) state hs
  have hapos : ∀ p ∈ a, 0 < p := by
    intro p hp
    have hp' : p ∈ state.selectedPrefix :=
      (List.drop_sublist (state.selectedPrefix.length - 7) state.selectedPrefix).subset hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp'))).pos
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN
  have hcube := actual_seventh_cube_lt_level parent
    (fun pre => (N : ℝ) ^ lambda6 pre) N cap w z h state hs
  have hp2 : (N : ℝ) ^ (2 * primeHistoryLogCoordinates (N : ℝ) 7 a 6) =
      (a.headD 0 : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hN0.le,
      rpow_primeHistoryLogCoordinates (N : ℝ) hN ha hapos]
    rw [primeHistoryTuple_last (k := 6) ha]
    norm_num
  have hpow : (N : ℝ) ^ ((∑ i : Fin 7, primeHistoryLogCoordinates (N : ℝ) 7 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 7 a 6) =
      (a.prod : ℝ) * (a.headD 0 : ℝ) ^ 2 := by
    rw [Real.rpow_add hN0, rpow_sum_primeHistoryLogCoordinates (N : ℝ) hN ha hapos, hp2]
  have hineq : (∑ i : Fin 7, primeHistoryLogCoordinates (N : ℝ) 7 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 7 a 6 <
        lambda6 (rosserAncestor 6 state.selectedPrefix) := by
    apply (Real.rpow_lt_rpow_left_iff hN).mp
    rw [hpow]
    exact hcube
  have hcoord (i : Fin 7) : primeHistoryLogCoordinates (N : ℝ) 7 a i =
      primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix (i.castLE (by omega)) :=
    primeHistoryLogCoordinates_ancestor (N : ℝ) hlen (by omega) i
  have hsum : (∑ i : Fin 7, primeHistoryLogCoordinates (N : ℝ) 7 a i) +
      2 * primeHistoryLogCoordinates (N : ℝ) 7 a 6 =
        P2OriginalDescendingEighthLogSemantics.history7
          (primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix) := by
    simp only [Fin.sum_univ_succ, hcoord, P2OriginalDescendingEighthLogSemantics.history7]
    ring
  rwa [hsum] at hineq

/-- The original lower residual inequality follows from the inherited
seventh test and the true order of the actual eight primes. -/
theorem actual_residual_parameter_gt_one
    (parent : Bool → List ℕ → Bool) (lambda6 : List ℕ → ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8
      (sixthPolicy parent (fun pre => (N : ℝ) ^ lambda6 pre))
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    1 < (lambda6 (rosserAncestor 6 state.selectedPrefix) -
      P2OriginalDescendingEighthLogSemantics.total
        (primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix)) /
      primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix 7 := by
  have hhist := actual_log_history7_lt_current parent lambda6 N cap hN w z h state hs
  have hgeometry := primeHistoryLogCoordinates_frontier 8
    (sixthPolicy parent (fun pre => (N : ℝ) ^ lambda6 pre)) h N cap hN w z state hs
  have hpos := (hgeometry.2 (7 : Fin 8)).1
  have horder := hgeometry.1 (by decide : (6 : Fin 8) < 7)
  have hidentity := P2OriginalDescendingEighthLogSemantics.history7_residual
    (primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix)
  apply (lt_div_iff₀ hpos).mpr
  linarith only [hhist, horder, hidentity]

end
end ImbalancedChen.P4AActualEighthInheritedHistoryGuard
