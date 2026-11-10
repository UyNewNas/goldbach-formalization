import ImbalancedChen.P4AOriginalFull87DataPolicy
import ImbalancedChen.P4AOriginalNewFifthPhysical

/-! The first chronological rank-six stage. It evaluates only the
original 632104 G4 rows on the actual fifth parent. Its active branch
uses exactly the same accepted rows and buffered caps as the final
bank. Outside the active third it uses the original raw saved stage.
The two displayed differences telescope at identical N and cutoff. -/
namespace ImbalancedChen.P4AOriginalSavedSixthStage
noncomputable section
open scoped Classical BigOperators
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87DataPolicy
open P4AOriginalFull87RawChronology (rawRoot)
open P4AOriginalSavedSixthArchive (Row)
open P1GuardFrozenFiniteCapAlgebra (rounded)

def level (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if active d N pre then
    finiteMax (Finset.univ : Finset Row) (fun i => Accepted n d N pre (.saved i))
      (fun i => (rounded n (P4AOriginalSavedSixthArchive.endpoint i
        (primeHistoryLogCoordinates N 6 pre)) : ℝ))
      (cap5 n d N (rosserAncestor 5 pre))
  else savedExponent d N pre

def policy (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (fifthPolicy n d N)
    (frozenParityRosserPolicy false 6 (fun h => N^level n d N h))

theorem even (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy n d N true pre = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (fifth_even n d N) (fun h => frozenParityRosserPolicy_upper_even 6 _ h) pre

theorem fifth_le_level (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    level5Exponent n d N (rosserAncestor 5 pre) ≤ level n d N pre := by
  by_cases ha : active d N pre
  · simp only [level,level5Exponent,active_ancestor d N 5 (by decide),if_pos ha]
    exact finiteMax_seed_le _ _ _ _
  · simp only [level,level5Exponent,active_ancestor d N 5 (by decide),if_neg ha]
    exact finiteMax_seed_le _ _ _ _

theorem level_le_sixth (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    level n d N pre ≤ level6Exponent n d N pre := by
  by_cases ha : active d N pre
  · simp only [level,level6Exponent,if_pos ha]
    apply finiteMax_le _ _ _ _ _ (cap5_le_licensed n d N pre)
    intro i _ hi
    exact finiteMax_row_le _ _ _ _ (.saved i)
      (P4AOriginalSixthActionBank.mem_allActions (.saved i)) hi
  · simp only [level,level6Exponent,if_neg ha]
    exact (show savedExponent d N pre ≤ elevenExponent d N pre from
      finiteMax_seed_le _ _ _ _).trans (afterLater_mono d N pre (show 0 ≤ 8 by omega))

theorem accepted_lower (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) (i : Row)
    (ha : active d N pre) (hi : Accepted n d N pre (.saved i)) :
    (rounded n (P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 pre)) : ℝ)
      ≤ level n d N pre := by
  rw [level,if_pos ha]
  exact finiteMax_row_le _ _ _ _ i (Finset.mem_univ i) hi

theorem inherit_if_no_source (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hs : ∀ i : Row, ¬P4AOriginalSavedSixthArchive.Source i (primeHistoryLogCoordinates N 6 pre)) :
    level n d N pre = level5Exponent n d N (rosserAncestor 5 pre) := by
  by_cases ha : active d N pre
  · simp only [level,level5Exponent,active_ancestor d N 5 (by decide),if_pos ha]
    apply finiteMax_eq_seed_of_outside
    intro i _ hi
    exact hs i hi.1.2.1
  · simp only [level,level5Exponent,active_ancestor d N 5 (by decide),if_neg ha,savedExponent]
    apply finiteMax_eq_seed_of_outside
    intro i _ hi
    exact hs i hi.2.1

def before (n : ℕ) (d : OriginalData) (N : ℕ) :=
  rawRoot (fifthPolicy n d (N:ℝ)) N - rawRoot (policy n d (N:ℝ)) N
def after (n : ℕ) (d : OriginalData) (N : ℕ) :=
  rawRoot (sixthPolicy n d (N:ℝ)) N - rawRoot (policy n d (N:ℝ)) N

theorem level_on_original_eleven_cell (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (hc : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c
      (primeHistoryLogCoordinates N 6 pre)) :
    level n d N pre = level5Exponent n d N (rosserAncestor 5 pre) :=
  inherit_if_no_source n d N pre (fun _ hs => (not_le_of_gt hc.oldCutoff) hs.2.2.2.2.1)

theorem exact_split (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    P4AOriginalNewFifthPhysical.sixthChange n e q a N =
      after n (P4AOriginalNewFifthUnion.data e q a) N -
      before n (P4AOriginalNewFifthUnion.data e q a) N := by
  let d := P4AOriginalNewFifthUnion.data e q a
  let P := fifthPolicy n d (N:ℝ)
  let C := frozenParityRosserPolicy false 6 (fun h => (N:ℝ)^level6Exponent n d (N:ℝ) h)
  have hp := fifth_even n d (N:ℝ)
  have hc (h : List ℕ) : C true h = true := frozenParityRosserPolicy_upper_even 6 _ h
  have hread (R : Bool → List ℕ → Bool) (hr : ∀ h,R true h = true) :
      P1Pair12RetainedSignedSource.signedTest R P4ACatalogFiveCoarseWeightedPayment.weight
        (fun _ _ => 1) [] true 1 (P4ACatalogFiveCoarseWeightedPayment.carrier N) = rawRoot R N := by
    rw [P5OriginalCommonFourthSourceLedger.signedTest_one_eq_polynomial]
    exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      R hr N N 0 (P4AOriginalFull87RawChronology.cutoff N)
  have hs : rawRoot (firstExitDepthSplicePolicy 6 P C) N - rawRoot P N =
      P4AOriginalFull87RawChronology.rawChange 6 P P C N := by
    calc
      _ = rawRoot (firstExitDepthSplicePolicy 6 P C) N -
          rawRoot (firstExitDepthSplicePolicy 6 P P) N := by rw [firstExitDepthSplicePolicy_self]
      _ = _ := by
        rw [← hread _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 P C hp hc),
          ← hread _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 P P hp hp),
          P1Pair12RetainedSignedSource.signedTest_splice_eq_stopped_add_frontier,
          P1Pair12RetainedSignedSource.signedTest_splice_eq_stopped_add_frontier,add_sub_add_left_eq_sub]
        unfold P4AOriginalFull87RawChronology.rawChange
        generalize firstExitDepthFrontier 6 P P4ACatalogFiveCoarseWeightedPayment.weight
          [] true 1 (P4ACatalogFiveCoarseWeightedPayment.carrier N) = xs
        induction xs with
        | nil => simp
        | cons h xs ih => simp only [List.map_cons,List.sum_cons]; linarith only [ih]
  change P4AOriginalFull87RawChronology.rawChange 6 P P C N =
    (rawRoot (firstExitDepthSplicePolicy 6 P C) N - rawRoot (policy n d (N:ℝ)) N) -
      (rawRoot P N - rawRoot (policy n d (N:ℝ)) N)
  linarith only [hs]

end
end ImbalancedChen.P4AOriginalSavedSixthStage
