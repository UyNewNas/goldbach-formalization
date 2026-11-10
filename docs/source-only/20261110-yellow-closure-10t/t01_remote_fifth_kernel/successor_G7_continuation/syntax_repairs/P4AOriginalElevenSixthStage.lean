import ImbalancedChen.P4AOriginalSavedSixthStage
import ImbalancedChen.P2OriginalSixthElevenLogSemantics

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The chronological G7 stage is inserted after the real G4 stage, on the
actual old+new fifth union. It uses exactly the existing eleven accepted
actions at this same prefix. The physical G7 source has t6<1/50, whereas
every G4 Source has t6>=1/50; this reduces the predecessor to the actual
level-five parent on G7, without identifying it with a raw comparison cap.
No occurrence, asymptotic density or numerical-floor conclusion is assumed.
-/
namespace ImbalancedChen.P4AOriginalElevenSixthStage
noncomputable section
open scoped Classical BigOperators
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87DataPolicy
open P4AOriginalFull87RawChronology (rawRoot)
open P1GuardFrozenFiniteCapAlgebra (rounded)
def level (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if active d N pre then
    finiteMax ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset (fun c => Accepted n d N pre (.eleven c))
      (fun c => (rounded n (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre)) : ℝ))
      (P4AOriginalSavedSixthStage.level n d N pre)
  else elevenExponent d N pre

def policy (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (fifthPolicy n d N)
    (frozenParityRosserPolicy false 6 (fun h => N^level n d N h))

theorem even (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy n d N true pre = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (fifth_even n d N) (fun h => frozenParityRosserPolicy_upper_even 6 _ h) pre

theorem saved_le_level (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    P4AOriginalSavedSixthStage.level n d N pre ≤ level n d N pre := by
  by_cases ha : active d N pre
  · simp only [level,if_pos ha]
    exact finiteMax_seed_le _ _ _ _
  · simp only [level,P4AOriginalSavedSixthStage.level,if_neg ha]
    exact finiteMax_seed_le _ _ _ _

theorem level_le_sixth (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    level n d N pre ≤ level6Exponent n d N pre := by
  by_cases ha : active d N pre
  · simp only [level,level6Exponent,if_pos ha]
    apply finiteMax_le _ _ _ _ _
      (by simpa only [level6Exponent,if_pos ha] using P4AOriginalSavedSixthStage.level_le_sixth n d N pre)
    intro c _ hc
    exact finiteMax_row_le _ _ _ _ (.eleven c)
      (P4AOriginalSixthActionBank.mem_allActions (.eleven c)) hc
  · simp only [level,level6Exponent,if_neg ha]
    exact afterLater_mono d N pre (show 0 ≤ 8 by omega)

theorem accepted_lower (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (ha : active d N pre) (hc : Accepted n d N pre (.eleven c)) :
    (rounded n (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre)) : ℝ) ≤ level n d N pre := by
  rw [level,if_pos ha]
  exact finiteMax_row_le _ _ _ _ c (List.mem_toFinset.mpr (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.allCells_complete c)) hc

/-- The genuine chronological predecessor on every original G7 source.
This is a disjoint-support identity, not an assumed parent cap bound. -/
theorem predecessor_on_original_source (n : ℕ) (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c (primeHistoryLogCoordinates N 6 pre)) :
    P4AOriginalSavedSixthStage.level n d N pre = level5Exponent n d N (rosserAncestor 5 pre) := by
  apply P4AOriginalSavedSixthStage.inherit_if_no_source
  intro i hs
  exact (not_le_of_gt hc.oldCutoff) hs.2.2.2.2.1

def gain (n : ℕ) (d : OriginalData) (N : ℕ) : ℝ :=
  rawRoot (P4AOriginalSavedSixthStage.policy n d (N:ℝ)) N - rawRoot (policy n d (N:ℝ)) N
def remaining (n : ℕ) (d : OriginalData) (N : ℕ) : ℝ :=
  rawRoot (sixthPolicy n d (N:ℝ)) N - rawRoot (policy n d (N:ℝ)) N

/-- Exact signed stage5→G4→G7→later-sixth decomposition, on one actual
union, one target and the same carrier/cutoff. G4 and G7 each occur once. -/
theorem exact_split (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    P4AOriginalNewFifthPhysical.sixthChange n e q a N =
      remaining n (P4AOriginalNewFifthUnion.data e q a) N -
      gain n (P4AOriginalNewFifthUnion.data e q a) N -
      P4AOriginalSavedSixthStage.before n (P4AOriginalNewFifthUnion.data e q a) N := by
  have h := P4AOriginalSavedSixthStage.exact_split n e q a N
  dsimp only [remaining,gain,P4AOriginalSavedSixthStage.after] at h ⊢
  linarith only [h]

end
end ImbalancedChen.P4AOriginalElevenSixthStage
