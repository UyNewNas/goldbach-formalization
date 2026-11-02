import ImbalancedChen.P4AOriginalLive171819PrimeBank

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The LIVE ascending13 source domains, rather than exclusions on slot16's
domains. The original slots15--18 inherit the independently frozen common
sixth ancestor; the original slot19 selects its own ascending138 cap.
The candidate58 and common87 constructors have exactly the same incoming
rank-eight LIST, including multiplicities, signs, masses and remainders.
No equality of their later policies, or full58/full87 exhaustion, is claimed.
-/
namespace ImbalancedChen.P4AOriginalLive19ActualChronology
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalLive171819Atlas P4AOriginalLive171819CommonParent
open P4AOriginalLive171819PrimeBank

/-- The actual seed7 row14 has the opposite third-pair side. -/
theorem live19_not_seed7 (i : Fin 13) (t : Point)
    (hs : sourceRows (.ascending19 i) t) :
    ¬ P4AOriginalSeed7Unequal15Literal.seed7SourceRows t := by
  intro hseed
  have ha := (source19_guard i t hs).ascendingThird
  have hd := hseed (14 : Fin 96)
  norm_num [P4AOriginalSeed7Unequal15Literal.seed7Rows,
    P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hd
  dsimp [mu] at ha
  linarith

theorem live19_not_ascending14 (i : Fin 13) (t : Point)
    (hs : sourceRows (.ascending19 i) t) :
    ¬ P4AOriginalAscending14Literal42.ascending14Owns t := by
  intro ha
  exact P4AOriginalAscending14Literal42.ascending14_disjoint_ascending13
    t ha i (source19_guard i t hs)

theorem live19_not_descending15 (i : Fin 13) (t : Point)
    (hs : sourceRows (.ascending19 i) t) :
    ¬ ∃ j : Fin 15, OriginalDescendingFifteenCellOwnership.StrictRows j t := by
  rintro ⟨j, hd⟩
  have ha := (source19_guard i t hs).ascendingThird
  have hb := hd.oldWinner
  dsimp [P2OriginalDescendingEighthLogSemantics.d] at hb
  linarith

/-- Uses the actual thirteen winner9 and both winner50 source domains.
The source-tag inequality is justified by the G literal owner theorem. -/
theorem live19_not_unequal15 (i : Fin 13) (t : Point)
    (hs : sourceRows (.ascending19 i) t)
    (u : P4AOriginalSeed7Unequal15Literal.UnequalCell) :
    ¬ P4AOriginalSeed7Unequal15Literal.unequalSourceRows u t := by
  intro hu
  have hu' : sourceRows (.unequal18 u) t := by cases u <;> exact hu
  have heq := live_owner_unique (.ascending19 i) (.unequal18 u) t hs hu'
  cases heq

/-- Exact original chronology on each LIVE19 domain. The only parent
inequality here is displayed; the arithmetic theorem below derives it
from the independently defined common frontier, rather than assuming it. -/
theorem source_slots1519 (i : Fin 13) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hs : sourceRows (.ascending19 i) (point8 N pre))
    (hcap : lambda6 (rosserAncestor 6 pre) ≤ oldCap (.ascending19 i) (point8 N pre)) :
    P4AOriginalPrior58Chronology.slot15 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot16 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot17 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot18 N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∧
    P4AOriginalPrior58Chronology.slot19 N lambda6 pre = newCap (.ascending19 i) (point8 N pre) := by
  let t := point8 N pre
  have hseed : ¬ P4AOriginalSeed7Unequal15Literal.ActualSeed7 N lambda6 pre := by
    intro h
    exact live19_not_seed7 i t hs h.2.1
  have h15 : P4AOriginalPrior58Chronology.slot15 N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalPrior58Chronology.slot15,
      P4AOriginalSeed7Unequal15Literal.seed7Raised, hseed,
      P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h16source : P4AOriginalAscending14Literal42.literal16Exponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    have hout := live19_not_ascending14 i t hs
    simpa [P4AOriginalAscending14Literal42.literal16Exponent,
      P2OriginalAscendingEighthCapDictionary.familyNextExponent,
      P4AOriginalAscending14Literal42.ascending14Owns,
      P2OriginalAscendingEighthCapDictionary.inheritedExponent, t, point8] using
      (show (if P4AOriginalAscending14Literal42.ascending14Owns t ∧
          P2OriginalAscendingEighthCapDictionary.CurrentParentGuard t
            (lambda6 (rosserAncestor 6 pre)) then
          P2OriginalAscendingEighthCapDictionary.M t else lambda6 (rosserAncestor 6 pre)) =
          lambda6 (rosserAncestor 6 pre) from if_neg (fun h => hout h.1))
  have h16 : P4AOriginalPrior58Chronology.slot16 N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp only [P4AOriginalPrior58Chronology.slot16, h15, h16source, max_self]
  have hdsource : OriginalDescendingFifteenCellOwnership.ownedRaisedExponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    have hout := live19_not_descending15 i t hs
    simp [OriginalDescendingFifteenCellOwnership.ownedRaisedExponent, hout,
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth,
      P2OriginalAscendingEighthCapDictionary.inheritedExponent, t, point8]
  have h17 : P4AOriginalPrior58Chronology.slot17 N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp only [P4AOriginalPrior58Chronology.slot17, h16, hdsource, max_self]
  have hu : ∀ u, ¬ P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 u pre := by
    intro u h
    exact live19_not_unequal15 i t hs u h.2.1
  have husource : P4AOriginalSeed7Unequal15Literal.unequalRaised N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalSeed7Unequal15Literal.unequalRaised, hu,
      P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h18 : P4AOriginalPrior58Chronology.slot18 N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp only [P4AOriginalPrior58Chronology.slot18, h17, husource, max_self]
  have h19source : OriginalAscendingThirteenCellOwnership.ownedRaisedExponent N lambda6 pre =
      newCap (.ascending19 i) t := by
    apply OriginalAscendingThirteenCellOwnership.ownedRaisedExponent_eq_selected_cap
      N lambda6 pre i (source19_guard i t hs)
    exact hcap
  have hle : lambda6 (rosserAncestor 6 pre) ≤ newCap (.ascending19 i) t :=
    hcap.trans (source_improvement (.ascending19 i) t hs).le
  have h19 : P4AOriginalPrior58Chronology.slot19 N lambda6 pre =
      newCap (.ascending19 i) t := by
    simp only [P4AOriginalPrior58Chronology.slot19, h18, h19source, max_eq_right hle]
  exact ⟨h15, h16, h17, h18, h19⟩

/-- The independently frozen common constructor and original candidate58
have the exact same incoming rank-eight LIST for any initial state.
This statement preserves repetitions; it is stronger than membership. -/
theorem candidate58_common_frontier
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8
        (P4AOriginalPrior58Chronology.candidate58Policy N
          (P5OriginalCommonRefinedConstructor.lambda6 d N)
          (P5OriginalCommonRefinedConstructor.policy5 d N)) h pre positive mass carrier =
      firstExitDepthFrontier 8 (P5OriginalCommonRefinedConstructor.policy8 d N)
        h pre positive mass carrier := by
  rw [P4AOriginalPrior58Chronology.candidate58_frontier_eight,
    P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six]
  rfl

/-- Actual prime states provide source membership, original firstStop and
the NEW common ancestor upper bound. This eliminates the displayed cap
premise of source_slots1519 at the genuine arithmetic consumer. -/
theorem actual_common_live19
    (i : Fin 13) (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    OriginalAscendingThirteenCellOwnership.StrictRows i (point8 (N : ℝ) s.selectedPrefix) ∧
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ)
      (rosserAncestor 1 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot18 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot19 (N : ℝ)
        (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
      P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex (.ascending19 i))
        (point8 (N : ℝ) s.selectedPrefix) := by
  obtain ⟨hrows, hstop, _hhistory, hcap⟩ :=
    shared_frontier_live_guard (.ascending19 i) d he N cap hN w z s hs
  obtain ⟨_h15, _h16, _h17, h18, h19⟩ :=
    source_slots1519 i (N : ℝ) (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
      s.selectedPrefix hrows hcap
  rw [source_newCap_dictionary (.ascending19 i) _ hrows] at h19
  exact ⟨source19_guard i _ hrows, hstop, h18, h19⟩

/-- This is equality of the original source bank LISTS on the two actual
constructors, rather than an association of separately chosen finite sets. -/
theorem candidate58_common_selected
    (c : LiveCell) (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N cap : ℕ) (w z : ℝ) :
    selected c d.e d.chi d.m d.omega N cap w z
        (P4AOriginalPrior58Chronology.candidate58Policy (N : ℝ)
          (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
          (P5OriginalCommonRefinedConstructor.policy5 d (N : ℝ))) =
      selected c d.e d.chi d.m d.omega N cap w z
        (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) := by
  unfold selected
  rw [candidate58_common_frontier]

/-- A real common-frontier state has exactly one of the 43 live source
owners whenever it belongs to any live bank. No frontier nodup premise. -/
theorem actual_common_bank_owner
    (c c' : LiveCell) (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    s ∈ selected c' d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) ↔ c' = c := by
  constructor
  · intro hs'
    exact live_owner_unique c' c _
      (shared_frontier_live_guard c' d he N cap hN w z s hs').1
      (shared_frontier_live_guard c d he N cap hN w z s hs).1
  · intro h
    simpa only [h] using hs

end
end ImbalancedChen.P4AOriginalLive19ActualChronology
