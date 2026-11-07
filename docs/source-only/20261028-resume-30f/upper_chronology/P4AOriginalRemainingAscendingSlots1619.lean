import ImbalancedChen.P4AOriginalRemainingAscendingPrimeBank

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact eleven remaining ascending cells preserve their slot16 action
through the literal slot17/18/19 updates. Descending15, unequal15 and
ascending13 source systems are excluded by their own actual original rows.
This does not construct the live regions of those three other stage atlases
or identify the whole common physical87 replacement with this chronology.
-/
namespace ImbalancedChen.P4AOriginalRemainingAscendingSlots1619
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
open P4AOriginalRemainingAscendingAtlas P4AOriginalRemainingAscendingCommonParent
open P4AOriginalRemainingAscendingPrimeBank

/-- The actual source atlas has different strict branch choices, not
merely different labels on one source region. -/
private theorem source_separator : ∀ (c c' : RemainingCell), c ≠ c' →
    ∃ I ∈ oldMasks, literalPattern (sourceId c) I ≠ literalPattern (sourceId c') I := by decide

theorem source_disjoint (c c' : RemainingCell) (hne : c ≠ c')
    (t : Fin 8 → ℝ) (h : sourceRows c t) (h' : sourceRows c' t) : False := by
  obtain ⟨I, hI, hdiff⟩ := source_separator c c' hne
  exact (sourceRows_cellGuard c t h).incompatible_patterns
    (sourceRows_cellGuard c' t h') I hI hdiff

/-- Exclusion of the three literal slot18 families uses the exact
source rows: 13 winner9 cells and the two genuinely different winner50
branches. A generic predicate called unequal is not used as a substitute. -/
theorem source_not_unequal (c : RemainingCell) (t : Fin 8 → ℝ)
    (hs : sourceRows c t) (u : P4AOriginalSeed7Unequal15Literal.UnequalCell)
    (hu : P4AOriginalSeed7Unequal15Literal.unequalSourceRows u t) : False := by
  cases u with
  | nine j =>
      have hr := hs (41 : Fin 96)
      have heq : rows c 41 = baseRows 41 := by fin_cases c <;> decide
      rw [heq] at hr
      have h14 := hu (14 : Fin 97)
      have h15 := hu (15 : Fin 97)
      fin_cases j <;>
        norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
          P4AOriginalSeed7Unequal15Literal.nineRows,
          evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
          Fin.sum_univ_succ] at hr h14 h15 <;> linarith
  | fiftyAsc =>
      have hr := hs (14 : Fin 96)
      have heq : rows c 14 = baseRows 14 := by fin_cases c <;> decide
      rw [heq] at hr
      have hf := hu (10 : Fin 95)
      norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
        P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
        evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        Fin.sum_univ_succ] at hr hf
      linarith
  | fiftyDesc =>
      have hr := hs (82 : Fin 96)
      have hd := (sourceRows_cellGuard c t hs).old_descending
      have hf15 := hu (15 : Fin 96)
      have hf22 := hu (22 : Fin 96)
      fin_cases c <;>
        norm_num [rows, changedRows, rightPatch, baseRows,
          P4AOriginalAscendingCell0Literal96.rows,
          P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
          evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
          Fin.sum_univ_succ] at hr hf15 hf22 <;>
        dsimp [A, C, d] at hd <;> linarith

private theorem unequal_inherits (c : RemainingCell) (N : ℝ)
    (lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (h : sourceRows c (point8 N pre)) :
    P4AOriginalSeed7Unequal15Literal.unequalRaised N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
  have hn : ∀ u, ¬ P4AOriginalSeed7Unequal15Literal.ActualUnequalCell N lambda6 u pre := by
    intro u hu
    exact source_not_unequal c _ h u hu.2.1
  simp [P4AOriginalSeed7Unequal15Literal.unequalRaised, hn,
    P4AOriginalSeed7Unequal15Literal.currentSixth]

/-- Exact per-prefix source chronology with the precise displayed frozen
cap. In the actual arithmetic application below this cap is NEW lambda6
from the independent common constructor, whose guard is derived there. -/
theorem source_slots1619 (c : RemainingCell) (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (hrows : sourceRows c (point8 N pre))
    (hparent : CurrentParentGuard (point8 N pre) (lambda6 (rosserAncestor 6 pre))) :
    P4AOriginalPrior58Chronology.slot16 N lambda6 pre = M (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot17 N lambda6 pre = M (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot18 N lambda6 pre = M (point8 N pre) ∧
    P4AOriginalPrior58Chronology.slot19 N lambda6 pre = M (point8 N pre) := by
  let t := point8 N pre
  have hc := sourceRows_cellGuard c t hrows
  have ha : ascending14Owns t := ⟨sourceId c, sourceId_selected c, hc⟩
  have hnSeed : ¬ P4AOriginalSeed7Unequal15Literal.ActualSeed7 N lambda6 pre := by
    intro h
    exact sourceRows_not_seed7 c t hrows h.2.1
  have h15 : P4AOriginalPrior58Chronology.slot15 N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [P4AOriginalPrior58Chronology.slot15,
      P4AOriginalSeed7Unequal15Literal.seed7Raised, hnSeed,
      P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h16candidate : literal16Exponent N lambda6 pre = M t := by
    simp [literal16Exponent, familyNextExponent, ha, hparent, t, point8, inheritedExponent]
  have hle : lambda6 (rosserAncestor 6 pre) ≤ M t := hparent.2.trans hc.improvement.le
  have h16 : P4AOriginalPrior58Chronology.slot16 N lambda6 pre = M t := by
    simp only [P4AOriginalPrior58Chronology.slot16, h15, h16candidate, max_eq_right hle]
  have hnotD : ¬ ∃ j : Fin 15, OriginalDescendingFifteenCellOwnership.StrictRows j t := by
    rintro ⟨j, hj⟩
    exact ascending14_disjoint_descending15 t ha j hj
  have hdparent : OriginalDescendingFifteenCellOwnership.ownedRaisedExponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [OriginalDescendingFifteenCellOwnership.ownedRaisedExponent, hnotD,
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth, t, point8]
  have h17 : P4AOriginalPrior58Chronology.slot17 N lambda6 pre = M t := by
    simp only [P4AOriginalPrior58Chronology.slot17, h16, hdparent, max_eq_left hle]
  have huparent := unequal_inherits c N lambda6 pre hrows
  have h18 : P4AOriginalPrior58Chronology.slot18 N lambda6 pre = M t := by
    simp only [P4AOriginalPrior58Chronology.slot18, h17, huparent, max_eq_left hle]
  have hnotA : ¬ ∃ j : Fin 13, OriginalAscendingThirteenCellOwnership.StrictRows j t := by
    rintro ⟨j, hj⟩
    exact ascending14_disjoint_ascending13 t ha j hj
  have haparent : OriginalAscendingThirteenCellOwnership.ownedRaisedExponent N lambda6 pre =
      lambda6 (rosserAncestor 6 pre) := by
    simp [OriginalAscendingThirteenCellOwnership.ownedRaisedExponent, hnotA,
      P4ASlot19ChargedFrontierSourceOnly.inheritedSixth, t, point8]
  have h19 : P4AOriginalPrior58Chronology.slot19 N lambda6 pre = M t := by
    simp only [P4AOriginalPrior58Chronology.slot19, h18, haparent, max_eq_left hle]
  exact ⟨h16, h17, h18, h19⟩

/-- The actual independently defined common policy supplies the history,
firstStop and NEW inherited cap guard for every one of the eleven genuine
remaining ascending banks. No source/parent outcome is requested as a premise. -/
theorem actual_common_slots1619 (c : RemainingCell)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot16 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        M (point8 (N : ℝ) s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot17 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        M (point8 (N : ℝ) s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot18 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        M (point8 (N : ℝ) s.selectedPrefix) ∧
    P4AOriginalPrior58Chronology.slot19 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        M (point8 (N : ℝ) s.selectedPrefix) := by
  obtain ⟨hrows, hstop, hg⟩ := shared_frontier_CurrentParentGuard c d he N cap hN w z s hs
  exact ⟨hstop, source_slots1619 c (N : ℝ) _ s.selectedPrefix hrows hg⟩

/-- Ownership separation is carried to the real common prime/frontier
bank. It is not merely injectivity of eleven metadata labels. -/
theorem actual_common_bank_unique (c c' : RemainingCell)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected c d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)))
    (hs' : s ∈ selected c' d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) : c = c' := by
  by_contra hne
  have h := (shared_frontier_CurrentParentGuard c d he N cap hN w z s hs).1
  have h' := (shared_frontier_CurrentParentGuard c' d he N cap hN w z s hs').1
  exact source_disjoint c c' hne _ h h'

end
end ImbalancedChen.P4AOriginalRemainingAscendingSlots1619
