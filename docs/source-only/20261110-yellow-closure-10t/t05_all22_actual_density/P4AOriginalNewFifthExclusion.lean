import ImbalancedChen.P4AOriginalFull87RawChronology
import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs

/-! Identify the rank-five action of the frozen full87 implementation at
an original fifth tuple outside the old grid-400 bank. The statement
includes both the active finite-cap branch and its inactive fallback. -/
namespace ImbalancedChen.P4AOriginalNewFifthExclusion
noncomputable section
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1HistoricalFifthIndexedOwnerArchive (ArchiveIndex archiveRow)
open P1OriginalVariableFourthContinuation (finiteMax_eq_seed_of_outside)
open P1OriginalVariableFifthContinuation (eligible)
open P4AOriginalCompleteSixthChronology (data)
open P5OriginalCommonRefinedConstructor (exponent4 exponent5)
open P4AOriginalFull87FiniteParentCaps (cap4 cap5 fifth_same_guard_image)
open P4AOriginalFull87FiniteParentPolicy (active active_ancestor level4Exponent level5Exponent)

def outsideOld (t : Fin 5 → ℝ) : Prop := ∀ i : ArchiveIndex, t ∉ (archiveRow i).originalBox

theorem no_licensed_fifth_at (e : ℚ) (q : ℕ) (a : ℝ) (t : Fin 5 → ℝ)
    (hout : outsideOld t) :
    let d := data e q a
    ∀ row ∈ d.rows5, ¬eligible d.e d.chi d.m d.omega d.J5 row t := by
  intro row hr he
  obtain ⟨i, _, _, _, hdecode⟩ :=
    P1HistoricalFifthCommonPolicyInputs.full_archive_licensed_rows_source
      P5OriginalFourthFifthSourceInputs.originalRows4
      P5OriginalFourthFifthSourceInputs.originalAdmission4 e q ((e : ℝ) / 20) a row hr
  exact hout i (decodeFifthRows_source_geometry (archiveRow i) _ row hdecode t he.2.2).2.2.2

theorem common_fifth_eq_fourth_on_complement (e : ℚ) (q : ℕ) (a N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hout : outsideOld (primeHistoryLogCoordinates N 5 pre)) :
    exponent5 (data e q a) N pre = exponent4 (data e q a) N (rosserAncestor 4 pre) := by
  unfold exponent5
  rw [if_pos hlen]
  exact finiteMax_eq_seed_of_outside _ _ _ _ (no_licensed_fifth_at e q a _ hout)

/-- On a disjoint new fifth tuple the frozen implementation uses
exactly its own fourth ancestor, even after finite requantization. -/
theorem licensed_fifth_eq_fourth_on_complement (n : ℕ) (e : ℚ) (q : ℕ) (a N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hout : outsideOld (primeHistoryLogCoordinates N 5 pre)) :
    level5Exponent n e q a N pre =
      level4Exponent n e q a N (rosserAncestor 4 pre) := by
  have hold := no_licensed_fifth_at e q a _ hout
  have hparent := active_ancestor e q a N 4 (by decide) pre
  by_cases ha : active e q a N pre
  · simp only [level5Exponent, level4Exponent, if_pos ha, if_pos (hparent.mpr ha)]
    rw [fifth_same_guard_image n e q a N pre hlen]
    exact finiteMax_eq_seed_of_outside _ _ _ _ hold
  · have hna : ¬active e q a N (rosserAncestor 4 pre) := fun h => ha (hparent.mp h)
    simp only [level5Exponent, level4Exponent, if_neg ha, if_neg hna]
    exact common_fifth_eq_fourth_on_complement e q a N pre hlen hout

end
end ImbalancedChen.P4AOriginalNewFifthExclusion
