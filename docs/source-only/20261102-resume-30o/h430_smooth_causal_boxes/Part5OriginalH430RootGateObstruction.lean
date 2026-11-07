import ImbalancedChen.Part5OriginalH430FrozenRootRefinement

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An exact obstruction to a whole-U3 realization using the existing M
root encoding and the existing `fullGates` predicate.  The selected root
prime is stored in `slots`, so `fullGates` tests its square.  On the
original U3 tail this square fails before any refinement.  Lowering Q,
adding smooth labels, or appending descendants cannot repair it.

This is a source-interface obstruction.  It is not a counterexample to
the manuscript's ordinary marked-count estimate: a different justified
root/full-history dictionary may distinguish an external selected mark
from the chronological slots to which a full square test applies.
-/

namespace ImbalancedChen.Part5OriginalH430RootGateObstruction

noncomputable section
open Set
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5UpperTables Part5UpperTables.OriginalU34

theorem sourceRoot_fullGates_iff (k : Root) (tau t : ℝ) :
    fullGates (sourceRoot k tau t).physical ↔ t ≤ sourceResidual k tau t := by
  simp only [fullGates, word, sourceRoot, List.map_cons, List.map_nil,
    SquareGates, zero_add, and_true]
  constructor <;> intro h <;> linarith

theorem sourceRoot_selectedGates (k : Root) (tau t : ℝ) :
    selectedGates (sourceRoot k tau t).physical := by
  simp [selectedGates, sourceRoot, selectedWord, remainingWord, SquareGates]

theorem source_U3_tail_not_fullGates {tau t : ℝ}
    (htau : 0 ≤ tau) (htail : tailCutoff ≤ t) :
    ¬ fullGates (sourceRoot .U3 tau t).physical := by
  rw [sourceRoot_fullGates_iff]
  have hcut : (1 / 4 : ℝ) < tailCutoff := by norm_num [tailCutoff]
  simp only [sourceResidual, U3Residual, if_neg (not_lt_of_ge htail), tailResidual]
  intro h
  linarith

theorem frozenRoot_fullGates_iff (n : ℕ) (k : Root) (tau t : ℝ) :
    fullGates (frozenRoot n k tau t).physical ↔
      2 * t ≤ frozenLevel n (sourceRoot k tau t).physical.total := by
  simp [fullGates, frozenRoot, word, sourceRoot, SquareGates]

theorem frozenRoot_fullGates_implies_source {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hf : fullGates (frozenRoot n k tau t).physical) :
    fullGates (sourceRoot k tau t).physical := by
  have hl := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  rw [frozenRoot_fullGates_iff] at hf
  rw [sourceRoot_fullGates_iff]
  change frozenLevel n (sourceRoot k tau t).physical.total ≤
    t + sourceResidual k tau t at hl
  linarith

theorem frozen_U3_tail_not_fullGates {n : ℕ} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand .U3) (htail : tailCutoff ≤ t) :
    ¬ fullGates (frozenRoot n .U3 tau t).physical :=
  fun hf => source_U3_tail_not_fullGates htau htail
    (frozenRoot_fullGates_implies_source htau htauhi ht hf)

/-- Every original full square remains a literal conjunct after any
Program, regardless of local membership or numerical generation labels. -/
theorem realize_fullGates_implies_root {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth)
    (hf : fullGates (realize depth n code z).physical) : fullGates n.physical := by
  obtain ⟨suffix, hs⟩ := realize_prefix n code z
  unfold fullGates word at hf
  rw [realize_total] at hf
  rw [hs, List.map_append, squareGates_append_iff] at hf
  exact hf.1

/-- In particular, no smooth support or physical arithmetic tuple can
meet the requested existing full-square predicate on this whole tail. -/
theorem tail_no_full_square_realization {n mesh depth : ℕ} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand .U3) (htail : tailCutoff ≤ t)
    (code : Program mesh depth) (z : Coordinates depth) :
    ¬ fullGates (realize depth (frozenRoot n .U3 tau t) code z).physical := by
  intro hf
  exact frozen_U3_tail_not_fullGates htau htauhi ht htail
    (realize_fullGates_implies_root _ code z hf)

/-- The obstruction contains a nonempty open interval of original root
coordinates; it is not an endpoint which a proper-wall payment removes. -/
theorem original_tail_open_interval :
    (Ioo tailCutoff (1 / 3 : ℝ)).Nonempty ∧
      Ioo tailCutoff (1 / 3 : ℝ) ⊆ rootBand .U3 := by
  constructor
  · exact Set.nonempty_Ioo.mpr (by norm_num [tailCutoff])
  · intro t ht
    refine ⟨?_, ht.2.le⟩
    exact (by norm_num [Part5OriginalUpsilon5CausalDictionary.a, tailCutoff] :
      Part5OriginalUpsilon5CausalDictionary.a ≤ tailCutoff).trans ht.1.le

end
end ImbalancedChen.Part5OriginalH430RootGateObstruction
