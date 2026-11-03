import ImbalancedChen.P4AOriginalFull87HistoryCore
import ImbalancedChen.P4AOriginalFull87SourceDispatch

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Compact inner trims of the EXACT original87 strict affine sources.  All
stored rows are retained through their original evaluators, with no new
payload or decoder.  The extra margins are consequences of those sources:
positive cap, actual comparison improvement, all full/selected squares.
These trims include the preceding common history core, and exhaust every
original source point.  Equality/inherit points are not declared sources.
No integral saving, archive gain or buffered density reserve is inferred.
-/
namespace ImbalancedChen.P4AOriginalFull87StrictActionTrim
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope P4AOriginalFull87SourceDictionary

/-- Preserve each source family's exact original strict-row alphabet. -/
def rowCount : Cell → ℕ
  | .remaining c => P4AOriginalRemainingEighthSources.rowCount c
  | .descending _ => 96
  | .ascendingPair _ => 97
  | .h3 _ => 99

def rowValue : (c : Cell) → Fin (rowCount c) → Point → ℝ
  | .remaining c, r =>
      P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row c r)
  | .descending i, r =>
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r)
  | .ascendingPair i, r =>
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r)
  | .h3 i, r =>
      P4AOriginalFirstFailureH3Literal.evalAffine
        (P4AOriginalFirstFailureH3Literal.sourceAffineRows i r).2

theorem source_iff_rows (c : Cell) (t : Point) :
    Source c t ↔ ∀ r : Fin (rowCount c), 0 < rowValue c r t := by
  cases c <;> rfl

theorem rowValue_continuous (c : Cell) (r : Fin (rowCount c)) :
    Continuous (rowValue c r) := by
  cases c <;>
    dsimp [rowValue, P4AOriginalRemainingEighthSources.evalRow,
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
      P4AOriginalFirstFailureH3Literal.evalAffine] <;> fun_prop

def sourceSet (c : Cell) : Set Point := {t | Source c t}

theorem sourceSet_measurable (c : Cell) : MeasurableSet (sourceSet c) := by
  have heq : sourceSet c = ⋂ r : Fin (rowCount c), {t | 0 < rowValue c r t} := by
    ext t
    simp only [sourceSet, mem_setOf_eq, mem_iInter, source_iff_rows]
  rw [heq]
  exact MeasurableSet.iInter fun r =>
    (isOpen_lt continuous_const (rowValue_continuous c r)).measurableSet

theorem newCap_continuous (c : Cell) : Continuous (newCap c) := by
  cases c with
  | remaining c =>
      dsimp only [newCap, P4AOriginalRemainingEighthSources.newCap]
      split_ifs <;>
        dsimp [P4AOriginalRemainingEighthSources.selectedSum, A, C] <;> fun_prop
  | descending i =>
      dsimp [newCap, P2OriginalDescendingEighthLogSemantics.newCap,
        P2OriginalDescendingEighthLogSemantics.selectedSum, C]
      fun_prop
  | ascendingPair i =>
      dsimp [newCap, P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
        P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum, A]
      fun_prop
  | h3 i =>
      dsimp [newCap, P4AOriginalFirstFailureH3Literal.M8,
        P4AOriginalFirstFailureH3Literal.A]
      fun_prop

theorem comparison_continuous (c : Cell) : Continuous (comparison c) := by
  cases c with
  | remaining c =>
      cases c <;> dsimp [comparison, P4AOriginalRemainingEighthSources.comparison,
        A, C] <;> fun_prop
  | descending i =>
      dsimp [comparison, P2OriginalDescendingEighthLogSemantics.oldRaw,
        P2OriginalDescendingEighthLogSemantics.d, C]
      fun_prop
  | ascendingPair i =>
      dsimp [comparison, P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap, A]
      fun_prop
  | h3 i =>
      dsimp [comparison, P4AOriginalFirstFailureH3Literal.R6,
        P4AOriginalFirstFailureH3Literal.A]
      fun_prop

inductive Margin where
  | positive
  | improvement
  | full (j : Fin 8)
  | complement (j : Fin 8)
  deriving DecidableEq, Fintype

/-- Selected slots impose no new complementary-square requirement. -/
def actionSlack (c : Cell) (t : Point) : Margin → ℝ
  | .positive => newCap c t
  | .improvement => newCap c t - comparison c t
  | .full j => newCap c t - prefixSquareExpr t j
  | .complement j =>
      if j ∈ selected c then newCap c t
      else newCap c t - selectedSquareExpr (selected c) t j

theorem actionSlack_continuous (c : Cell) (j : Margin) :
    Continuous (fun t => actionSlack c t j) := by
  cases j with
  | positive => exact newCap_continuous c
  | improvement => exact (newCap_continuous c).sub (comparison_continuous c)
  | full j => exact (newCap_continuous c).sub (continuous_prefixSquareExpr j)
  | complement j =>
      by_cases hj : j ∈ selected c
      · simpa only [actionSlack, if_pos hj] using newCap_continuous c
      · simpa only [actionSlack, if_neg hj] using
          (newCap_continuous c).sub (continuous_selectedSquareExpr (selected c) j)

theorem source_actionSlack_pos {c : Cell} {t : Point} (hs : Source c t)
    (j : Margin) : 0 < actionSlack c t j := by
  cases j with
  | positive => exact P4AOriginalFull87SourceDispatch.source_cap_positive hs
  | improvement => exact sub_pos.mpr (source_improvement_terminal hs).1
  | full j => exact sub_pos.mpr ((source_full_selected hs).1 j)
  | complement j =>
      by_cases hj : j ∈ selected c
      · simpa only [actionSlack, if_pos hj] using
          P4AOriginalFull87SourceDispatch.source_cap_positive hs
      · simpa only [actionSlack, if_neg hj] using
          sub_pos.mpr ((source_full_selected hs).2 j hj)

/-- Unlike Source intersect the old history core, this entire set is
closed and compact.  Every strict source row has the same positive floor. -/
def trim (c : Cell) (delta : ℝ) : Set Point :=
  P4AOriginalFull87HistoryCore.core delta ∩
    (⋂ r : Fin (rowCount c), {t | delta ≤ rowValue c r t}) ∩
    (⋂ j : Margin, {t | delta ≤ actionSlack c t j})

theorem mem_trim (c : Cell) (delta : ℝ) (t : Point) :
    t ∈ trim c delta ↔
      t ∈ P4AOriginalFull87HistoryCore.core delta ∧
      (∀ r : Fin (rowCount c), delta ≤ rowValue c r t) ∧
      (∀ j : Margin, delta ≤ actionSlack c t j) := by
  simp only [trim, mem_inter_iff, mem_iInter, mem_setOf_eq, and_assoc]

theorem isClosed_trim (c : Cell) (delta : ℝ) : IsClosed (trim c delta) :=
  ((P4AOriginalFull87HistoryCore.isClosed_core delta).inter
    (isClosed_iInter fun r => isClosed_le continuous_const (rowValue_continuous c r))).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (actionSlack_continuous c j))

theorem trim_subset_core (c : Cell) (delta : ℝ) :
    trim c delta ⊆ P4AOriginalFull87HistoryCore.core delta :=
  fun t ht => ((mem_trim c delta t).mp ht).1

theorem isCompact_trim (c : Cell) (delta : ℝ) : IsCompact (trim c delta) :=
  (P4AOriginalFull87HistoryCore.isCompact_core delta).of_isClosed_subset
    (isClosed_trim c delta) (trim_subset_core c delta)

theorem trim_subset_source (c : Cell) {delta : ℝ} (hd : 0 < delta) :
    trim c delta ⊆ sourceSet c := by
  intro t ht
  apply (source_iff_rows c t).mpr
  exact fun r => hd.trans_le (((mem_trim c delta t).mp ht).2.1 r)

theorem trim_antitone (c : Cell) {delta eta : ℝ} (h : delta ≤ eta) :
    trim c eta ⊆ trim c delta := by
  intro t ht
  obtain ⟨hc, hr, ha⟩ := (mem_trim c eta t).mp ht
  exact (mem_trim c delta t).mpr
    ⟨P4AOriginalFull87HistoryCore.core_antitone h hc,
      fun r => h.trans (hr r), fun j => h.trans (ha j)⟩

/-- Pointwise exhaustion uses ALL original rows and all action margins.
There is no assumption of a uniform positive gap on an open source. -/
theorem source_eventually_trimmed {c : Cell} {t : Point} (hs : Source c t) :
    ∀ᶠ n : ℕ in atTop, t ∈ trim c (P4AOriginalFull87HistoryCore.width n) := by
  have hr : ∀ᶠ n : ℕ in atTop, ∀ r : Fin (rowCount c),
      P4AOriginalFull87HistoryCore.width n < rowValue c r t := by
    apply eventually_all.mpr
    intro r
    exact P4AOriginalFull87HistoryCore.width_tendsto.eventually
      (gt_mem_nhds ((source_iff_rows c t).mp hs r))
  have ha : ∀ᶠ n : ℕ in atTop, ∀ j : Margin,
      P4AOriginalFull87HistoryCore.width n < actionSlack c t j := by
    apply eventually_all.mpr
    intro j
    exact P4AOriginalFull87HistoryCore.width_tendsto.eventually
      (gt_mem_nhds (source_actionSlack_pos hs j))
  filter_upwards [P4AOriginalFull87HistoryCore.source_eventually_in_core hs, hr, ha]
    with n hc hn hm
  exact (mem_trim _ _ _).mpr ⟨hc, fun r => (hn r).le, fun j => (hm j).le⟩

theorem source_eq_iUnion_trim (c : Cell) :
    sourceSet c = ⋃ n : ℕ, trim c (P4AOriginalFull87HistoryCore.width n) := by
  ext t
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := (source_eventually_trimmed hs).exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact trim_subset_source c (P4AOriginalFull87HistoryCore.width_pos n) hn

theorem trim_owner_unique {c d : Cell} {delta : ℝ} (hd : 0 < delta)
    {t : Point} (hc : t ∈ trim c delta) (he : t ∈ trim d delta) : c = d :=
  P4AOriginalFull87Ownership.source_owner_unique
    (trim_subset_source c hd hc) (trim_subset_source d hd he)

end
end ImbalancedChen.P4AOriginalFull87StrictActionTrim
