import ImbalancedChen.Part5OriginalH430FirstRoundSourcePartition

/-!
P5.6 / h34: exact FIRST-round upper support cutoff at physical index 100.

The literal 106-row bank has NO target >= 100. The first upper
ordinary action retains the original seed because the lower seed is
identically zero; that upper seed is zero at indices >= 60. Hence the
first upper output is zero at 100..199. Combined with the established
lower first-round support 50..108, only 100 upper and 59 lower physical
cells can be nonzero in round one.

This is an unconditional producer support statement, not an F
inequality, not the first-round positive-source payment, and not an
all-430 CLOSED-CELL proof. The row-target finite check uses ordinary
Lean decidability, not a native/unsafe certificate.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport
noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430Q80InitialSupport
open Part5OriginalUpsilon5CausalDictionary (floorValue)

/-- Exhaustive check on the actual 106-row target lists; their
largest physical target is 99, including all 36 non-W1 rows.
This is about the literal rows, not an assumed generic target bound. -/
theorem original_106_targets_below_hundred :
    ∀ k : Fin 106, ∀ j ∈ (rows k).targets, j < 100 := by
  intro k
  fin_cases k <;> decide

theorem original_bank_untargeted_from_hundred
    (i : Fin 200) (hi : 100 ≤ i.val) (k : Fin 106) :
    i.val ∉ (rows k).targets := by
  intro htarget
  have hlt := original_106_targets_below_hundred k i.val htarget
  omega

/-- Actual scan induction: rows without this physical target
do not change the decision or its provenance. -/
private theorem scan_unchanged_when_no_row_targets
    (old : Table) (i : Fin 200) (ks : List (Fin 106)) :
    ∀ d : Decision,
      (∀ k ∈ ks, i.val ∉ (rows k).targets) →
      scan old i ks d = d := by
  induction ks with
  | nil =>
      intro d _
      rfl
  | cons k ks ih =>
      intro d hnone
      have hk : i.val ∉ (rows k).targets :=
        hnone k (by simp)
      have htail : ∀ j ∈ ks, i.val ∉ (rows j).targets := by
        intro j hj
        exact hnone j (by simp [hj])
      change scan old i ks (offerRow old i d k) = d
      have hrow : offerRow old i d k = d := by
        simp [offerRow, hk]
      rw [hrow]
      exact ih d htail

/-- Upper cells 100..199 are all ZERO at the ACTUAL first update.
No hypothetical ceiling or analytic envelope is required. -/
theorem first_upper_round_zero_from_hundred
    (i : Fin 200) (hi : 100 ≤ i.val) :
    iterate 1 true i = 0 := by
  have hnone : ∀ k ∈ List.finRange 106,
      i.val ∉ (rows k).targets := by
    intro k _
    exact original_bank_untargeted_from_hundred i hi k
  have hscan :=
    scan_unchanged_when_no_row_targets seed i (List.finRange 106)
      (⟨seed true i, Choice.retained⟩ : Decision) hnone
  rw [first_upper_round_is_exact_bank_scan, hscan]
  have h60 : ¬ i.val < 60 := by omega
  simp [seed, h60]

/-- Genuine support of BOTH 200-cell Q80 tables after the first round.
Every position outside the 100-upper/59-lower window is exactly zero. -/
theorem first_round_outside_active_window_zero
    (upper : Bool) (i : Fin 200)
    (houtside :
      (upper = true ∧ 100 ≤ i.val) ∨
      (upper = false ∧ (i.val < 50 ∨ 109 ≤ i.val))) :
    iterate 1 upper i = 0 := by
  rcases houtside with ⟨hu, hi⟩ | ⟨hu, hi⟩
  · subst upper
    exact first_upper_round_zero_from_hundred i hi
  · subst upper
    rcases hi with hi | hi
    · exact lower_first_fifty_zero 1 i hi
    · exact first_lower_tail_zero i hi

/-- Converse, with no claim that every eligible position is positive.
The first producer step has at most 159 possibly nonzero positions. -/
theorem first_round_nonzero_only_inside_active_window
    (upper : Bool) (i : Fin 200)
    (hnonzero : iterate 1 upper i ≠ 0) :
    (upper = true ∧ i.val < 100) ∨
    (upper = false ∧ 50 ≤ i.val ∧ i.val < 109) := by
  cases upper with
  | false =>
      obtain ⟨h50, h109⟩ :=
        first_lower_nonzero_only_in_fifty_to_108 i hnonzero
      exact Or.inr ⟨rfl, h50, h109⟩
  | true =>
      have h100 : i.val < 100 := by
        by_contra hn
        exact hnonzero
          (first_upper_round_zero_from_hundred i (by omega))
      exact Or.inl ⟨rfl, h100⟩

/-- At all 241 inactive physical cells, first-round CLOSED-CELL needs
only nonnegativity of the UNCHANGED F at its actual query location.
This does not assert that nonnegativity or the positive 159-cell bounds. -/
theorem inactive_first_round_floor_le_F
    (F : Bool → ℝ → ℝ) (upper : Bool) (i : Fin 200) (s : ℝ)
    (houtside :
      (upper = true ∧ 100 ≤ i.val) ∨
      (upper = false ∧ (i.val < 50 ∨ 109 ≤ i.val)))
    (hs : s ∈ queryCell i)
    (hF : (0 : ℝ) ≤ F upper s) :
    floorValue (iterate 1 upper) i ≤ F upper s := by
  have hzero := first_round_outside_active_window_zero upper i houtside
  simpa [floorValue, hzero] using hF

end
end ImbalancedChen.Part5OriginalH430FirstRoundActiveSupport
