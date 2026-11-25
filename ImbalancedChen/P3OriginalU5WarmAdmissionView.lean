import ImbalancedChen.P3OriginalU5WarmCapCodeStability

/-!
# Reading the actual warm trace through the existing first-decision API

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

`admissionView` only reads the existing `run` and `admission`; it is not a
replacement retained policy or a new coefficient. Its Boolean polarity is
ignored because the literal admission already includes the odd bypass.
The bridge retains the incoming accepted flag and every ancestor test.
-/

namespace ImbalancedChen.P3OriginalU5WarmAdmissionView

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P4AUpperTaggedFirstPrefixDisagreement

def admissionView {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (_positive : Bool) : List ℝ → Bool
  | [] => true
  | x :: pre => decide (admission (run P a b base pre.reverse) x)

/-- An exact conjunction identity, including the incoming accepted flag. -/
theorem run_accepted_iff_view {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (xs : List ℝ) :
    ∀ (pre : List ℝ) (positive : Bool),
      (run P a b (run P a b base pre.reverse) xs).accepted = true ↔
        (run P a b base pre.reverse).accepted = true ∧
          FirstExitValidSelection (admissionView P a b base) pre positive xs := by
  induction xs with
  | nil =>
      intro pre positive
      simp only [run, List.foldl_nil, FirstExitValidSelection, and_true]
  | cons x xs ih =>
      intro pre positive
      have hnext : run P a b base (x :: pre).reverse =
          step P a b (run P a b base pre.reverse) x := by
        rw [List.reverse_cons, run_append]
        rfl
      change (run P a b (step P a b (run P a b base pre.reverse) x) xs).accepted =
        true ↔ _
      rw [← hnext, ih (x :: pre) (!positive), hnext, step_accepted_iff]
      simp only [FirstExitValidSelection, admissionView, decide_eq_true_eq, and_assoc]

theorem decisionAt_admissionView {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (xs : List ℝ) (k : ℕ) (hk : k < xs.length) :
    decisionAt (admissionView P a b base) [] true xs k =
      decide (admission (run P a b base (xs.take k)) xs[k]) := by
  rw [decisionAt_eq_prefix _ _ _ _ _ hk, List.take_succ_eq_append_getElem hk]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.append_nil, admissionView, List.reverse_reverse]

/-- The old generic first-disagreement theorem is applied to the exact
admission view. The last conjunct retains the earlier decisions verbatim. -/
theorem first_actual_admission_difference {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (hbase : base.accepted = true)
    (xs ys : List ℝ) (hlen : xs.length = ys.length)
    (hdiff : ¬((run P a b base xs).accepted = true ↔
      (run P a b base ys).accepted = true)) :
    ∃ k : ℕ, ∃ hk : k < xs.length,
      ¬(admission (run P a b base (xs.take k)) xs[k] ↔
        admission (run P a b base (ys.take k)) (getElem ys k (by omega))) ∧
      ∀ i : ℕ, i < k →
        decisionAt (admissionView P a b base) [] true xs i =
          decisionAt (admissionView P a b base) [] true ys i := by
  have hx : (run P a b base xs).accepted = true ↔
      FirstExitValidSelection (admissionView P a b base) [] true xs := by
    simpa only [List.reverse_nil, run, List.foldl_nil, hbase, true_and] using
      run_accepted_iff_view P a b base xs [] true
  have hy : (run P a b base ys).accepted = true ↔
      FirstExitValidSelection (admissionView P a b base) [] true ys := by
    simpa only [List.reverse_nil, run, List.foldl_nil, hbase, true_and] using
      run_accepted_iff_view P a b base ys [] true
  have hd : ¬(FirstExitValidSelection (admissionView P a b base) [] true xs ↔
      FirstExitValidSelection (admissionView P a b base) [] true ys) := by
    intro h
    exact hdiff (hx.trans (h.trans hy.symm))
  obtain ⟨k, hk, hneq, hbefore⟩ := validSelection_disagreement_first_decision
    (admissionView P a b base) xs ys hlen [] [] true hd
  refine ⟨k, hk, ?_, hbefore⟩
  intro h
  apply hneq
  rw [decisionAt_admissionView _ _ _ _ _ _ hk,
    decisionAt_admissionView _ _ _ _ _ _ (show k < ys.length by omega)]
  exact congrArg decide (propext h)

end
end ImbalancedChen.P3OriginalU5WarmAdmissionView
