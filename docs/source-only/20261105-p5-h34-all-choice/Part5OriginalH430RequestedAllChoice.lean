import ImbalancedChen.Part5OriginalH430RequestedNonbankLevel

/-!
One exact manuscript-local, ALL-CHOICE partition of a generated request
level. SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

Only the chosen action is counted: one of 106 banks, one strict Buchstab
list, or one retained old cell. An exterior scalar request emits nothing.
The indices are original LIST positions, not products/catalog labels.
This does NOT identify the feedback history with U3/U4 source counts.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedAllChoice

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankLevel

/-- A single active request selects exactly one kind of next step,
including a specified-cell request whose choice differs from scalar lookup. -/
private theorem selected_case_partition (g : ℕ) (r : Request) (v : ℝ) :
    (if ∃ a : Original106Action, ∃ i : Fin 200,
        Selected g r i (.bank (slotOfAction a)) then v else 0) +
      (if ∃ i : Fin 200, Selected g r i .buchstab then v else 0) +
      (if ∃ i : Fin 200, Selected g r i .retained then v else 0) =
      if resolve (g+1) r = none then 0 else v := by
  cases hresolve : resolve (g+1) r with
  | none =>
      have hn (c : Choice) : ¬ ∃ i : Fin 200, Selected g r i c := by
        rintro ⟨i,hi⟩
        have hx := hi.1
        rw [hresolve] at hx
        cases hx
      have hb : ¬ ∃ a : Original106Action, ∃ i : Fin 200,
          Selected g r i (.bank (slotOfAction a)) := by
        rintro ⟨a,i,hi⟩
        exact hn _ ⟨i,hi⟩
      simp only [if_neg hb, if_neg (hn .buchstab), if_neg (hn .retained),
        hresolve, ite_true, add_zero]
  | some i =>
      cases hc : (roundDecision (iterate g) r.node.upper i).choice with
      | retained =>
          have hs : Selected g r i .retained := ⟨hresolve,hc⟩
          have hr : ∃ j : Fin 200, Selected g r j .retained := ⟨i,hs⟩
          have hb : ¬ ∃ a : Original106Action, ∃ j : Fin 200,
              Selected g r j (.bank (slotOfAction a)) := by
            rintro ⟨a,j,hj⟩
            have hx : (Choice.bank (slotOfAction a)) = .retained :=
              selected_choice_unique hj hs
            cases hx
          have hu : ¬ ∃ j : Fin 200, Selected g r j .buchstab := by
            rintro ⟨j,hj⟩
            have hx : Choice.buchstab = .retained :=
              selected_choice_unique hj hs
            cases hx
          simp only [if_neg hb, if_neg hu, if_pos hr, hresolve,
            reduceCtorEq, ite_false, zero_add]
      | buchstab =>
          have hs : Selected g r i .buchstab := ⟨hresolve,hc⟩
          have hu : ∃ j : Fin 200, Selected g r j .buchstab := ⟨i,hs⟩
          have hb : ¬ ∃ a : Original106Action, ∃ j : Fin 200,
              Selected g r j (.bank (slotOfAction a)) := by
            rintro ⟨a,j,hj⟩
            have hx : Choice.bank (slotOfAction a) = .buchstab :=
              selected_choice_unique hj hs
            cases hx
          have hr : ¬ ∃ j : Fin 200, Selected g r j .retained := by
            rintro ⟨j,hj⟩
            have hx : Choice.retained = .buchstab :=
              selected_choice_unique hj hs
            cases hx
          simp only [if_neg hb, if_pos hu, if_neg hr, hresolve,
            reduceCtorEq, ite_false, add_zero, zero_add]
      | bank k =>
          have hs : Selected g r i (.bank k) := ⟨hresolve,hc⟩
          have hb : ∃ a : Original106Action, ∃ j : Fin 200,
              Selected g r j (.bank (slotOfAction a)) :=
            ⟨actionOfSlot k,i,by simpa only [slot_action] using hs⟩
          have hu : ¬ ∃ j : Fin 200, Selected g r j .buchstab := by
            rintro ⟨j,hj⟩
            have hx : Choice.buchstab = .bank k :=
              selected_choice_unique hj hs
            cases hx
          have hr : ¬ ∃ j : Fin 200, Selected g r j .retained := by
            rintro ⟨j,hj⟩
            have hx : Choice.retained = .bank k :=
              selected_choice_unique hj hs
            cases hx
          simp only [if_pos hb, if_neg hu, if_neg hr, hresolve,
            reduceCtorEq, ite_false, add_zero]

/-- Exact list-position partition for ANY signed test, without quotienting
equal integer products and without counting an unselected offer. -/
theorem exact_level_partition (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (F : Index N n root tau p g → ℝ) :
    ((∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l) +
      (∑ l ∈ selectedBuchstabLevel N n root tau p g, F l)) +
      (∑ l ∈ selectedRetainedLevel N n root tau p g, F l) =
      ∑ l : Index N n root tau p g,
        if resolve (g.val+1) (levelOccurrence l).current = none then 0 else F l := by
  rw [sum_selectedLevel]
  simp only [selectedBuchstabLevel, selectedRetainedLevel, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  exact selected_case_partition g.val (levelOccurrence l).current (F l)

/-- The actual generated one-generation child value, using the actual
previous array and the exact original edge weights. -/
def generationValue (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l * edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

/-- Exact, three-way one-step value identity. The retained contribution
is the existing retainedLevelValue (and thus the old specified cell);
no prime sum, integral, count inequality or rounding charge is assumed. -/
theorem generationValue_partition (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    generationValue N n root tau p g =
      ((∑ a : Original106Action,
         ∑ l ∈ selectedLevel N n root tau p g a,
           levelMark l * edgeValue (rootQ N n root tau p) (iterate g.val)
             (levelOccurrence l).current
             (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)) +
       (∑ l ∈ selectedBuchstabLevel N n root tau p g,
         levelMark l * edgeValue (rootQ N n root tau p) (iterate g.val)
           (levelOccurrence l).current
           (children N (rootQ N n root tau p) g.val (levelOccurrence l).current))) +
       retainedLevelValue N n root tau p g := by
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l * edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)
  have hv : generationValue N n root tau p g =
      ∑ l : Index N n root tau p g,
        if resolve (g.val+1) (levelOccurrence l).current = none then 0 else F l := by
    unfold generationValue
    apply Finset.sum_congr rfl
    intro l _
    cases hr : resolve (g.val+1) (levelOccurrence l).current with
    | none => simp [F, children, hr, edgeValue]
    | some i => simp only [hr, reduceCtorEq, ite_false]
  calc
    generationValue N n root tau p g =
      ∑ l : Index N n root tau p g,
        if resolve (g.val+1) (levelOccurrence l).current = none then 0 else F l := hv
    _ = _ := by
      simpa only [F, retainedLevelValue] using
        (exact_level_partition N n root tau p g F).symm

end
end ImbalancedChen.Part5OriginalH430RequestedAllChoice
