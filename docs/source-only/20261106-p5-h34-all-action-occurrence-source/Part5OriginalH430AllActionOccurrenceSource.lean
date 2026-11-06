import ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply

/-!
P5.6 / h34: exact all-action source partition for the ACTUAL request level.

This is a manuscript-internal predecessor-level identity, not an assumed
count estimate. Every selected request is precisely retained, Buchstab,
or one of the original 106 bank actions. The split uses the computed
roundDecision on the genuine generation and the actual read mode.
Repeated tagged paths retain distinct Fin indices and their exact mark.
Outside scalar reads contribute exactly zero by resolve_none_value.

This supplies the combinatorial source partition and the literal selected
retention/Buchstab child lists needed before the still-open all-action
closed-cell *inequality*. It does not establish Buchstab mass estimates,
base/seed, original U3/U4 count equality or the 430+11 refinement.

SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430AllActionOccurrenceSource

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply

/-- Retention is classified on actual level-list positions, not on
an auxiliary catalog of products or by the scalar owner alone. -/
def retainedLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ i : Fin 200, Selected g.val (levelOccurrence l).current i .retained)

/-- Both original Buchstab polarities use the SAME chosen action tag,
but their real children retain the original upper/lower flag. -/
def buchstabLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ i : Fin 200, Selected g.val (levelOccurrence l).current i .buchstab)

/-- The chosen action is unique even when a specified-cell read and
a scalar closed-min read would choose DIFFERENT cells. This concerns
one fixed actual Request, and never equates those two read modes. -/
theorem selected_choice_unique {g : ℕ} {r : Request}
    {i j : Fin 200} {c d : Choice}
    (hc : Selected g r i c) (hd : Selected g r j d) : c = d := by
  have hij : i = j := Option.some.inj (hc.1.symm.trans hd.1)
  subst j
  exact hc.2.symm.trans hd.2

/-- Three mutually exclusive original action types exhaust every
actually RESOLVED request. No assumption on a synthetic selected set. -/
theorem choice_three_indicator (g : ℕ) (r : Request) (v : ℝ) :
    (if ∃ i : Fin 200, Selected g r i .retained then v else 0) +
    (if ∃ i : Fin 200, Selected g r i .buchstab then v else 0) +
    (if ∃ a : Original106Action, ∃ i : Fin 200,
      Selected g r i (.bank (slotOfAction a)) then v else 0) =
    (if ∃ i : Fin 200, resolve (g+1) r = some i then v else 0) := by
  classical
  by_cases hactive : ∃ i : Fin 200, resolve (g+1) r = some i
  · obtain ⟨i,hi⟩ := hactive
    have hact : ∃ j : Fin 200, resolve (g+1) r = some j := ⟨i,hi⟩
    cases hc : (roundDecision (iterate g) r.node.upper i).choice with
    | retained =>
        have hs : Selected g r i .retained := ⟨hi,hc⟩
        have hr : ∃ j : Fin 200, Selected g r j .retained := ⟨i,hs⟩
        have hb : ¬∃ j : Fin 200, Selected g r j .buchstab := by
          rintro ⟨j,hj⟩
          have h := selected_choice_unique hs hj
          cases h
        have hk : ¬∃ a : Original106Action, ∃ j : Fin 200,
            Selected g r j (.bank (slotOfAction a)) := by
          rintro ⟨a,j,hj⟩
          have h := selected_choice_unique hs hj
          cases h
        simp [hr,hb,hk,hact]
    | buchstab =>
        have hs : Selected g r i .buchstab := ⟨hi,hc⟩
        have hb : ∃ j : Fin 200, Selected g r j .buchstab := ⟨i,hs⟩
        have hr : ¬∃ j : Fin 200, Selected g r j .retained := by
          rintro ⟨j,hj⟩
          have h := selected_choice_unique hs hj
          cases h
        have hk : ¬∃ a : Original106Action, ∃ j : Fin 200,
            Selected g r j (.bank (slotOfAction a)) := by
          rintro ⟨a,j,hj⟩
          have h := selected_choice_unique hs hj
          cases h
        simp [hr,hb,hk,hact]
    | bank k =>
        have hs : Selected g r i (.bank k) := ⟨hi,hc⟩
        have hk : ∃ a : Original106Action, ∃ j : Fin 200,
            Selected g r j (.bank (slotOfAction a)) :=
          ⟨actionOfSlot k,i,by simpa only [slot_action] using hs⟩
        have hr : ¬∃ j : Fin 200, Selected g r j .retained := by
          rintro ⟨j,hj⟩
          have h := selected_choice_unique hj hs
          cases h
        have hb : ¬∃ j : Fin 200, Selected g r j .buchstab := by
          rintro ⟨j,hj⟩
          have h := selected_choice_unique hj hs
          cases h
        simp [hr,hb,hk,hact]
  · have hnone (c : Choice) : ¬∃ i : Fin 200, Selected g r i c := by
      rintro ⟨i,hi⟩
      exact hactive ⟨i,hi.1⟩
    have hk : ¬∃ a : Original106Action, ∃ i : Fin 200,
        Selected g r i (.bank (slotOfAction a)) := by
      rintro ⟨a,i,hi⟩
      exact hactive ⟨i,hi.1⟩
    simp [hactive,hnone,hk]

/-- Every genuine retained request has ONE unchanged-parent child,
with the specified-cell mode rather than the old scalar owner. -/
theorem selected_retained_children {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hs : Selected g r i .retained) :
    children N Q g r = [Edge.retained i] := by
  simp only [children,hs.1,hs.2,branchEdges]

/-- The actual retained contribution uses the preceding table at its
selected cell. No extra historic mark or count weight is inserted. -/
theorem selected_retained_value {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hs : Selected g r i .retained) :
    edgeValue Q (iterate g) r (children N Q g r) =
      thetaAtom N Q (parentProduct r.old) *
        floorValue (iterate g r.node.upper) i := by
  rw [selected_retained_children hs]
  exact retained_edgeValue N Q (iterate g) r i

/-- Both upper and lower Buchstab requests expand the original
strict prime carrier, never the union of all possible bank actions. -/
theorem selected_buchstab_children {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hs : Selected g r i .buchstab) :
    children N Q g r =
      (singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling).toList.map (.buchstab r.node.upper) := by
  simp only [children,hs.1,hs.2,branchEdges]

/-- Signed sums over all selected bank slots have already been proved
in RequestedLevelBankSupply. Extend that exact partition to the other
TWO action kinds at the SAME level and over its actual list indices. -/
theorem level_action_partition (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (F : Index N n root tau p g → ℝ) :
    (∑ l ∈ retainedLevel N n root tau p g, F l) +
    (∑ l ∈ buchstabLevel N n root tau p g, F l) +
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a, F l) =
    ∑ l : Index N n root tau p g,
      if ∃ i : Fin 200,
        resolve (g.val+1) (levelOccurrence l).current = some i
      then F l else 0 := by
  classical
  rw [sum_selectedLevel]
  simp only [retainedLevel,buchstabLevel,Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  exact choice_three_indicator g.val (levelOccurrence l).current (F l)

/-- The zero outside the actual resolver is justified by the original
scalar CLOSED read. A specified-cell read is always resolved. -/
theorem exterior_level_value_zero (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    (∑ l : Index N n root tau p g,
      if ∃ i : Fin 200,
        resolve (g.val+1) (levelOccurrence l).current = some i
      then levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current
      else 0) =
    (∑ l : Index N n root tau p g,
      levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current) := by
  classical
  apply Finset.sum_congr rfl
  intro l _
  by_cases ha : ∃ i : Fin 200,
      resolve (g.val+1) (levelOccurrence l).current = some i
  · simp [ha]
  · have hn : resolve (g.val+1) (levelOccurrence l).current = none := by
      cases hr : resolve (g.val+1) (levelOccurrence l).current with
      | none => rfl
      | some i => exact (ha ⟨i,hr⟩).elim
    have hv : requestValue (iterate (g.val+1)) (levelOccurrence l).current = 0 :=
      resolve_none_value (generation := g.val+1) hn
    simp [ha,hv]

/-- Literal one-level ALL-ACTION source identity. It is valid for
arbitrary original physical roots and read modes WITHOUT assuming a
count theorem. Multiplicities are the real level-list positions and
every summand retains the computed positive path mark. -/
theorem full_level_action_source (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    (∑ l : Index N n root tau p g,
      levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current) =
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current) +
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current) +
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current) := by
  exact (exterior_level_value_zero N n root tau p g).symm.trans
    (level_action_partition N n root tau p g
      (fun l => levelMark l *
        requestValue (iterate (g.val+1)) (levelOccurrence l).current)).symm

end
end ImbalancedChen.Part5OriginalH430AllActionOccurrenceSource
