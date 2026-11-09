import ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply

/-!
P5.6 / h34 — the COMPLETE one-generation ACTUAL request-action partition.

The old requested-level theorem summed only the selected 106 bank actions.
This packet separates the same original resolved Fin LIST positions into
retention, Buchstab, and the original 106 bank actions, without asking for
an owner, a new generation map, or a substitute scalar read. The resolver
uses generation g+1; the winner reads iterate g.  Exterior unresolved
requests contribute exactly zero at iterate (g+1).

This is only a finite exact all-action SOURCE partition. It is not an
all-action CLOSED-CELL count induction, a full/selected/inherited owner,
an arithmetic U3/U4 source identity, or an analytic payment estimate.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply

/-- The original actual resolver, not a new action selector. -/
def actualChoice (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : Option Choice :=
  (resolve (g.val + 1) (levelOccurrence l).current).map
    (fun i => (roundDecision (iterate g.val)
      (levelOccurrence l).current.node.upper i).choice)

/-- Membership in a chosen action is literally the existing Selected predicate
at predecessor generation g, for either scalar or specified-cell reads. -/
theorem actual_choice_iff_selected
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) (c : Choice) :
    actualChoice N n root tau p g l = some c ↔
      ∃ i, Selected g.val (levelOccurrence l).current i c := by
  constructor
  · intro h
    cases hi : resolve (g.val + 1) (levelOccurrence l).current with
    | none =>
        simp [actualChoice, hi] at h
    | some i =>
        have hc :
            (roundDecision (iterate g.val)
              (levelOccurrence l).current.node.upper i).choice = c := by
          simpa [actualChoice, hi] using h
        exact ⟨i, ⟨hi, hc⟩⟩
  · rintro ⟨i, ⟨hi, hc⟩⟩
    simp [actualChoice, hi, hc]

/-- These are actual, indexed request occurrences, not product or catalog sets. -/
def retainedLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    actualChoice N n root tau p g l = some .retained)

def buchstabLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    actualChoice N n root tau p g l = some .buchstab)

def bankLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ a : Original106Action, ∃ i,
      Selected g.val (levelOccurrence l).current i (.bank (slotOfAction a)))

def resolvedLevel (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    (actualChoice N n root tau p g l).isSome)

/-- The 106 original rows, not an invented alternative bank, exhaust the
literal bank constructor.  The existing action-slot bijection is used. -/
theorem bank_level_iff_actual_bank
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) :
    l ∈ bankLevel N n root tau p g ↔
      ∃ k : Fin 106, actualChoice N n root tau p g l = some (.bank k) := by
  constructor
  · intro hl
    obtain ⟨a, i, hi⟩ := (Finset.mem_filter.mp hl).2
    exact ⟨slotOfAction a,
      (actual_choice_iff_selected N n root tau p g l _).2 ⟨i, hi⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ :=
      (actual_choice_iff_selected N n root tau p g l (.bank k)).1 hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨actionOfSlot k, i, ?_⟩⟩
    simpa only [slot_action] using hi

/-- Exact exhaustiveness of the ACTUAL generation g+1 resolver.
No exterior request and no other action is smuggled into the partition. -/
theorem resolved_level_partition
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    resolvedLevel N n root tau p g =
      retainedLevel N n root tau p g ∪
        (buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g) := by
  ext l
  rw [Finset.mem_union, Finset.mem_union,
    bank_level_iff_actual_bank N n root tau p g l]
  simp only [resolvedLevel, retainedLevel, buchstabLevel,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases hc : actualChoice N n root tau p g l with
  | none => simp [hc]
  | some c =>
      cases c with
      | retained => simp [hc]
      | buchstab => simp [hc]
      | bank k => simp [hc]

theorem retained_buchstab_disjoint
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Disjoint (retainedLevel N n root tau p g)
      (buchstabLevel N n root tau p g) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  have h1 := (Finset.mem_filter.mp hl).2
  have h2 := (Finset.mem_filter.mp hr).2
  rw [h1] at h2
  cases h2

theorem retained_bank_disjoint
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Disjoint (retainedLevel N n root tau p g)
      (bankLevel N n root tau p g) := by
  apply Finset.disjoint_left.mpr
  intro l hl hb
  have h1 := (Finset.mem_filter.mp hl).2
  obtain ⟨k, hk⟩ :=
    (bank_level_iff_actual_bank N n root tau p g l).1 hb
  rw [h1] at hk
  cases hk

theorem buchstab_bank_disjoint
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    Disjoint (buchstabLevel N n root tau p g)
      (bankLevel N n root tau p g) := by
  apply Finset.disjoint_left.mpr
  intro l hl hb
  have h1 := (Finset.mem_filter.mp hl).2
  obtain ⟨k, hk⟩ :=
    (bank_level_iff_actual_bank N n root tau p g l).1 hb
  rw [h1] at hk
  cases hk

/-- The existing bank-only sum is precisely the bank part of this
three-way partition; no duplicate original106Action wins a position. -/
theorem bank_level_sum_eq_original_106
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (F : Index N n root tau p g → ℝ) :
    (∑ l ∈ bankLevel N n root tau p g, F l) =
      ∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l := by
  simpa only [bankLevel, Finset.sum_filter] using
    (sum_selectedLevel N n root tau p g F).symm

/-- Every signed weighted test over resolved ACTUAL list positions has
an exact retention/Buchstab/106-bank partition.  This is a one-generation
source equality, not a sum over all 430 generations or all original q. -/
theorem resolved_level_sum_all_actions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (F : Index N n root tau p g → ℝ) :
    (∑ l ∈ resolvedLevel N n root tau p g, F l) =
      (∑ l ∈ retainedLevel N n root tau p g, F l) +
      (∑ l ∈ buchstabLevel N n root tau p g, F l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l) := by
  have hRB :
      Disjoint (retainedLevel N n root tau p g)
        (buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g) := by
    apply Finset.disjoint_left.mpr
    intro l hl hr
    rcases Finset.mem_union.mp hr with hB | hK
    · exact (Finset.disjoint_left.mp
        (retained_buchstab_disjoint N n root tau p g)) hl hB
    · exact (Finset.disjoint_left.mp
        (retained_bank_disjoint N n root tau p g)) hl hK
  rw [resolved_level_partition,
    Finset.sum_union hRB,
    Finset.sum_union (buchstab_bank_disjoint N n root tau p g),
    bank_level_sum_eq_original_106]

/-- An actual exterior unresolved request has ZERO new-generation value.
This is the original scalar/cell request semantics, not count-source excision. -/
theorem unresolved_level_value_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∉ resolvedLevel N n root tau p g) :
    requestValue (iterate (g.val + 1)) (levelOccurrence l).current = 0 := by
  cases hr : resolve (g.val + 1) (levelOccurrence l).current with
  | none => exact resolve_none_value hr
  | some i =>
      have hmem : l ∈ resolvedLevel N n root tau p g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [actualChoice, hr]
      exact (hl hmem).elim

/-- The whole computed selected-request list (including exterior zeroes)
splits exactly into retention, Buchstab, and the original bank rows, with
literal positive path marks and WITHOUT conflating specified-cell/scalar
reads or replacing the actual generation by a supplied one. -/
theorem actual_level_request_value_all_actions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l : Index N n root tau p g,
      levelMark l * requestValue (iterate (g.val + 1))
        (levelOccurrence l).current) =
      (∑ l ∈ retainedLevel N n root tau p g,
        levelMark l * requestValue (iterate (g.val + 1))
          (levelOccurrence l).current) +
      (∑ l ∈ buchstabLevel N n root tau p g,
        levelMark l * requestValue (iterate (g.val + 1))
          (levelOccurrence l).current) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          levelMark l * requestValue (iterate (g.val + 1))
            (levelOccurrence l).current) := by
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l * requestValue (iterate (g.val + 1))
      (levelOccurrence l).current
  have hfull :
      (∑ l : Index N n root tau p g, F l) =
        ∑ l ∈ resolvedLevel N n root tau p g, F l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ∈ resolvedLevel N n root tau p g
    · simp [hl]
    · have hz := unresolved_level_value_zero N n root tau p g l hl
      simp [F, hl, hz]
  change (∑ l : Index N n root tau p g, F l) =
    (∑ l ∈ retainedLevel N n root tau p g, F l) +
    (∑ l ∈ buchstabLevel N n root tau p g, F l) +
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a, F l)
  rw [hfull]
  exact resolved_level_sum_all_actions N n root tau p g F

end
end ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition
