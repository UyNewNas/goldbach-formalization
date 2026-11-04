import ImbalancedChen.Part5OriginalH430FixedReadRows

/-!
Manuscript-local requested-cell semantics. SOURCE ONLY / UNCOMPILED.
A specified CELL and a scalar CLOSED lookup are distinct requests.
The scalar owner is computed at the generation being requested, while
its winner reads only the preceding generation. No count bound is a field.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedReads

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430ClosedOwner Part5OriginalH430DecisionProvenance
open Part5OriginalH430FixedReadDictionary Part5OriginalH430BankSlotTargets
open P2EnhancedLowerFinitePhysicalGraph

inductive ReadMode where
  | scalar
  | cell (index : Fin 200)
  deriving DecidableEq

/-- Data only: the integer word, physical state and kind of old read. -/
structure Request where
  node : TypedNode
  old : List ℕ
  mode : ReadMode

/-- Only a specified-cell request needs a containment condition. A scalar
request outside its supported interval is the literal zero lookup. -/
def ReadValid (r : Request) : Prop :=
  match r.mode with
  | .scalar => True
  | .cell i => r.node.physical.argument ∈ queryCell i

def requestValue (table : Table) (r : Request) : ℝ :=
  match r.mode with
  | .scalar => tableFunction (!r.node.upper) (table r.node.upper) r.node.physical.argument
  | .cell i => floorValue (table r.node.upper) i

/-- No arbitrary owner supplied by the caller. There is at most one
scalar atom; atomOwner retains the original updated-array adjacent minimum. -/
def resolve (generation : ℕ) (r : Request) : Option (Fin 200) :=
  match r.mode with
  | .cell i => some i
  | .scalar =>
      if h : ∃ b : FloorAtom, r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b then
        some (atomOwner (iterate generation r.node.upper) (Classical.choose h))
      else none

theorem resolve_value {generation : ℕ} {r : Request} {i : Fin 200}
    (hi : resolve generation r = some i) :
    requestValue (iterate generation) r = floorValue (iterate generation r.node.upper) i := by
  cases hm : r.mode with
  | cell j =>
      have hij : j = i := by simpa only [resolve, hm, Option.some.injEq] using hi
      simpa only [requestValue, hm, hij]
  | scalar =>
      simp only [resolve, hm] at hi
      split_ifs at hi with hex
      · have hown : atomOwner (iterate generation r.node.upper) (Classical.choose hex) = i :=
          Option.some.inj hi
        simp only [requestValue, hm]
        change tableFunction (!r.node.upper) (iterate generation r.node.upper)
          r.node.physical.argument = _
        rw [tableFunction_at_atom _ (Classical.choose_spec hex), atomOwner_value, hown]
      · cases hi

theorem resolve_contains {generation : ℕ} {r : Request} {i : Fin 200}
    (hr : ReadValid r) (hi : resolve generation r = some i) :
    r.node.physical.argument ∈ queryCell i := by
  cases hm : r.mode with
  | cell j =>
      have hij : j = i := by simpa only [resolve, hm, Option.some.injEq] using hi
      simpa only [ReadValid, hm, hij] using hr
  | scalar =>
      simp only [resolve, hm] at hi
      split_ifs at hi with hex
      · have hown := Option.some.inj hi
        rw [← hown]
        exact atomOwner_contains _ (Classical.choose_spec hex)
      · cases hi

/-- Stopping an exterior scalar request loses exactly zero; it is not
an unproved source-support excision or a statement about count mass. -/
theorem resolve_none_value {generation : ℕ} {r : Request}
    (hi : resolve generation r = none) : requestValue (iterate generation) r = 0 := by
  cases hm : r.mode with
  | cell j => simp [resolve, hm] at hi
  | scalar =>
      simp only [resolve, hm] at hi
      split_ifs at hi with hex
      · cases hi
      · simp only [requestValue, hm, tableFunction]
        apply Finset.sum_eq_zero
        intro b _
        exact indicator_of_notMem (fun hb => hex ⟨b, hb⟩) _

/-- g is the PREDECESSOR index. Owner selection uses g+1. -/
def Selected (g : ℕ) (r : Request) (i : Fin 200) (c : Choice) : Prop :=
  resolve (g+1) r = some i ∧ (roundDecision (iterate g) r.node.upper i).choice = c

theorem selected_allowed {g : ℕ} {r : Request} {i : Fin 200} {c : Choice}
    (hc : Selected g r i c) : choiceAllowed r.node.upper i c := by
  have h := roundDecision_allowed (iterate g) r.node.upper i
  rwa [hc.2] at h

theorem selected_value {g : ℕ} {r : Request} {i : Fin 200} {c : Choice}
    (hc : Selected g r i c) :
    requestValue (iterate (g+1)) r =
      (choiceValue (iterate g) r.node.upper i c : ℝ)/(2^80 : ℝ) := by
  rw [resolve_value hc.1]
  change ((roundDecision (iterate g) r.node.upper i).numerator : ℝ)/(2^80 : ℝ) = _
  rw [roundDecision_value, hc.2]

theorem selected_bank_target {g : ℕ} {r : Request} {i : Fin 200} {k : Fin 106}
    (hr : ReadValid r) (hc : Selected g r i (.bank k)) :
    r.node.upper = true ∧ r.node.physical.argument ≤ actionTarget (actionOfSlot k) := by
  have ha := selected_allowed hc
  have hcell := resolve_contains hr hc.1
  rw [queryCell_eq_grid] at hcell
  exact ⟨ha.1, hcell.2.trans (targetCell_right_le ha.2)⟩

theorem selected_buchstab_guard {g : ℕ} {r : Request} {i : Fin 200}
    (hr : ReadValid r) (hc : Selected g r i .buchstab) : 2 ≤ r.node.physical.argument := by
  have ha : 50 ≤ i.val := selected_allowed hc
  have hcell := resolve_contains hr hc.1
  have haR : (50 : ℝ) ≤ i.val := by exact_mod_cast ha
  change 1+(i.val : ℝ)/50 ≤ r.node.physical.argument ∧ _ at hcell
  linarith [hcell.1]

/-- Exact literal bank comparison on EITHER request mode. The preceding
closed-cell invariant and all numerical feedback/base licences remain open. -/
theorem selected_bank_candidate_upper {g : ℕ} {r : Request} {i : Fin 200} {k : Fin 106}
    (hc : Selected g r i (.bank k)) :
    requestValue (iterate (g+1)) r ≤ baseValue (actionOfSlot k) +
      fixedValue (iterate g true) (actionOfSlot k) +
      feedbackValue (iterate g) (actionOfSlot k) := by
  rw [selected_value hc]
  have h := candidate_fixedRead_upper (iterate g) (actionOfSlot k)
  simpa only [slot_action, choiceValue] using h

/-- Scalar resolution agrees with the previously exported closed owner.
This does not identify the specified-cell mode with scalar lookup. -/
theorem scalar_resolve_owner {g : Fin 430} {r : Request} {b : FloorAtom}
    (hm : r.mode = .scalar)
    (hb : r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b) :
    resolve (g.val+1) r = some (Part5OriginalH430ClosedOwner.selectedOwner g r.node.upper b) := by
  have hex : ∃ c : FloorAtom, r.node.physical.argument ∈ tableAtomSet (!r.node.upper) c := ⟨b,hb⟩
  have heq := tableAtom_unique (Classical.choose_spec hex) hb
  simp only [resolve, hm, dif_pos hex, heq, Part5OriginalH430ClosedOwner.selectedOwner]

end
end ImbalancedChen.Part5OriginalH430RequestedReads
