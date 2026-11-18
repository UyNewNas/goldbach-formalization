import ImbalancedChen.Part5OriginalH430LiveAnchorMassConservation
import ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition

/-!
P5.6 / h34: bind the already conserved literal fixed-read mass to
the actual generation-g+1 winner at each physical request LIST position.

This is the genuine scalar/specified-cell resolver (not an invented owner).
Only a winning original 106-bank action has a fixed channel; retention,
Buchstab and unresolved exterior requests contribute zero fixed read.
The same occurrenceScale and Q80 predecessor are used on both sides.

In particular this proves an exact SOURCE identification between the
previous selectedLiteralFixedMass and a single all-action positional ledger.
It does NOT identify these request occurrences with the arithmetic U3/U4
selected counts, provide a root 7/2 count normalization, discharge
CLOSED-CELL, or pay the remaining positive defect.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualWinnerFixedRead

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430ExactOuterQ80FloorCredit
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430LiveAnchorMassConservation

/-- The literal fixed Q80 channel of the ACTUAL selected action.
Retention and Buchstab are intentionally zero in this FIXED channel;
their other physical and feedback channels are accounted elsewhere. -/
def actualWinnerFixedRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  match actualChoice N n root tau p g l with
  | some (.bank k) => fixedValue (precedingH g) (actionOfSlot k)
  | _ => 0

/-- The winning row's fixed term is exactly its original 106-bank
fixedValue, not the scalar-owner value of a possibly different cell. -/
theorem actual_winner_fixed_read_of_selected
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    actualWinnerFixedRead N n root tau p g l =
      fixedValue (precedingH g) a := by
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hl).2
  have hc : actualChoice N n root tau p g l =
      some (.bank (slotOfAction a)) :=
    (actual_choice_iff_selected N n root tau p g l
      (.bank (slotOfAction a))).2 ⟨i, hi⟩
  simp [actualWinnerFixedRead, hc, action_slot]

/-- A genuine retained request does not acquire a bank fixed debit. -/
theorem actual_winner_fixed_read_of_retained
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∈ retainedLevel N n root tau p g) :
    actualWinnerFixedRead N n root tau p g l = 0 := by
  have hc : actualChoice N n root tau p g l = some .retained :=
    (Finset.mem_filter.mp hl).2
  simp [actualWinnerFixedRead, hc]

/-- Nor does a genuinely selected Buchstab request use the bank fixed
read; the Buchstab physical positive source remains a separate term. -/
theorem actual_winner_fixed_read_of_buchstab
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∈ buchstabLevel N n root tau p g) :
    actualWinnerFixedRead N n root tau p g l = 0 := by
  have hc : actualChoice N n root tau p g l = some .buchstab :=
    (Finset.mem_filter.mp hl).2
  simp [actualWinnerFixedRead, hc]

/-- Exterior unresolved requests do not contribute an unselected
fixed channel. This is about literal resolution, not U3/U4 filtering. -/
theorem actual_winner_fixed_read_of_unresolved
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∉ resolvedLevel N n root tau p g) :
    actualWinnerFixedRead N n root tau p g l = 0 := by
  cases hc : actualChoice N n root tau p g l with
  | none =>
      simp [actualWinnerFixedRead, hc]
  | some c =>
      have hm : l ∈ resolvedLevel N n root tau p g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [hc]
      exact (hl hm).elim

/-- Selected fixed mass is the fixed channel at each ACTUAL bank winner
position, with original positive marks and occurrence Theta. This is an
owner-free equality: the original resolver itself identifies the owner. -/
theorem selected_literal_fixed_mass_eq_bank_winner_positions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    selectedLiteralFixedMass N n root tau p g =
      ∑ l ∈ bankLevel N n root tau p g,
        occurrenceScale N n root tau p g l *
          actualWinnerFixedRead N n root tau p g l := by
  calc
    selectedLiteralFixedMass N n root tau p g =
        ∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a,
            occurrenceScale N n root tau p g l *
              actualWinnerFixedRead N n root tau p g l := by
      unfold selectedLiteralFixedMass
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro l hl
      rw [actual_winner_fixed_read_of_selected
        N n root tau p g a l hl]
    _ = ∑ l ∈ bankLevel N n root tau p g,
          occurrenceScale N n root tau p g l *
            actualWinnerFixedRead N n root tau p g l :=
      (bank_level_sum_eq_original_106 N n root tau p g
        (fun l => occurrenceScale N n root tau p g l *
          actualWinnerFixedRead N n root tau p g l)).symm

/-- Physical all-action fixed ledger. The zero slots are real
retention/Buchstab winners, not deleted arithmetic U3/U4 sources. -/
def resolvedWinnerFixedMass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ resolvedLevel N n root tau p g,
    occurrenceScale N n root tau p g l *
      actualWinnerFixedRead N n root tau p g l

/-- Exact source match to the one-generation full-action partition.
No CLOSED-CELL or nonnegative mass hypothesis is needed. -/
theorem resolved_winner_fixed_mass_eq_literal_selected
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    resolvedWinnerFixedMass N n root tau p g =
      selectedLiteralFixedMass N n root tau p g := by
  let f : Index N n root tau p g → ℝ := fun l =>
    occurrenceScale N n root tau p g l *
      actualWinnerFixedRead N n root tau p g l
  have hret :
      (∑ l ∈ retainedLevel N n root tau p g, f l) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    simp [f, actual_winner_fixed_read_of_retained
      N n root tau p g l hl]
  have hbuch :
      (∑ l ∈ buchstabLevel N n root tau p g, f l) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    simp [f, actual_winner_fixed_read_of_buchstab
      N n root tau p g l hl]
  change (∑ l ∈ resolvedLevel N n root tau p g, f l) =
    selectedLiteralFixedMass N n root tau p g
  calc
    (∑ l ∈ resolvedLevel N n root tau p g, f l) =
        (∑ l ∈ retainedLevel N n root tau p g, f l) +
        (∑ l ∈ buchstabLevel N n root tau p g, f l) +
        (∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a, f l) :=
      resolved_level_sum_all_actions N n root tau p g f
    _ = ∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a, f l := by
      rw [hret, hbuch]
      ring
    _ = ∑ l ∈ bankLevel N n root tau p g, f l :=
      (bank_level_sum_eq_original_106 N n root tau p g f).symm
    _ = selectedLiteralFixedMass N n root tau p g :=
      (selected_literal_fixed_mass_eq_bank_winner_positions
        N n root tau p g).symm

/-- All 430 predecessor slots use the same exact winning fixed channel.
No new generation, scalar-owner substitution, or deduplication occurs. -/
theorem all_generations_resolved_winner_fixed_mass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    (∑ g : Fin 430, resolvedWinnerFixedMass N n root tau p g) =
      (∑ g : Fin 430, selectedLiteralFixedMass N n root tau p g) := by
  apply Finset.sum_congr rfl
  intro g _
  exact resolved_winner_fixed_mass_eq_literal_selected N n root tau p g

/-- Conservation now names the actual physical resolved-list fixed
channel. The CLOSED-CELL predecessor premise is still explicit. -/
theorem all_generations_physical_winner_fixed_conservation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (F : ℝ → ℝ)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    (∑ g : Fin 430,
      bankSelectedPositiveAnchorPayment N n root tau p g F) +
    (∑ g : Fin 430,
      resolvedWinnerFixedMass N n root tau p g) =
    (∑ g : Fin 430,
      selectedLiteralReferenceMass N n root tau p g F) := by
  rw [all_generations_resolved_winner_fixed_mass]
  exact all_generations_literal_fixed_mass_conservation
    N n root tau p F hclosed

/-- Root consumer with the ORIGINAL resolved finite-list winner fixed
read on the left; both Q80 integer-rounding credits remain unchanged.
This is NOT an arithmetic U3/U4 count-owner equality or h34 closure. -/
theorem frozen_root_le_actual_winner_fixed_mass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430,
        bankCompleteFloorCredit N n root tau p g) +
      (∑ g : Fin 430,
        resolvedWinnerFixedMass N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            selectedLiteralReferenceMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) := by
  rw [all_generations_resolved_winner_fixed_mass]
  exact frozen_root_le_reference_with_literal_fixed_mass
    N n root tau p F hN ht ht' hn hp hband hclosed

end
end ImbalancedChen.Part5OriginalH430ActualWinnerFixedRead
