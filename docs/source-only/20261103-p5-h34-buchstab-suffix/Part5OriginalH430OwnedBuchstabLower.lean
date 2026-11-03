import ImbalancedChen.Part5OriginalH430SuffixIntegral
import ImbalancedChen.Part5OriginalH430CutoffCoherence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original rounded suffix -> right-endpoint integral -> EVERY query in the
owned closed cell -> the actual selected closed-minimum value. The middle
step is oriented monotonicity, not equality and not old-table monotonicity.
No future count licence, positive seed theorem, or final h34 is assumed.
-/
namespace ImbalancedChen.Part5OriginalH430OwnedBuchstabLower

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5UpperTables.Renewal P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430DecisionProvenance Part5OriginalH430ClosedOwner
open Part5OriginalH430CutoffCoherence Part5OriginalH430SuffixIntegral
open Part5OriginalH430ImmutableBankProfiles

/-- The endpoint conventions differ only in a SCALAR integral. No
arithmetic endpoint or physical pullback is erased by this identity. -/
theorem originalProfile_eq_tableTail (up : Bool) {s : ℝ} (hs : 2 ≤ s)
    (oldH oldh : Fin 200 → ℤ) :
    originalProfile up s oldH oldh =
      tableTail (if up then oldh else oldH) (if up then max 2 (s-1) else s-1) := by
  cases up with
  | false =>
      change (∫ w in Icc (s-1) 5, upperFloor oldH w/w) = tableTail oldH (s-1)
      have he := lowerTransition_literal oldH hs
      change tableTail oldH (s-1) = _ at he
      rw [integral_Ico_eq_integral_Ioc] at he
      rw [integral_Icc_eq_integral_Ioc]
      exact he.symm
  | true =>
      change (∫ w in Icc (max 2 (s-1)) 5, floorStep oldh w/w) =
        tableTail oldh (max 2 (s-1))
      have he := upperTransition_literal oldh s
      change tableTail oldh (max 2 (s-1)) = _ at he
      rw [integral_Ico_eq_integral_Ioc] at he
      rw [integral_Icc_eq_integral_Ioc]
      exact he.symm

theorem originalProfile_antitone (up : Bool) (oldH oldh : Fin 200 → ℤ)
    (hH : ∀ i, 0 ≤ oldH i) (hh : ∀ i, 0 ≤ oldh i)
    {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    originalProfile up t oldH oldh ≤ originalProfile up s oldH oldh := by
  rw [originalProfile_eq_tableTail up (hs.trans hst), originalProfile_eq_tableTail up hs]
  cases up with
  | false => exact tableTail_antitone hH (sub_le_sub_right hst 1)
  | true => exact tableTail_antitone hh (max_le_max le_rfl (sub_le_sub_right hst 1))

theorem eligible_cell_argument {i : Fin 200} (hi : 50 ≤ i.val) {s : ℝ}
    (hs : s ∈ queryCell i) : 2 ≤ s ∧ s ≤ floorGrid (i.val+1) := by
  rw [queryCell_eq_grid] at hs
  have hleft := grid_mono hi
  have htwo : (2:ℝ) ≤ floorGrid i.val := by
    simpa [floorGrid] using hleft
  exact ⟨htwo.trans hs.1, hs.2⟩

/-- This is the exact historical suffix index, not a rounded physical
query or an interval selected after inspecting the new prime. -/
theorem buchstabValue_le_right_profile (old : Table)
    (hn : ∀ up i, 0 ≤ old up i) (up : Bool) (i : Fin 200) (hi : 50 ≤ i.val) :
    ((buchstabValue old up i : ℤ) : ℝ)/(2:ℝ)^80 ≤
      originalProfile up (floorGrid (i.val+1)) (old true) (old false) := by
  have hs : (2:ℝ) ≤ floorGrid (i.val+1) := by
    have hx := grid_mono (show 50 ≤ i.val+1 by omega)
    simpa [floorGrid] using hx
  rw [originalProfile_eq_tableTail up hs]
  cases up with
  | false =>
      have hstart := P2TableActionSourceOnly.tableGrid_lower_start hi
      change floorGrid (i.val-49) = floorGrid (i.val+1)-1 at hstart
      have h := suffix_le_tableTail old true (k := i.val-49)
        (by have := i.isLt; omega) (hn true)
      rw [hstart] at h
      exact h
  | true =>
      have hstart := P2TableActionSourceOnly.tableGrid_upper_start hi
      change floorGrid (max 50 (i.val-49)) = max 2 (floorGrid (i.val+1)-1) at hstart
      have h := suffix_le_tableTail old false (k := max 50 (i.val-49))
        (by have := i.isLt; omega) (hn false)
      rw [hstart] at h
      exact h

/-- The whole CLOSED owner cell, including both endpoints and s=2.
Only nonnegativity of entries is used; the array need not be antitone. -/
theorem buchstabValue_le_cell_profile (old : Table)
    (hn : ∀ up i, 0 ≤ old up i) (up : Bool) (i : Fin 200) (hi : 50 ≤ i.val)
    {s : ℝ} (hs : s ∈ queryCell i) :
    ((buchstabValue old up i : ℤ) : ℝ)/(2:ℝ)^80 ≤
      originalProfile up s (old true) (old false) := by
  have hc := eligible_cell_argument hi hs
  exact (buchstabValue_le_right_profile old hn up i hi).trans
    (originalProfile_antitone up (old true) (old false) (hn true) (hn false) hc.1 hc.2)

/-- The owner is computed from g+1, its winning candidate reads g, and
the resulting selected value is paid by the original real profile at s. -/
theorem selected_atom_le_original {g : Fin 430} {up : Bool} {b : FloorAtom} {s : ℝ}
    (hb : s ∈ tableAtomSet (!up) b) (hc : selectedChoice g up b = .buchstab) :
    floorAtomValue (iterate (g.val+1) up) b ≤
      originalProfile up s (precedingH g) (precedingh g) := by
  have hi := selected_allowed g up b
  rw [hc] at hi
  change 50 ≤ (selectedOwner g up b).val at hi
  rw [closed_value_eq_selected, hc]
  exact buchstabValue_le_cell_profile (iterate g.val) (iterate_nonneg g.val) up
    (selectedOwner g up b) hi (selected_owner_contains hb)

theorem selected_lookup_le_original {g : Fin 430} {up : Bool} {b : FloorAtom} {s : ℝ}
    (hb : s ∈ tableAtomSet (!up) b) (hc : selectedChoice g up b = .buchstab) :
    tableFunction (!up) (iterate (g.val+1) up) s ≤
      originalProfile up s (precedingH g) (precedingh g) := by
  rw [tableFunction_at_atom _ hb]
  exact selected_atom_le_original hb hc

/-- The new correction remains nonnegative without evaluating iterate.
This follows from retention of the nonnegative seed, not action bases. -/
theorem iterate_lookup_nonneg (g : ℕ) (up : Bool) (s : ℝ) :
    0 ≤ tableFunction (!up) (iterate g up) s :=
  tableFunction_nonneg (iterate_nonneg g up) (!up) s

end
end ImbalancedChen.Part5OriginalH430OwnedBuchstabLower
