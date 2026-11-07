import ImbalancedChen.Part5OriginalH430SelectedReadGraph
import ImbalancedChen.P5OriginalFeedbackTableKernels
import ImbalancedChen.P5ZU11ActualH248Ordinary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Resolve the original CLOSED minimum into one actual cell and then read
that cell's actual selected action. The owner uses the UPDATED table;
the selected action uses the PRECEDING table. These orders cannot be
interchanged. Exterior-zero atoms are never turned into action licences.
-/
namespace ImbalancedChen.Part5OriginalH430ClosedOwner

noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430DecisionProvenance Part5OriginalH430SelectedReadGraph

/-- Deterministic left owner on equal adjacent numerators. -/
def knotOwner (nums : Fin 200 → ℤ) (j : Fin 201) : Fin 200 :=
  if h0 : j.val = 0 then 0
  else if hlast : j.val = 200 then 199
  else if nums ⟨j.val-1, by omega⟩ ≤ nums ⟨j.val, by omega⟩ then
    ⟨j.val-1, by omega⟩ else ⟨j.val, by omega⟩

def atomOwner (nums : Fin 200 → ℤ) : FloorAtom → Fin 200
  | .inl i => i
  | .inr j => knotOwner nums j

private theorem floorValue_mono {nums : Fin 200 → ℤ} {i j : Fin 200}
    (h : nums i ≤ nums j) : floorValue nums i ≤ floorValue nums j := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem knotOwner_value (nums : Fin 200 → ℤ) (j : Fin 201) :
    floorKnotValue nums j = floorValue nums (knotOwner nums j) := by
  by_cases h0 : j.val = 0
  · simp [floorKnotValue, knotOwner, h0]
  · by_cases hlast : j.val = 200
    · simp [floorKnotValue, knotOwner, h0, hlast]
    · let l : Fin 200 := ⟨j.val-1, by omega⟩
      let r : Fin 200 := ⟨j.val, by omega⟩
      by_cases hle : nums l ≤ nums r
      · have hv := floorValue_mono hle
        simpa [floorKnotValue, knotOwner, h0, hlast, l, r, hle] using min_eq_left hv
      · have hv := floorValue_mono (le_of_not_ge hle)
        simpa [floorKnotValue, knotOwner, h0, hlast, l, r, hle] using min_eq_right hv

theorem atomOwner_value (nums : Fin 200 → ℤ) (b : FloorAtom) :
    floorAtomValue nums b = floorValue nums (atomOwner nums b) := by
  cases b with
  | inl i => rfl
  | inr j => exact knotOwner_value nums j

theorem tableAtom_subset_upper (lower : Bool) (b : FloorAtom) :
    tableAtomSet lower b ⊆ upperAtomSet b := by
  cases lower with
  | false => exact Subset.rfl
  | true =>
      cases b <;> intro s hs
      all_goals exact ⟨⟨(by linarith [hs.1.1]), hs.1.2⟩, hs.2⟩

theorem tableAtom_unique {lower : Bool} {s : ℝ} {b c : FloorAtom}
    (hb : s ∈ tableAtomSet lower b) (hc : s ∈ tableAtomSet lower c) : b = c :=
  P5Z.U11H248.upperAtom_unique (tableAtom_subset_upper lower b hb)
    (tableAtom_subset_upper lower c hc)

private theorem grid_mono {i j : ℕ} (h : i ≤ j) : floorGrid i ≤ floorGrid j := by
  have hR : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast h
  dsimp [floorGrid]
  linarith

theorem queryCell_eq_grid (i : Fin 200) :
    queryCell i = Icc (floorGrid i.val) (floorGrid (i.val+1)) := by
  simp only [queryCell, floorGrid, Nat.cast_add, Nat.cast_one]

/-- The closed owner is a cell that ACTUALLY contains the query, including
both global endpoints and all internal knots. No null-set deletion. -/
theorem atomOwner_contains {lower : Bool} {s : ℝ} {b : FloorAtom}
    (nums : Fin 200 → ℤ) (hb : s ∈ tableAtomSet lower b) :
    s ∈ queryCell (atomOwner nums b) := by
  have hu := tableAtom_subset_upper lower b hb
  rw [queryCell_eq_grid]
  cases b with
  | inl i => exact ⟨hu.2.1.le, hu.2.2.le⟩
  | inr j =>
      have hs : s = floorGrid j.val := hu.2
      rw [hs]
      by_cases h0 : j.val = 0
      · simp [atomOwner, knotOwner, h0, floorGrid]
      · by_cases hlast : j.val = 200
        · norm_num [atomOwner, knotOwner, h0, hlast, floorGrid]
        · have hj : j.val-1+1 = j.val := by omega
          simp only [atomOwner, knotOwner, dif_neg h0, dif_neg hlast]
          split_ifs
          · exact ⟨grid_mono (by omega), by rw [hj]⟩
          · exact ⟨le_rfl, grid_mono (Nat.le_succ _)⟩

theorem tableFunction_at_atom {lower : Bool} {s : ℝ} {b : FloorAtom}
    (nums : Fin 200 → ℤ) (hb : s ∈ tableAtomSet lower b) :
    tableFunction lower nums s = floorAtomValue nums b := by
  unfold tableFunction
  calc
    _ = (tableAtomSet lower b).indicator (fun _ => floorAtomValue nums b) s := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        exact indicator_of_notMem (fun hc => hcb (tableAtom_unique hc hb)) _
      · intro h
        exact (h (Finset.mem_univ b)).elim
    _ = _ := indicator_of_mem hb _

/-- The winner of the adjacent MINIMUM is computed at generation g+1,
not at g. Its retained maximum still reads only generation g. -/
def selectedOwner (g : Fin 430) (up : Bool) (b : FloorAtom) : Fin 200 :=
  atomOwner (iterate (g.val+1) up) b

def selectedDecision (g : Fin 430) (up : Bool) (b : FloorAtom) : Decision :=
  roundDecision (iterate g.val) up (selectedOwner g up b)

def selectedChoice (g : Fin 430) (up : Bool) (b : FloorAtom) : Choice :=
  (selectedDecision g up b).choice

theorem selected_allowed (g : Fin 430) (up : Bool) (b : FloorAtom) :
    choiceAllowed up (selectedOwner g up b) (selectedChoice g up b) :=
  roundDecision_allowed _ _ _

/-- Exact closed lookup = decoded winning candidate. Original product
floors, original base and outer divisor remain INSIDE choiceValue. -/
theorem closed_value_eq_selected (g : Fin 430) (up : Bool) (b : FloorAtom) :
    floorAtomValue (iterate (g.val+1) up) b =
      ((choiceValue (iterate g.val) up (selectedOwner g up b)
        (selectedChoice g up b) : ℤ) : ℝ)/(2^80:ℝ) := by
  rw [atomOwner_value]
  change ((selectedDecision g up b).numerator : ℝ)/(2^80:ℝ) = _
  exact congrArg (fun z : ℤ => (z:ℝ)/(2^80:ℝ))
    (roundDecision_value (iterate g.val) up (selectedOwner g up b))

theorem closed_value_eq_readGraph (g : Fin 430) (up : Bool) (b : FloorAtom) :
    floorAtomValue (iterate (g.val+1) up) b =
      ((eval (read (iterate g.val))
        (chosenExpr (iterate g.val) up (selectedOwner g up b)) : ℤ) : ℝ)/(2^80:ℝ) := by
  rw [eval_chosenExpr, atomOwner_value]

/-- Polarity: upper=true reads the H lookup, hence lower=false. -/
theorem selected_owner_contains {g : Fin 430} {up : Bool} {b : FloorAtom} {s : ℝ}
    (hb : s ∈ tableAtomSet (!up) b) : s ∈ queryCell (selectedOwner g up b) :=
  atomOwner_contains _ hb

theorem selected_buchstab_guard {g : Fin 430} {up : Bool} {b : FloorAtom} {s : ℝ}
    (hb : s ∈ tableAtomSet (!up) b) (hc : selectedChoice g up b = .buchstab) :
    2 ≤ s := by
  have hi := selected_allowed g up b
  rw [hc] at hi
  change 50 ≤ (selectedOwner g up b).val at hi
  have hiR : (50:ℝ) ≤ (selectedOwner g up b).val := by exact_mod_cast hi
  have hcell := selected_owner_contains hb
  change 1+((selectedOwner g up b).val:ℝ)/50 ≤ s ∧ _ at hcell
  linarith [hcell.1]

/-- Pointwise all-query formula, including exterior zero and every knot.
It selects one enabled maximum at the owned cell; it does not add banks. -/
theorem lookup_eq_selected_atom_sum (g : Fin 430) (up : Bool) (s : ℝ) :
    tableFunction (!up) (iterate (g.val+1) up) s =
      ∑ b : FloorAtom, (tableAtomSet (!up) b).indicator
        (fun _ => ((choiceValue (iterate g.val) up (selectedOwner g up b)
          (selectedChoice g up b) : ℤ) : ℝ)/(2^80:ℝ)) s := by
  unfold tableFunction
  apply Finset.sum_congr rfl
  intro b _
  rw [closed_value_eq_selected]

end
end ImbalancedChen.Part5OriginalH430ClosedOwner
