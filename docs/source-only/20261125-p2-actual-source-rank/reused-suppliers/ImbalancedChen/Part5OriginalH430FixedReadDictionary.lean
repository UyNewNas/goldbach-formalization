import ImbalancedChen.Part5OriginalH430BankSlotTargets
import ImbalancedChen.Part5OriginalH430ArithmeticParentMass
import ImbalancedChen.P2HistoricLogPointInterpreter

/-!
SOURCE ONLY / UNCOMPILED.

The literal bank reads an old CELL at each fixed argument. This is not
in general the adjacent-min scalar lookup at that argument. Keep the
original cells, coefficients, order, and outer divisor. Finite data checks
below are unevaluated Lean proof bodies, not input hypotheses. No old-cell
count bound, bank base, or analytic input is manufactured here.
-/
namespace ImbalancedChen.Part5OriginalH430FixedReadDictionary

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430LiteralActionData (rows)
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5OriginalH430BankSlotTargets Part5OriginalH430ClosedOwner
open Part5OriginalH430ArithmeticParentMass

/-- Original W1 fixed read: the cell ending at the anchor. -/
def w1Cell (j : Fin 10) : Fin 200 :=
  ⟨109 + 10*j.val, by have := j.isLt; omega⟩

/-- Read the ORIGINAL W2 point list, without a second point-index table. -/
def w2RawCell (j : Fin 36) (anchor : Bool) : ℕ :=
  ((rows (slotOfAction (.inr j))).points.getD (if anchor then 0 else 1) (0,0)).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem w2RawCell_lt (j : Fin 36) (anchor : Bool) : w2RawCell j anchor < 200 := by
  fin_cases j <;> cases anchor <;> decide

def w2Cell (j : Fin 36) (anchor : Bool) : Fin 200 :=
  ⟨w2RawCell j anchor, w2RawCell_lt j anchor⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem literal_W1_points (i : Fin 7) (j : Fin 10) :
    (rows (slotOfAction (.inl (i,j)))).points = [((w1Cell j).val,1)] ∧
    (rows (slotOfAction (.inl (i,j)))).divisor = 1 := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- List equality checks length, order, multiplicities, and excludes
getD's default as an unnoticed extra or missing occurrence. -/
theorem literal_W2_points (j : Fin 36) :
    (rows (slotOfAction (.inr j))).points =
      [((w2Cell j true).val,4), ((w2Cell j false).val,1)] ∧
    (rows (slotOfAction (.inr j))).divisor = 5 := by
  fin_cases j <;> decide

theorem w1Cell_contains (j : Fin 10) : W1Anchor j ∈ queryCell (w1Cell j) := by
  fin_cases j <;> norm_num [queryCell, w1Cell, W1Anchor]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Connect each point read to its existing real parameter record.
These are closed cells, NOT membership in an open FloorAtom. -/
theorem w2Cell_contains (j : Fin 36) (anchor : Bool) :
    (if anchor then (originalW2At j).s0 else (originalW2At j).phi1) ∈
      queryCell (w2Cell j anchor) := by
  fin_cases j <;> cases anchor <;>
    norm_num [queryCell, w2Cell, w2RawCell, slotOfAction, rows,
      originalW2At, originalRepairedW2Bank]

def fixedValue (nums : Fin 200 → ℤ) : Original106Action → ℝ
  | .inl (_,j) => floorValue nums (w1Cell j)
  | .inr j => (4*floorValue nums (w2Cell j true) + floorValue nums (w2Cell j false))/5

/-- Real decoding of the raw point numerator. The outer INTEGER division
of the full candidate is deliberately not distributed over this term. -/
def rawFixedValue (old : Table) (a : Original106Action) : ℝ :=
  ((((rows (slotOfAction a)).points.map (fun p => read old true p.1 * p.2)).sum : ℤ) : ℝ) /
    ((rows (slotOfAction a)).divisor : ℝ) / (2^80 : ℝ)

theorem rawFixedValue_eq (old : Table) (a : Original106Action) :
    rawFixedValue old a = fixedValue (old true) a := by
  rcases a with ⟨i,j⟩ | j
  · simp only [rawFixedValue, (literal_W1_points i j).1, (literal_W1_points i j).2,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      read, dif_pos (w1Cell j).isLt, mul_one, add_zero,
      Nat.cast_one, div_one, fixedValue, floorValue]
  · simp only [rawFixedValue, (literal_W2_points j).1, (literal_W2_points j).2,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      read, dif_pos (w2Cell j true).isLt, dif_pos (w2Cell j false).isLt,
      mul_one, add_zero, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Nat.cast_ofNat, fixedValue, floorValue]
    ring


/-- Only the literal per-product integer feedback quotients occur here.
They are kept UNEVALUATED; this is not their integral comparison. -/
def feedbackNumerator (old : Table) (a : Original106Action) : ℤ :=
  ((rows (slotOfAction a)).lowerWeights.map
    (fun p => read old false p.1 * p.2 / P2Selected430LiteralActionData.q)).sum +
  ((rows (slotOfAction a)).upperWeights.map
    (fun p => read old true p.1 * p.2 / P2Selected430LiteralActionData.q)).sum

def baseValue (a : Original106Action) : ℝ :=
  ((rows (slotOfAction a)).base : ℝ)/(2^80 : ℝ)

def feedbackValue (old : Table) (a : Original106Action) : ℝ :=
  (feedbackNumerator old a : ℝ)/((rows (slotOfAction a)).divisor : ℝ)/(2^80 : ℝ)

theorem literal_divisor_pos (a : Original106Action) :
    0 < (rows (slotOfAction a)).divisor := by
  rcases a with ⟨i,j⟩ | j
  · rw [(literal_W1_points i j).2]
    decide
  · rw [(literal_W2_points j).2]
    decide

/-- Pay the outer INTEGER quotient in its correct direction; do not
pretend it distributes as an equality over points, feedback, or base.
This bound holds even for signed arrays and signed bases. -/
theorem candidate_fixedRead_upper (old : Table) (a : Original106Action) :
    ((candidate old (rows (slotOfAction a)) : ℤ) : ℝ)/(2^80 : ℝ) ≤
      baseValue a + fixedValue (old true) a + feedbackValue old a := by
  let P : ℤ := ((rows (slotOfAction a)).points.map (fun p => read old true p.1*p.2)).sum
  let F : ℤ := feedbackNumerator old a
  let d : ℕ := (rows (slotOfAction a)).divisor
  have hd : (0 : ℤ) < (d : ℤ) := by exact_mod_cast literal_divisor_pos a
  have hround := Certificates.P2HistoricLogPointInterpreter.ediv_le_real (P+F) (d : ℤ) hd
  have heval : candidate old (rows (slotOfAction a)) =
      (rows (slotOfAction a)).base + (P+F)/(d : ℤ) := by
    dsimp [candidate,P,F,d,feedbackNumerator]
    congr 1
    congr 1
    ring
  rw [heval,Int.cast_add,add_div]
  calc
    _ ≤ ((rows (slotOfAction a)).base : ℝ)/(2^80 : ℝ) +
        (((P+F : ℤ) : ℝ)/(d : ℝ))/(2^80 : ℝ) := by
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (by simpa only [Int.cast_natCast] using hround)
        (by positivity)
    _ = _ := by
      rw [← rawFixedValue_eq old a]
      simp only [Int.cast_add,add_div]
      dsimp [baseValue,rawFixedValue,feedbackValue,P,F,d]
      ring

/-- This is an INDUCTION STEP from the preceding generation's closed-cell
bound. It does not assert that the source count satisfies that invariant. -/
theorem fixedValue_le_of_cells (nums : Fin 200 → ℤ) (F : ℝ → ℝ)
    (hcells : ∀ i s, s ∈ queryCell i → floorValue nums i ≤ F s)
    (a : Original106Action) :
    fixedValue nums a ≤ match a with
      | .inl (_,j) => F (W1Anchor j)
      | .inr j => (4*F (originalW2At j).s0 + F (originalW2At j).phi1)/5 := by
  rcases a with ⟨i,j⟩ | j
  · exact hcells _ _ (w1Cell_contains j)
  · have h0 := hcells _ _ (w2Cell_contains j true)
    have h1 := hcells _ _ (w2Cell_contains j false)
    change (4*floorValue nums (w2Cell j true) + floorValue nums (w2Cell j false))/5 ≤ _
    exact div_le_div_of_nonneg_right (add_le_add
      (mul_le_mul_of_nonneg_left h0 (by norm_num)) h1) (by norm_num)

/-- Every point in a closed cell has its usual unique scalar atom, but
the cell used by the producer need not be that scalar atom's owner. -/
theorem scalar_atom_exists {s : ℝ} {i : Fin 200} (hs : s ∈ queryCell i) :
    ∃ b : FloorAtom, s ∈ tableAtomSet false b := by
  rw [queryCell_eq_grid] at hs
  have h1 : 1 ≤ s := (Part5UpperTables.Renewal.grid_bounds
    (show i.val ≤ 200 by omega)).1.trans hs.1
  have h5 : s ≤ 5 := hs.2.trans (Part5UpperTables.Renewal.grid_bounds
    (show i.val+1 ≤ 200 by omega)).2
  by_cases hl : s = floorGrid i.val
  · exact ⟨.inr i.castSucc, ⟨⟨h1,h5⟩,hl⟩⟩
  · by_cases hr : s = floorGrid (i.val+1)
    · exact ⟨.inr i.succ, ⟨⟨h1,h5⟩,hr⟩⟩
    · exact ⟨.inl i, ⟨⟨h1,h5⟩,
        lt_of_le_of_ne hs.1 (Ne.symm hl), lt_of_le_of_ne hs.2 hr⟩⟩

theorem one_lookup_of_cell {s : ℝ} {i : Fin 200} (hs : s ∈ queryCell i) :
    tableFunction false oneNumerators s = 1 := by
  obtain ⟨b,hb⟩ := scalar_atom_exists hs
  rw [tableFunction_at_atom oneNumerators hb, one_floorAtomValue]

/-- A nonnegative arbitrary-array witness, NOT a counterexample to the
actual430 arrays or to the manuscript. It blocks an invalid generic rewrite. -/
def seamWitness (i : Fin 200) : ℤ := if i = 109 then 2^80 else 0

theorem specified_cell_is_not_scalar_lookup :
    fixedValue seamWitness (.inl (0,0)) = 1 ∧
    tableFunction false seamWitness (W1Anchor 0) = 0 := by
  have hb : W1Anchor 0 ∈ tableAtomSet false (.inr (110 : Fin 201)) := by
    norm_num [tableAtomSet, upperAtomSet, floorGrid, W1Anchor]
  constructor
  · norm_num [fixedValue, w1Cell, floorValue, seamWitness]
  · rw [tableFunction_at_atom seamWitness hb]
    norm_num [floorAtomValue, floorKnotValue, floorValue, seamWitness]

end
end ImbalancedChen.Part5OriginalH430FixedReadDictionary
