import ImbalancedChen.P4AOriginalCell2CommonRefinedParent
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact remaining original ascending source IDs are 3,4,5,6,8,...,14.
Each is a fixed navigation cell, not an arbitrary CellGuard input. All rows
use the original 96-row order. The eight actual A-to-C patch vectors and
the eleven exact per-cell patch sets below transcribe immutable navigation.
-/
namespace ImbalancedChen.P4AOriginalRemainingAscendingAtlas
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
abbrev RemainingCell := Fin 11
abbrev Point8 := Fin 8 → ℝ
abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine
abbrev baseRows := P4AOriginalAscendingCell0Literal96.rows

def sourceId : RemainingCell → Fin 15 := ![3,4,5,6,8,9,10,11,12,13,14]

def changedRows : RemainingCell → Finset (Fin 96) :=
  ![
    {58,90},
    {58,90,92},
    {58,60,90,92},
    {58,74,90},
    {58,74,82,90},
    {58,74,82,90,92},
    {58,60,74,90,92},
    {58,60,74,82,90,92},
    {58,60,74,76,90,92},
    {58,60,74,76,82,90,92},
    {58,60,74,76,82,84,90,92}
  ]

def rightPatch (k : Fin 96) : String × (Fin 9 → ℚ) :=
  match k.val with
  | 58 => ("old subset 26 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,3/2,0,0,0])
  | 60 => ("old subset 28 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,3/2,0,0,0])
  | 74 => ("old subset 42 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,0,3/2,0,0])
  | 76 => ("old subset 44 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,0,3/2,0,0])
  | 82 => ("old subset 50 chosen plane 1 below R6", ![0,0,0,-3/2,0,3/2,3/2,0,0])
  | 84 => ("old subset 52 chosen plane 1 below R6", ![0,0,-3/2,0,0,3/2,3/2,0,0])
  | 90 => ("old subset 58 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,3/2,3/2,0,0])
  | 92 => ("old subset 60 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,3/2,3/2,0,0])
  | _ => baseRows k

def rows (c : RemainingCell) (k : Fin 96) :=
  if k ∈ changedRows c then rightPatch k else baseRows k

def sourceRows (c : RemainingCell) (t : Point8) : Prop :=
  ∀ k : Fin 96, 0 < evalRow (rows c k).2 t

def seedSeparator : RemainingCell → Fin 96 := ![74,74,60,92,82,82,60,60,60,60,60]


theorem sourceId_injective : Function.Injective sourceId := by decide

theorem sourceId_selected (c : RemainingCell) : sourceId c ∈ selectedCellIndices := by
  fin_cases c <;> decide

private def commonRows (t : Point8) : Prop :=
  ∀ k : Fin 34, 0 < evalRow (baseRows ⟨k.val, by omega⟩).2 t

private theorem common_row_exact : ∀ (c : RemainingCell) (k : Fin 34),
    rows c ⟨k.val, by omega⟩ = baseRows ⟨k.val, by omega⟩ := by
  intro c k
  have hn : (⟨k.val, by omega⟩ : Fin 96) ∉ changedRows c := by
    fin_cases c <;> norm_num [changedRows, Fin.ext_iff] <;> omega
  simp only [rows, if_neg hn]

private theorem sourceRows_common (c : RemainingCell) (t : Point8)
    (h : sourceRows c t) : commonRows t := by
  intro k
  simpa only [common_row_exact] using h ⟨k.val, by omega⟩

private theorem singleton_row_exact (c : RemainingCell) : rows c 34 = baseRows 34 := by
  fin_cases c <;> rfl

private theorem fin8_coord2 : (⟨2, by decide⟩ : Fin 8) = (2 : Fin 8) := Fin.ext rfl

private theorem fin8_coord3 : (⟨3, by decide⟩ : Fin 8) = (3 : Fin 8) := Fin.ext rfl

private theorem fin8_coord4 : (⟨4, by decide⟩ : Fin 8) = (4 : Fin 8) := Fin.ext rfl

private theorem fin8_coord5 : (⟨5, by decide⟩ : Fin 8) = (5 : Fin 8) := Fin.ext rfl

private theorem fin8_coord6 : (⟨6, by decide⟩ : Fin 8) = (6 : Fin 8) := Fin.ext rfl

private theorem fin8_coord7 : (⟨7, by decide⟩ : Fin 8) = (7 : Fin 8) := Fin.ext rfl
attribute [local simp] fin8_coord2 fin8_coord3 fin8_coord4 fin8_coord5 fin8_coord6 fin8_coord7

private def planeIndex (I : Finset (Fin 6)) : Fin 96 :=
  ⟨if sixMask I < 6 then 33 + sixMask I else 32 + sixMask I, by
    have hmask : sixMask I ≤ 63 := by fin_cases I <;> decide
    split_ifs <;> omega⟩

private def planeGapRow (c : RemainingCell) (I : Finset (Fin 6)) : Fin 9 → ℚ :=
  fun j => if j = 0 then
      if literalPattern (sourceId c) I then 0 else 25 / 64
    else
      (if j.val = 2 ∨ j.val = 3 then (-3 / 2 : ℚ) else 0) -
      (if ∃ i ∈ I, i.val + 1 = j.val then
        if literalPattern (sourceId c) I then (-3 / 2 : ℚ) else 1 / 2 else 0)

/-- A finite source equality for all eleven literal row systems. The
closed decision body is a source proposal; it has not been evaluated. -/
private theorem plane_row_01 (c : RemainingCell) :
    (rows c (planeIndex ({0} : Finset (Fin 6)))).2 = planeGapRow c ({0} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0} : Finset (Fin 6)) = (34 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (34 : Fin 96)).2 = ![25/64, -1/2, -3/2, -3/2, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_02 (c : RemainingCell) :
    (rows c (planeIndex ({1} : Finset (Fin 6)))).2 = planeGapRow c ({1} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1} : Finset (Fin 6)) = (35 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (35 : Fin 96)).2 = ![25/64, 0, -2, -3/2, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_03 (c : RemainingCell) :
    (rows c (planeIndex ({0,1} : Finset (Fin 6)))).2 = planeGapRow c ({0,1} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1} : Finset (Fin 6)) = (36 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (36 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_04 (c : RemainingCell) :
    (rows c (planeIndex ({2} : Finset (Fin 6)))).2 = planeGapRow c ({2} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2} : Finset (Fin 6)) = (37 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (37 : Fin 96)).2 = ![25/64, 0, -3/2, -2, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({2} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_05 (c : RemainingCell) :
    (rows c (planeIndex ({0,2} : Finset (Fin 6)))).2 = planeGapRow c ({0,2} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2} : Finset (Fin 6)) = (38 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (38 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_07 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2} : Finset (Fin 6)) = (39 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (39 : Fin 96)).2 = ![0, 3/2, 0, 0, 0, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_08 (c : RemainingCell) :
    (rows c (planeIndex ({3} : Finset (Fin 6)))).2 = planeGapRow c ({3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({3} : Finset (Fin 6)) = (40 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (40 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, -1/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({3} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_09 (c : RemainingCell) :
    (rows c (planeIndex ({0,3} : Finset (Fin 6)))).2 = planeGapRow c ({0,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,3} : Finset (Fin 6)) = (41 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (41 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 3/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,3} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_10 (c : RemainingCell) :
    (rows c (planeIndex ({1,3} : Finset (Fin 6)))).2 = planeGapRow c ({1,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,3} : Finset (Fin 6)) = (42 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (42 : Fin 96)).2 = ![25/64, 0, -2, -3/2, -1/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,3} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_11 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,3} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,3} : Finset (Fin 6)) = (43 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (43 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 3/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,3} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_12 (c : RemainingCell) :
    (rows c (planeIndex ({2,3} : Finset (Fin 6)))).2 = planeGapRow c ({2,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,3} : Finset (Fin 6)) = (44 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (44 : Fin 96)).2 = ![25/64, 0, -3/2, -2, -1/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({2,3} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_13 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,3} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,3} : Finset (Fin 6)) = (45 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (45 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 3/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,3} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_14 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,3} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,3} : Finset (Fin 6)) = (46 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (46 : Fin 96)).2 = ![0, 0, 0, 0, 3/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,3} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_15 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,3} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,3} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,3} : Finset (Fin 6)) = (47 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (47 : Fin 96)).2 = ![0, 3/2, 0, 0, 3/2, 0, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,3} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_16 (c : RemainingCell) :
    (rows c (planeIndex ({4} : Finset (Fin 6)))).2 = planeGapRow c ({4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({4} : Finset (Fin 6)) = (48 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (48 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, 0, -1/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({4} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_17 (c : RemainingCell) :
    (rows c (planeIndex ({0,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,4} : Finset (Fin 6)) = (49 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (49 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 0, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_18 (c : RemainingCell) :
    (rows c (planeIndex ({1,4} : Finset (Fin 6)))).2 = planeGapRow c ({1,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,4} : Finset (Fin 6)) = (50 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (50 : Fin 96)).2 = ![25/64, 0, -2, -3/2, 0, -1/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,4} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_19 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,4} : Finset (Fin 6)) = (51 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (51 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 0, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_20 (c : RemainingCell) :
    (rows c (planeIndex ({2,4} : Finset (Fin 6)))).2 = planeGapRow c ({2,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,4} : Finset (Fin 6)) = (52 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (52 : Fin 96)).2 = ![25/64, 0, -3/2, -2, 0, -1/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({2,4} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_21 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,4} : Finset (Fin 6)) = (53 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (53 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 0, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_22 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,4} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,4} : Finset (Fin 6)) = (54 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (54 : Fin 96)).2 = ![0, 0, 0, 0, 0, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_23 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,4} : Finset (Fin 6)) = (55 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (55 : Fin 96)).2 = ![0, 3/2, 0, 0, 0, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_24 (c : RemainingCell) :
    (rows c (planeIndex ({3,4} : Finset (Fin 6)))).2 = planeGapRow c ({3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({3,4} : Finset (Fin 6)) = (56 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (56 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, -1/2, -1/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({3,4} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_25 (c : RemainingCell) :
    (rows c (planeIndex ({0,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,3,4} : Finset (Fin 6)) = (57 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (57 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,3,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_26 (c : RemainingCell) :
    (rows c (planeIndex ({1,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({1,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,3,4} : Finset (Fin 6)) = (58 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({1,3,4} : Finset (Fin 6)) = decide ((58 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (58 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (58 : Fin 96)).2 = ![0,0,0,-3/2,3/2,3/2,0,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,4} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (58 : Fin 96)).2 = ![25/64, 0, -2, -3/2, -1/2, -1/2, 0, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,4} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_27 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,3,4} : Finset (Fin 6)) = (59 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (59 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 3/2, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,3,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_28 (c : RemainingCell) :
    (rows c (planeIndex ({2,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({2,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,3,4} : Finset (Fin 6)) = (60 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({2,3,4} : Finset (Fin 6)) = decide ((60 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (60 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (60 : Fin 96)).2 = ![0,0,-3/2,0,3/2,3/2,0,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,4} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (60 : Fin 96)).2 = ![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,4} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_29 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,3,4} : Finset (Fin 6)) = (61 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (61 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 3/2, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,3,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_30 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,3,4} : Finset (Fin 6)) = (62 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (62 : Fin 96)).2 = ![0, 0, 0, 0, 3/2, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,3,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_31 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,3,4} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,3,4} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,3,4} : Finset (Fin 6)) = (63 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (63 : Fin 96)).2 = ![0, 3/2, 0, 0, 3/2, 3/2, 0, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,3,4} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_32 (c : RemainingCell) :
    (rows c (planeIndex ({5} : Finset (Fin 6)))).2 = planeGapRow c ({5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({5} : Finset (Fin 6)) = (64 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (64 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, 0, 0, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_33 (c : RemainingCell) :
    (rows c (planeIndex ({0,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,5} : Finset (Fin 6)) = (65 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (65 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 0, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_34 (c : RemainingCell) :
    (rows c (planeIndex ({1,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,5} : Finset (Fin 6)) = (66 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (66 : Fin 96)).2 = ![25/64, 0, -2, -3/2, 0, 0, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_35 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,5} : Finset (Fin 6)) = (67 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (67 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 0, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_36 (c : RemainingCell) :
    (rows c (planeIndex ({2,5} : Finset (Fin 6)))).2 = planeGapRow c ({2,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,5} : Finset (Fin 6)) = (68 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (68 : Fin 96)).2 = ![25/64, 0, -3/2, -2, 0, 0, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({2,5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_37 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,5} : Finset (Fin 6)) = (69 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (69 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 0, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_38 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,5} : Finset (Fin 6)) = (70 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (70 : Fin 96)).2 = ![0, 0, 0, 0, 0, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_39 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,5} : Finset (Fin 6)) = (71 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (71 : Fin 96)).2 = ![0, 3/2, 0, 0, 0, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_40 (c : RemainingCell) :
    (rows c (planeIndex ({3,5} : Finset (Fin 6)))).2 = planeGapRow c ({3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({3,5} : Finset (Fin 6)) = (72 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (72 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, -1/2, 0, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({3,5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_41 (c : RemainingCell) :
    (rows c (planeIndex ({0,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,3,5} : Finset (Fin 6)) = (73 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (73 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 3/2, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,3,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_42 (c : RemainingCell) :
    (rows c (planeIndex ({1,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,3,5} : Finset (Fin 6)) = (74 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({1,3,5} : Finset (Fin 6)) = decide ((74 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (74 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (74 : Fin 96)).2 = ![0,0,0,-3/2,3/2,0,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (74 : Fin 96)).2 = ![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_43 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,3,5} : Finset (Fin 6)) = (75 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (75 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 3/2, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,3,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_44 (c : RemainingCell) :
    (rows c (planeIndex ({2,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({2,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,3,5} : Finset (Fin 6)) = (76 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({2,3,5} : Finset (Fin 6)) = decide ((76 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (76 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (76 : Fin 96)).2 = ![0,0,-3/2,0,3/2,0,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (76 : Fin 96)).2 = ![25/64, 0, -3/2, -2, -1/2, 0, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_45 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,3,5} : Finset (Fin 6)) = (77 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (77 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 3/2, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,3,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_46 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,3,5} : Finset (Fin 6)) = (78 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (78 : Fin 96)).2 = ![0, 0, 0, 0, 3/2, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,3,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_47 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,3,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,3,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,3,5} : Finset (Fin 6)) = (79 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (79 : Fin 96)).2 = ![0, 3/2, 0, 0, 3/2, 0, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,3,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_48 (c : RemainingCell) :
    (rows c (planeIndex ({4,5} : Finset (Fin 6)))).2 = planeGapRow c ({4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({4,5} : Finset (Fin 6)) = (80 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (80 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, 0, -1/2, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({4,5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_49 (c : RemainingCell) :
    (rows c (planeIndex ({0,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,4,5} : Finset (Fin 6)) = (81 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (81 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 0, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_50 (c : RemainingCell) :
    (rows c (planeIndex ({1,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,4,5} : Finset (Fin 6)) = (82 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({1,4,5} : Finset (Fin 6)) = decide ((82 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (82 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (82 : Fin 96)).2 = ![0,0,0,-3/2,0,3/2,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,4,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (82 : Fin 96)).2 = ![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,4,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_51 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,4,5} : Finset (Fin 6)) = (83 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (83 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 0, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_52 (c : RemainingCell) :
    (rows c (planeIndex ({2,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({2,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,4,5} : Finset (Fin 6)) = (84 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({2,4,5} : Finset (Fin 6)) = decide ((84 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (84 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (84 : Fin 96)).2 = ![0,0,-3/2,0,0,3/2,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,4,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (84 : Fin 96)).2 = ![25/64, 0, -3/2, -2, 0, -1/2, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,4,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_53 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,4,5} : Finset (Fin 6)) = (85 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (85 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 0, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_54 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,4,5} : Finset (Fin 6)) = (86 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (86 : Fin 96)).2 = ![0, 0, 0, 0, 0, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_55 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,4,5} : Finset (Fin 6)) = (87 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (87 : Fin 96)).2 = ![0, 3/2, 0, 0, 0, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_56 (c : RemainingCell) :
    (rows c (planeIndex ({3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({3,4,5} : Finset (Fin 6)) = (88 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (88 : Fin 96)).2 = ![25/64, 0, -3/2, -3/2, -1/2, -1/2, -1/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({3,4,5} : Finset (Fin 6)) = false := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_57 (c : RemainingCell) :
    (rows c (planeIndex ({0,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,3,4,5} : Finset (Fin 6)) = (89 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (89 : Fin 96)).2 = ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,3,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_58 (c : RemainingCell) :
    (rows c (planeIndex ({1,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,3,4,5} : Finset (Fin 6)) = (90 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({1,3,4,5} : Finset (Fin 6)) = decide ((90 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (90 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (90 : Fin 96)).2 = ![0,0,0,-3/2,3/2,3/2,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,4,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (90 : Fin 96)).2 = ![25/64, 0, -2, -3/2, -1/2, -1/2, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({1,3,4,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_59 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,3,4,5} : Finset (Fin 6)) = (91 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (91 : Fin 96)).2 = ![0, 3/2, 0, -3/2, 3/2, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,3,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_60 (c : RemainingCell) :
    (rows c (planeIndex ({2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({2,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({2,3,4,5} : Finset (Fin 6)) = (92 : Fin 96) := by rfl
  rw [hindex]
  have hp : literalPattern (sourceId c) ({2,3,4,5} : Finset (Fin 6)) = decide ((92 : Fin 96) ∈ changedRows c) := by
    fin_cases c <;> decide
  by_cases hm : (92 : Fin 96) ∈ changedRows c
  · have hrow : (rows c (92 : Fin 96)).2 = ![0,0,-3/2,0,3/2,3/2,3/2,0,0] := by
      rw [rows, if_pos hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,4,5} : Finset (Fin 6)) = true := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

  · have hrow : (rows c (92 : Fin 96)).2 = ![25/64, 0, -3/2, -2, -1/2, -1/2, -1/2, 0, 0] := by
      rw [rows, if_neg hm]
      rfl
    rw [hrow]
    have hpattern : literalPattern (sourceId c) ({2,3,4,5} : Finset (Fin 6)) = false := by simpa [hm] using hp
    funext j
    fin_cases j <;>
      simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
        Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
        Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
        false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
        Bool.false_eq_true,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_61 (c : RemainingCell) :
    (rows c (planeIndex ({0,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,2,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,2,3,4,5} : Finset (Fin 6)) = (93 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (93 : Fin 96)).2 = ![0, 3/2, -3/2, 0, 3/2, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,2,3,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_62 (c : RemainingCell) :
    (rows c (planeIndex ({1,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({1,2,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({1,2,3,4,5} : Finset (Fin 6)) = (94 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (94 : Fin 96)).2 = ![0, 0, 0, 0, 3/2, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({1,2,3,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_63 (c : RemainingCell) :
    (rows c (planeIndex ({0,1,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow c ({0,1,2,3,4,5} : Finset (Fin 6)) := by
  have hindex : planeIndex ({0,1,2,3,4,5} : Finset (Fin 6)) = (95 : Fin 96) := by rfl
  rw [hindex]
  have hrow : (rows c (95 : Fin 96)).2 = ![0, 3/2, 0, 0, 3/2, 3/2, 3/2, 0, 0] := by
    fin_cases c <;> rfl
  rw [hrow]
  have hpattern : literalPattern (sourceId c) ({0,1,2,3,4,5} : Finset (Fin 6)) = true := by
    fin_cases c <;> decide
  funext j
  fin_cases j <;>
    simp only [planeGapRow, hpattern, Finset.exists_mem_insert,
      Finset.mem_singleton, Finset.mem_insert, Finset.notMem_empty,
      Finset.exists_mem_empty_iff, exists_eq_left, exists_false, or_and_right, exists_or,
      false_and, and_false, true_and, and_true] <;>
    norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      Bool.false_eq_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl


private theorem plane_row_exact : ∀ (c : RemainingCell) (I : Finset (Fin 6)),
    I ≠ ∅ → I ≠ winner6 → (rows c (planeIndex I)).2 = planeGapRow c I := by
  intro c I hne hw
  fin_cases I
  · exact (hne (by decide)).elim
  · exact plane_row_01 c
  · exact plane_row_02 c
  · exact plane_row_03 c
  · exact plane_row_04 c
  · exact plane_row_05 c
  · exact (hw (by decide)).elim
  · exact plane_row_07 c
  · exact plane_row_08 c
  · exact plane_row_09 c
  · exact plane_row_10 c
  · exact plane_row_11 c
  · exact plane_row_12 c
  · exact plane_row_13 c
  · exact plane_row_14 c
  · exact plane_row_15 c
  · exact plane_row_16 c
  · exact plane_row_17 c
  · exact plane_row_18 c
  · exact plane_row_19 c
  · exact plane_row_20 c
  · exact plane_row_21 c
  · exact plane_row_22 c
  · exact plane_row_23 c
  · exact plane_row_24 c
  · exact plane_row_25 c
  · exact plane_row_26 c
  · exact plane_row_27 c
  · exact plane_row_28 c
  · exact plane_row_29 c
  · exact plane_row_30 c
  · exact plane_row_31 c
  · exact plane_row_32 c
  · exact plane_row_33 c
  · exact plane_row_34 c
  · exact plane_row_35 c
  · exact plane_row_36 c
  · exact plane_row_37 c
  · exact plane_row_38 c
  · exact plane_row_39 c
  · exact plane_row_40 c
  · exact plane_row_41 c
  · exact plane_row_42 c
  · exact plane_row_43 c
  · exact plane_row_44 c
  · exact plane_row_45 c
  · exact plane_row_46 c
  · exact plane_row_47 c
  · exact plane_row_48 c
  · exact plane_row_49 c
  · exact plane_row_50 c
  · exact plane_row_51 c
  · exact plane_row_52 c
  · exact plane_row_53 c
  · exact plane_row_54 c
  · exact plane_row_55 c
  · exact plane_row_56 c
  · exact plane_row_57 c
  · exact plane_row_58 c
  · exact plane_row_59 c
  · exact plane_row_60 c
  · exact plane_row_61 c
  · exact plane_row_62 c
  · exact plane_row_63 c

private theorem plane_gap_eval (c : RemainingCell) (I : Finset (Fin 6)) (t : Point8) :
    evalRow (planeGapRow c I) t =
      P2OriginalAscendingEighthCapDictionary.R t - chosenOldPlane (literalPattern (sourceId c)) t I := by
  fin_cases I
  · change evalRow (planeGapRow c (∅ : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t (∅ : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) (∅ : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,3} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,3} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,3,4} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,3,4} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,3,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,3,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({2,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({2,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,2,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,2,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({1,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({1,2,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({1,2,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (planeGapRow c ({0,1,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern (sourceId c)) t ({0,1,2,3,4,5} : Finset (Fin 6))
    cases hp : literalPattern (sourceId c) ({0,1,2,3,4,5} : Finset (Fin 6)) <;>
      simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
        planeGapRow, hp, chosenOldPlane, subsetSum,
        P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
        VariableEnvelope.A, VariableEnvelope.C,
        Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
        Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
        or_and_right, exists_or, false_and, and_false, true_and, and_true] <;>
      norm_num only [if_true, if_false, false_or, or_false, true_or, or_true,
        Bool.false_eq_true, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
        Fin.val_zero, Fin.val_one, Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
        fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
        Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ,
        Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
        Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
        Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
        Rat.cast_zero, Rat.cast_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring

theorem sourceRows_old_planes (c : RemainingCell) (t : Point8) (h : sourceRows c t) :
    OldPlaneRows (literalPattern (sourceId c)) t := by
  intro I hI
  have hne : I ≠ ∅ := by simpa [oldMasks] using hI
  by_cases hw : I = winner6
  · subst I
    have hp : literalPattern (sourceId c) winner6 = true := by fin_cases c <;> decide
    simpa only [chosenOldPlane, hp, if_true,
      P2OriginalAscendingEighthCapDictionary.winner6_sum,
      P2OriginalAscendingEighthCapDictionary.R] using
      (le_refl (VariableEnvelope.C (P2OriginalAscendingEighthCapDictionary.d t)))
  · have hr := h (planeIndex I)
    rw [plane_row_exact c I hne hw, plane_gap_eval] at hr
    linarith

private theorem common_order (t : Point8) (h : commonRows t) : StrictAnti t := by
  have h01 := h 3
  have h12 := h 4
  have h23 := h 5
  have h34 := h 6
  have h45 := h 7
  have h56 := h 8
  have h67 := h 9
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod] at h01 h12 h23 h34 h45 h56 h67
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h45
  · exact h56
  · exact h67

private theorem common_ascending (t : Point8) (h : commonRows t) :
    A (selectedSum t) < C (selectedSum t) := by
  have hr := h 17
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod] at hr
  dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.selectedSum]
  linarith

private theorem common_descending_gain (t : Point8) (h : commonRows t) :
    C (d t) < A (d t) ∧ P2OriginalAscendingEighthCapDictionary.R t < M t := by
  have hw := h 14
  have hg := h 16
  have ha := common_ascending t h
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod] at hw hg
  rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
  dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, P2OriginalAscendingEighthCapDictionary.selectedSum, P2OriginalAscendingEighthCapDictionary.eta]
  constructor <;> linarith

private theorem row_coeff018 : (baseRows (18 : Fin 96)).2 =
    ![499999/1000000, -3/2, 0, 0, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff019 : (baseRows (19 : Fin 96)).2 =
    ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff020 : (baseRows (20 : Fin 96)).2 =
    ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, -1/2] := rfl

private theorem row_coeff021 : (baseRows (21 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff022 : (baseRows (22 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, -1/2] := rfl

private theorem row_coeff023 : (baseRows (23 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, 1/2] := rfl

private theorem row_coeff024 : (baseRows (24 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, -1/2] := rfl

private theorem row_coeff025 : (baseRows (25 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, 1/2] := rfl

private theorem row_coeff026 : (baseRows (26 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, -1/2] := rfl

private theorem row_coeff027 : (baseRows (27 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, 1/2] := rfl

private theorem row_coeff028 : (baseRows (28 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, -1/2] := rfl

private theorem row_coeff029 : (baseRows (29 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, 1/2] := rfl

private theorem row_coeff030 : (baseRows (30 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, -1/2] := rfl

private theorem row_coeff031 : (baseRows (31 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -1, -3/2] := rfl

private def fullIndex : Fin 8 → Fin 34 := ![18,19,21,23,25,27,29,31]

private theorem full_square_row (t : Point8) (j : Fin 8)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (baseRows ⟨(fullIndex j).val, by omega⟩).2 t = M t - fullSquare t j := by
  rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
  fin_cases j
  · change evalRow (baseRows (18 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (0 : Fin 8)
    rw [row_coeff018]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (19 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (1 : Fin 8)
    rw [row_coeff019]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (21 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (2 : Fin 8)
    rw [row_coeff021]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (23 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (3 : Fin 8)
    rw [row_coeff023]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (25 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (4 : Fin 8)
    rw [row_coeff025]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (27 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (5 : Fin 8)
    rw [row_coeff027]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (29 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (6 : Fin 8)
    rw [row_coeff029]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (31 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.fullSquare t (7 : Fin 8)
    rw [row_coeff031]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring

private theorem selected_square_row (t : Point8) (j : Fin 8) (hj0 : 0 < j) (hj7 : j < 7)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (baseRows ⟨18 + 2 * j.val, by omega⟩).2 t = M t - selectedRemainingSquare t j := by
  rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
  fin_cases j
  · norm_num [Fin.lt_def] at hj0
  · change evalRow (baseRows (20 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (1 : Fin 8)
    rw [row_coeff020]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (22 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (2 : Fin 8)
    rw [row_coeff022]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (24 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (3 : Fin 8)
    rw [row_coeff024]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (26 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (4 : Fin 8)
    rw [row_coeff026]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (28 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (5 : Fin 8)
    rw [row_coeff028]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · change evalRow (baseRows (30 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare t (6 : Fin 8)
    rw [row_coeff030]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalAscendingEighthCapDictionary.fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      P2OriginalAscendingEighthCapDictionary.selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
      P2OriginalAscendingEighthCapDictionary.selectedSum, VariableEnvelope.A,
      P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      if_true, if_false, and_true, true_and, false_and, and_false,
      Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> ring
  · norm_num [Fin.lt_def] at hj7

/-- The complete guard is derived from each of the eleven actual raw
navigation row systems, with its own exact sourceId and changedRows. -/
theorem sourceRows_cellGuard (c : RemainingCell) (t : Point8) (h : sourceRows c t) :
    CellGuard (literalPattern (sourceId c)) t := by
  have hc := sourceRows_common c t h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h10 := hc 10
  have h11 := hc 11
  have h12 := hc 12
  have h13 := hc 13
  have h15 := hc 15
  have h32 := hc 32
  have h33 := hc 33
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod] at h0 h1 h2 h10 h11 h12 h13 h15 h32 h33
  have ha := common_ascending t hc
  have hgain := common_descending_gain t hc
  refine {
    order := common_order t hc
    last_pos := by linarith
    largest := by dsimp [VariableEnvelope.mu]; linarith
    third_activation := by linarith
    compact_cutoff := by linarith
    first_history := ?_
    history3 := ?_
    history5 := ?_
    history7 := ?_
    old_descending := hgain.1
    old_W := ?_
    old_planes := sourceRows_old_planes c t h
    new_ascending := ha
    improvement := hgain.2
    full_squares := ?_
    selected_squares := ?_
    old_residual := ?_
    new_residual := ?_ }
  · dsimp [P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [P2OriginalAscendingEighthCapDictionary.oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [P2OriginalAscendingEighthCapDictionary.oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [P2OriginalAscendingEighthCapDictionary.oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · dsimp [VariableEnvelope.B, VariableEnvelope.cap, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · intro j
    have hr := hc (fullIndex j)
    rw [full_square_row t j ha] at hr
    linarith
  · intro j hj0 hj7
    have hr := hc (⟨18 + 2 * j.val, by omega⟩ : Fin 34)
    rw [selected_square_row t j hj0 hj7 ha] at hr
    linarith
  · norm_num [P2OriginalAscendingEighthCapDictionary.S, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
    norm_num [P2OriginalAscendingEighthCapDictionary.S, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, VariableEnvelope.A, P2OriginalAscendingEighthCapDictionary.selectedSum, P2OriginalAscendingEighthCapDictionary.eta]
    linarith

/-- Literal source separator from already adopted equal-parent cell7.
The separator can be mask42, mask28, mask60 or mask50; mask26 alone would
incorrectly cover only the first few cells. -/
theorem sourceRows_not_seed7 (c : RemainingCell) (t : Point8) (h : sourceRows c t)
    (hseed : P4AOriginalSeed7Unequal15Literal.seed7SourceRows t) : False := by
  have hl := h (seedSeparator c)
  have hr := hseed (seedSeparator c)
  have hd := (sourceRows_cellGuard c t h).old_descending
  fin_cases c
  · change 0 < evalRow (![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![0, 0, 0, -3/2, 3/2, 0, 3/2, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![0, 0, 0, -3/2, 3/2, 0, 3/2, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, -1/2, 0, 0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![0, 0, -3/2, 0, 3/2, 3/2, 3/2, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,0,-3/2,0,3/2,3/2,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,0,-3/2,0,3/2,3/2,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]
  · change 0 < evalRow (![0,0,-3/2,0,3/2,3/2,0,0,0] : Fin 9 → ℚ) t at hl
    change 0 < evalRow (![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] : Fin 9 → ℚ) t at hr
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ, Fin.lt_def,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Fin.val_zero, Fin.val_one,
      Fin.val_ofNat, Fin.mk_zero, Fin.mk_one,
      fin8_coord2, fin8_coord3, fin8_coord4, fin8_coord5, fin8_coord6, fin8_coord7,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg,
      Rat.cast_zero, Rat.cast_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] at hl hr
    dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.d] at hd
    linarith only [hl, hr, hd]

end
end ImbalancedChen.P4AOriginalRemainingAscendingAtlas
