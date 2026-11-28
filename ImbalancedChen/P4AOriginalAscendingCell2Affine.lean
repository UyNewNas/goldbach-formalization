import ImbalancedChen.P4AOriginalAscendingCell1ActualChronology
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal next ascending cell2, in the immutable navigation's row order.
Compared with cell1 exactly row92 (old mask60) changes from A to C.
This source proves its own full CellGuard; the preceding cells' guards are not reused.
-/
namespace ImbalancedChen.P4AOriginalAscendingCell2Affine
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42 P4AOriginalAscendingCell0AfterSeed7
abbrev Point8 := Fin 8 → ℝ

/-- Raw source cell2 row92; all other 95 rows are byte-level identical
rational vectors in the pinned cell1/cell2 navigation. -/
def rows2 (k : Fin 96) : String × (Fin 9 → ℚ) :=
  if k = 92 then
    ("old subset 60 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,3/2,3/2,0,0])
  else P4AOriginalAscendingCell1Affine.rows1 k

abbrev sourceRow := rows2
abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine

private theorem fin8_coord2 : (⟨2, by decide⟩ : Fin 8) = (2 : Fin 8) := Fin.ext rfl
private theorem fin8_coord3 : (⟨3, by decide⟩ : Fin 8) = (3 : Fin 8) := Fin.ext rfl
private theorem fin8_coord4 : (⟨4, by decide⟩ : Fin 8) = (4 : Fin 8) := Fin.ext rfl
private theorem fin8_coord5 : (⟨5, by decide⟩ : Fin 8) = (5 : Fin 8) := Fin.ext rfl
private theorem fin8_coord6 : (⟨6, by decide⟩ : Fin 8) = (6 : Fin 8) := Fin.ext rfl
private theorem fin8_coord7 : (⟨7, by decide⟩ : Fin 8) = (7 : Fin 8) := Fin.ext rfl
attribute [local simp] fin8_coord2 fin8_coord3 fin8_coord4 fin8_coord5 fin8_coord6 fin8_coord7

private theorem row_coeff000 : (sourceRow (0 : Fin 96)).2 =
    ![25/128, -1, 0, 0, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff001 : (sourceRow (1 : Fin 96)).2 =
    ![-1/100, 0, 0, 1, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff002 : (sourceRow (2 : Fin 96)).2 =
    ![-53/13824, 0, 0, 0, 0, 0, 0, 0, 1] := rfl

private theorem row_coeff003 : (sourceRow (3 : Fin 96)).2 =
    ![0, 1, -1, 0, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff004 : (sourceRow (4 : Fin 96)).2 =
    ![0, 0, 1, -1, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff005 : (sourceRow (5 : Fin 96)).2 =
    ![0, 0, 0, 1, -1, 0, 0, 0, 0] := rfl

private theorem row_coeff006 : (sourceRow (6 : Fin 96)).2 =
    ![0, 0, 0, 0, 1, -1, 0, 0, 0] := rfl

private theorem row_coeff007 : (sourceRow (7 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 1, -1, 0, 0] := rfl

private theorem row_coeff008 : (sourceRow (8 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 0, 1, -1, 0] := rfl

private theorem row_coeff009 : (sourceRow (9 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 0, 0, 1, -1] := rfl

private theorem row_coeff010 : (sourceRow (10 : Fin 96)).2 =
    ![57/64, -3, -3/2, -3/2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff011 : (sourceRow (11 : Fin 96)).2 =
    ![57/64, -1, -5/2, -9/2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff012 : (sourceRow (12 : Fin 96)).2 =
    ![57/64, -1, -5/2, -5/2, -1, -3, 0, 0, 0] := rfl

private theorem row_coeff013 : (sourceRow (13 : Fin 96)).2 =
    ![57/64, -1, -5/2, -5/2, -1, -1, -1, -3, 0] := rfl

private theorem row_coeff014 : (sourceRow (14 : Fin 96)).2 =
    ![-25/64, 0, 2, 2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff015 : (sourceRow (15 : Fin 96)).2 =
    ![75/256, 0, -3/2, -9/8, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff016 : (sourceRow (16 : Fin 96)).2 =
    ![-195313/500000, 1/2, 3/2, 3/2, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff017 : (sourceRow (17 : Fin 96)).2 =
    ![25/64, -2, 0, 0, 0, 0, 0, 0, -2] := rfl

private theorem row_coeff018 : (sourceRow (18 : Fin 96)).2 =
    ![499999/1000000, -3/2, 0, 0, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff019 : (sourceRow (19 : Fin 96)).2 =
    ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff020 : (sourceRow (20 : Fin 96)).2 =
    ![499999/1000000, -1/2, -2, 0, 0, 0, 0, 0, -1/2] := rfl

private theorem row_coeff021 : (sourceRow (21 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, 1/2] := rfl

private theorem row_coeff022 : (sourceRow (22 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -2, 0, 0, 0, 0, -1/2] := rfl

private theorem row_coeff023 : (sourceRow (23 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, 1/2] := rfl

private theorem row_coeff024 : (sourceRow (24 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -2, 0, 0, 0, -1/2] := rfl

private theorem row_coeff025 : (sourceRow (25 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, 1/2] := rfl

private theorem row_coeff026 : (sourceRow (26 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -2, 0, 0, -1/2] := rfl

private theorem row_coeff027 : (sourceRow (27 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, 1/2] := rfl

private theorem row_coeff028 : (sourceRow (28 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -2, 0, -1/2] := rfl

private theorem row_coeff029 : (sourceRow (29 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, 1/2] := rfl

private theorem row_coeff030 : (sourceRow (30 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -2, -1/2] := rfl

private theorem row_coeff031 : (sourceRow (31 : Fin 96)).2 =
    ![499999/1000000, -1/2, -1, -1, -1, -1, -1, -1, -3/2] := rfl

private theorem row_coeff032 : (sourceRow (32 : Fin 96)).2 =
    ![57/64, -1, -5/2, -5/2, -1, -1, -1, -1, -2] := rfl

private theorem row_coeff033 : (sourceRow (33 : Fin 96)).2 =
    ![-499999/1000000, 1/2, 1, 1, 1, 1, 1, 1, 7/2] := rfl

private theorem row_coeff034 : (sourceRow (34 : Fin 96)).2 =
    ![25/64, -1/2, -3/2, -3/2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff035 : (sourceRow (35 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff036 : (sourceRow (36 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff037 : (sourceRow (37 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff038 : (sourceRow (38 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff039 : (sourceRow (39 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 0, 0, 0, 0, 0] := rfl

private theorem row_coeff040 : (sourceRow (40 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, -1/2, 0, 0, 0, 0] := rfl

private theorem row_coeff041 : (sourceRow (41 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 3/2, 0, 0, 0, 0] := rfl

private theorem row_coeff042 : (sourceRow (42 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, -1/2, 0, 0, 0, 0] := rfl

private theorem row_coeff043 : (sourceRow (43 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 3/2, 0, 0, 0, 0] := rfl

private theorem row_coeff044 : (sourceRow (44 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, -1/2, 0, 0, 0, 0] := rfl

private theorem row_coeff045 : (sourceRow (45 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 3/2, 0, 0, 0, 0] := rfl

private theorem row_coeff046 : (sourceRow (46 : Fin 96)).2 =
    ![0, 0, 0, 0, 3/2, 0, 0, 0, 0] := rfl

private theorem row_coeff047 : (sourceRow (47 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 3/2, 0, 0, 0, 0] := rfl

private theorem row_coeff048 : (sourceRow (48 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, 0, -1/2, 0, 0, 0] := rfl

private theorem row_coeff049 : (sourceRow (49 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 0, 3/2, 0, 0, 0] := rfl

private theorem row_coeff050 : (sourceRow (50 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, 0, -1/2, 0, 0, 0] := rfl

private theorem row_coeff051 : (sourceRow (51 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 0, 3/2, 0, 0, 0] := rfl

private theorem row_coeff052 : (sourceRow (52 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, 0, -1/2, 0, 0, 0] := rfl

private theorem row_coeff053 : (sourceRow (53 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 0, 3/2, 0, 0, 0] := rfl

private theorem row_coeff054 : (sourceRow (54 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 3/2, 0, 0, 0] := rfl

private theorem row_coeff055 : (sourceRow (55 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 0, 3/2, 0, 0, 0] := rfl

private theorem row_coeff056 : (sourceRow (56 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, -1/2, -1/2, 0, 0, 0] := rfl

private theorem row_coeff057 : (sourceRow (57 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 0, 0, 0] := rfl

private theorem row_coeff058 : (sourceRow (58 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, -1/2, -1/2, 0, 0, 0] := rfl

private theorem row_coeff059 : (sourceRow (59 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 3/2, 3/2, 0, 0, 0] := rfl

private theorem row_coeff060 : (sourceRow (60 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, -1/2, -1/2, 0, 0, 0] := rfl

private theorem row_coeff061 : (sourceRow (61 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 3/2, 3/2, 0, 0, 0] := rfl

private theorem row_coeff062 : (sourceRow (62 : Fin 96)).2 =
    ![0, 0, 0, 0, 3/2, 3/2, 0, 0, 0] := rfl

private theorem row_coeff063 : (sourceRow (63 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 3/2, 3/2, 0, 0, 0] := rfl

private theorem row_coeff064 : (sourceRow (64 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, 0, 0, -1/2, 0, 0] := rfl

private theorem row_coeff065 : (sourceRow (65 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 0, 0, 3/2, 0, 0] := rfl

private theorem row_coeff066 : (sourceRow (66 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, 0, 0, -1/2, 0, 0] := rfl

private theorem row_coeff067 : (sourceRow (67 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 0, 0, 3/2, 0, 0] := rfl

private theorem row_coeff068 : (sourceRow (68 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, 0, 0, -1/2, 0, 0] := rfl

private theorem row_coeff069 : (sourceRow (69 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 0, 0, 3/2, 0, 0] := rfl

private theorem row_coeff070 : (sourceRow (70 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 0, 3/2, 0, 0] := rfl

private theorem row_coeff071 : (sourceRow (71 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 0, 0, 3/2, 0, 0] := rfl

private theorem row_coeff072 : (sourceRow (72 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, -1/2, 0, -1/2, 0, 0] := rfl

private theorem row_coeff073 : (sourceRow (73 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 3/2, 0, 3/2, 0, 0] := rfl

private theorem row_coeff074 : (sourceRow (74 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, -1/2, 0, -1/2, 0, 0] := rfl

private theorem row_coeff075 : (sourceRow (75 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 3/2, 0, 3/2, 0, 0] := rfl

private theorem row_coeff076 : (sourceRow (76 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, -1/2, 0, -1/2, 0, 0] := rfl

private theorem row_coeff077 : (sourceRow (77 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 3/2, 0, 3/2, 0, 0] := rfl

private theorem row_coeff078 : (sourceRow (78 : Fin 96)).2 =
    ![0, 0, 0, 0, 3/2, 0, 3/2, 0, 0] := rfl

private theorem row_coeff079 : (sourceRow (79 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 3/2, 0, 3/2, 0, 0] := rfl

private theorem row_coeff080 : (sourceRow (80 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, 0, -1/2, -1/2, 0, 0] := rfl

private theorem row_coeff081 : (sourceRow (81 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 0, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff082 : (sourceRow (82 : Fin 96)).2 =
    ![25/64, 0, -2, -3/2, 0, -1/2, -1/2, 0, 0] := rfl

private theorem row_coeff083 : (sourceRow (83 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 0, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff084 : (sourceRow (84 : Fin 96)).2 =
    ![25/64, 0, -3/2, -2, 0, -1/2, -1/2, 0, 0] := rfl

private theorem row_coeff085 : (sourceRow (85 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 0, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff086 : (sourceRow (86 : Fin 96)).2 =
    ![0, 0, 0, 0, 0, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff087 : (sourceRow (87 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 0, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff088 : (sourceRow (88 : Fin 96)).2 =
    ![25/64, 0, -3/2, -3/2, -1/2, -1/2, -1/2, 0, 0] := rfl

private theorem row_coeff089 : (sourceRow (89 : Fin 96)).2 =
    ![0, 3/2, -3/2, -3/2, 3/2, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff090 : (sourceRow (90 : Fin 96)).2 =
    ![0,0,0,-3/2,3/2,3/2,3/2,0,0] := rfl

private theorem row_coeff091 : (sourceRow (91 : Fin 96)).2 =
    ![0, 3/2, 0, -3/2, 3/2, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff092 : (sourceRow (92 : Fin 96)).2 =
    ![0,0,-3/2,0,3/2,3/2,3/2,0,0] := rfl

private theorem row_coeff093 : (sourceRow (93 : Fin 96)).2 =
    ![0, 3/2, -3/2, 0, 3/2, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff094 : (sourceRow (94 : Fin 96)).2 =
    ![0, 0, 0, 0, 3/2, 3/2, 3/2, 0, 0] := rfl

private theorem row_coeff095 : (sourceRow (95 : Fin 96)).2 =
    ![0, 3/2, 0, 0, 3/2, 3/2, 3/2, 0, 0] := rfl

def literalRows (t : Point8) : Prop := ∀ k : Fin 96, 0 < evalRow (rows2 k).2 t

/-- These four common rows still separate cell2 from the adopted seed7. -/
theorem literalRows_core (t : Point8) (h : literalRows t) : Cell0Affine t := by
  trace "CELL2_PROGRESS literalRows_core"
  have h14 := h (14 : Fin 96)
  have h16 := h (16 : Fin 96)
  have h17 := h (17 : Fin 96)
  have h58 := h (58 : Fin 96)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < evalRow cell0Row14 t at h14
    exact h14
  · change 0 < evalRow cell0Row16 t at h16
    exact h16
  · change 0 < evalRow cell0Row17 t at h17
    exact h17
  · change 0 < evalRow cell0Row58 t at h58
    exact h58

private def planeIndex (I : Finset (Fin 6)) : Fin 96 :=
  ⟨if sixMask I < 6 then 33 + sixMask I else 32 + sixMask I, by
    have hmask : sixMask I ≤ 63 := by fin_cases I <;> decide
    split_ifs <;> omega⟩

/-- The exact rational coefficients of R minus the selected old plane. -/
private def planeGapRow (I : Finset (Fin 6)) : Fin 9 → ℚ :=
  fun j => if j = 0 then
      if literalPattern 2 I then 0 else 25 / 64
    else
      (if j.val = 2 ∨ j.val = 3 then (-3 / 2 : ℚ) else 0) -
      (if ∃ i ∈ I, i.val + 1 = j.val then
        if literalPattern 2 I then (-3 / 2 : ℚ) else 1 / 2
       else 0)

/-- This finite equality checks the original row order, including the
omitted mask-6 identity. It does not check a sampled point. -/
private theorem plane_row_01 :
    (sourceRow (planeIndex ({0} : Finset (Fin 6)))).2 = planeGapRow ({0} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_01"
  have hindex : planeIndex ({0} : Finset (Fin 6)) = (34 : Fin 96) := by rfl
  rw [hindex, row_coeff034]
  have hpattern : literalPattern 2 ({0} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_02 :
    (sourceRow (planeIndex ({1} : Finset (Fin 6)))).2 = planeGapRow ({1} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_02"
  have hindex : planeIndex ({1} : Finset (Fin 6)) = (35 : Fin 96) := by rfl
  rw [hindex, row_coeff035]
  have hpattern : literalPattern 2 ({1} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_03 :
    (sourceRow (planeIndex ({0,1} : Finset (Fin 6)))).2 = planeGapRow ({0,1} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_03"
  have hindex : planeIndex ({0,1} : Finset (Fin 6)) = (36 : Fin 96) := by rfl
  rw [hindex, row_coeff036]
  have hpattern : literalPattern 2 ({0,1} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_04 :
    (sourceRow (planeIndex ({2} : Finset (Fin 6)))).2 = planeGapRow ({2} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_04"
  have hindex : planeIndex ({2} : Finset (Fin 6)) = (37 : Fin 96) := by rfl
  rw [hindex, row_coeff037]
  have hpattern : literalPattern 2 ({2} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_05 :
    (sourceRow (planeIndex ({0,2} : Finset (Fin 6)))).2 = planeGapRow ({0,2} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_05"
  have hindex : planeIndex ({0,2} : Finset (Fin 6)) = (38 : Fin 96) := by rfl
  rw [hindex, row_coeff038]
  have hpattern : literalPattern 2 ({0,2} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_07 :
    (sourceRow (planeIndex ({0,1,2} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_07"
  have hindex : planeIndex ({0,1,2} : Finset (Fin 6)) = (39 : Fin 96) := by rfl
  rw [hindex, row_coeff039]
  have hpattern : literalPattern 2 ({0,1,2} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_08 :
    (sourceRow (planeIndex ({3} : Finset (Fin 6)))).2 = planeGapRow ({3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_08"
  have hindex : planeIndex ({3} : Finset (Fin 6)) = (40 : Fin 96) := by rfl
  rw [hindex, row_coeff040]
  have hpattern : literalPattern 2 ({3} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_09 :
    (sourceRow (planeIndex ({0,3} : Finset (Fin 6)))).2 = planeGapRow ({0,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_09"
  have hindex : planeIndex ({0,3} : Finset (Fin 6)) = (41 : Fin 96) := by rfl
  rw [hindex, row_coeff041]
  have hpattern : literalPattern 2 ({0,3} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_10 :
    (sourceRow (planeIndex ({1,3} : Finset (Fin 6)))).2 = planeGapRow ({1,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_10"
  have hindex : planeIndex ({1,3} : Finset (Fin 6)) = (42 : Fin 96) := by rfl
  rw [hindex, row_coeff042]
  have hpattern : literalPattern 2 ({1,3} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_11 :
    (sourceRow (planeIndex ({0,1,3} : Finset (Fin 6)))).2 = planeGapRow ({0,1,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_11"
  have hindex : planeIndex ({0,1,3} : Finset (Fin 6)) = (43 : Fin 96) := by rfl
  rw [hindex, row_coeff043]
  have hpattern : literalPattern 2 ({0,1,3} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_12 :
    (sourceRow (planeIndex ({2,3} : Finset (Fin 6)))).2 = planeGapRow ({2,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_12"
  have hindex : planeIndex ({2,3} : Finset (Fin 6)) = (44 : Fin 96) := by rfl
  rw [hindex, row_coeff044]
  have hpattern : literalPattern 2 ({2,3} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_13 :
    (sourceRow (planeIndex ({0,2,3} : Finset (Fin 6)))).2 = planeGapRow ({0,2,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_13"
  have hindex : planeIndex ({0,2,3} : Finset (Fin 6)) = (45 : Fin 96) := by rfl
  rw [hindex, row_coeff045]
  have hpattern : literalPattern 2 ({0,2,3} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_14 :
    (sourceRow (planeIndex ({1,2,3} : Finset (Fin 6)))).2 = planeGapRow ({1,2,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_14"
  have hindex : planeIndex ({1,2,3} : Finset (Fin 6)) = (46 : Fin 96) := by rfl
  rw [hindex, row_coeff046]
  have hpattern : literalPattern 2 ({1,2,3} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_15 :
    (sourceRow (planeIndex ({0,1,2,3} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,3} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_15"
  have hindex : planeIndex ({0,1,2,3} : Finset (Fin 6)) = (47 : Fin 96) := by rfl
  rw [hindex, row_coeff047]
  have hpattern : literalPattern 2 ({0,1,2,3} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_16 :
    (sourceRow (planeIndex ({4} : Finset (Fin 6)))).2 = planeGapRow ({4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_16"
  have hindex : planeIndex ({4} : Finset (Fin 6)) = (48 : Fin 96) := by rfl
  rw [hindex, row_coeff048]
  have hpattern : literalPattern 2 ({4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_17 :
    (sourceRow (planeIndex ({0,4} : Finset (Fin 6)))).2 = planeGapRow ({0,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_17"
  have hindex : planeIndex ({0,4} : Finset (Fin 6)) = (49 : Fin 96) := by rfl
  rw [hindex, row_coeff049]
  have hpattern : literalPattern 2 ({0,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_18 :
    (sourceRow (planeIndex ({1,4} : Finset (Fin 6)))).2 = planeGapRow ({1,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_18"
  have hindex : planeIndex ({1,4} : Finset (Fin 6)) = (50 : Fin 96) := by rfl
  rw [hindex, row_coeff050]
  have hpattern : literalPattern 2 ({1,4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_19 :
    (sourceRow (planeIndex ({0,1,4} : Finset (Fin 6)))).2 = planeGapRow ({0,1,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_19"
  have hindex : planeIndex ({0,1,4} : Finset (Fin 6)) = (51 : Fin 96) := by rfl
  rw [hindex, row_coeff051]
  have hpattern : literalPattern 2 ({0,1,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_20 :
    (sourceRow (planeIndex ({2,4} : Finset (Fin 6)))).2 = planeGapRow ({2,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_20"
  have hindex : planeIndex ({2,4} : Finset (Fin 6)) = (52 : Fin 96) := by rfl
  rw [hindex, row_coeff052]
  have hpattern : literalPattern 2 ({2,4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_21 :
    (sourceRow (planeIndex ({0,2,4} : Finset (Fin 6)))).2 = planeGapRow ({0,2,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_21"
  have hindex : planeIndex ({0,2,4} : Finset (Fin 6)) = (53 : Fin 96) := by rfl
  rw [hindex, row_coeff053]
  have hpattern : literalPattern 2 ({0,2,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_22 :
    (sourceRow (planeIndex ({1,2,4} : Finset (Fin 6)))).2 = planeGapRow ({1,2,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_22"
  have hindex : planeIndex ({1,2,4} : Finset (Fin 6)) = (54 : Fin 96) := by rfl
  rw [hindex, row_coeff054]
  have hpattern : literalPattern 2 ({1,2,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_23 :
    (sourceRow (planeIndex ({0,1,2,4} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_23"
  have hindex : planeIndex ({0,1,2,4} : Finset (Fin 6)) = (55 : Fin 96) := by rfl
  rw [hindex, row_coeff055]
  have hpattern : literalPattern 2 ({0,1,2,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_24 :
    (sourceRow (planeIndex ({3,4} : Finset (Fin 6)))).2 = planeGapRow ({3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_24"
  have hindex : planeIndex ({3,4} : Finset (Fin 6)) = (56 : Fin 96) := by rfl
  rw [hindex, row_coeff056]
  have hpattern : literalPattern 2 ({3,4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_25 :
    (sourceRow (planeIndex ({0,3,4} : Finset (Fin 6)))).2 = planeGapRow ({0,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_25"
  have hindex : planeIndex ({0,3,4} : Finset (Fin 6)) = (57 : Fin 96) := by rfl
  rw [hindex, row_coeff057]
  have hpattern : literalPattern 2 ({0,3,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_26 :
    (sourceRow (planeIndex ({1,3,4} : Finset (Fin 6)))).2 = planeGapRow ({1,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_26"
  have hindex : planeIndex ({1,3,4} : Finset (Fin 6)) = (58 : Fin 96) := by rfl
  rw [hindex, row_coeff058]
  have hpattern : literalPattern 2 ({1,3,4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_27 :
    (sourceRow (planeIndex ({0,1,3,4} : Finset (Fin 6)))).2 = planeGapRow ({0,1,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_27"
  have hindex : planeIndex ({0,1,3,4} : Finset (Fin 6)) = (59 : Fin 96) := by rfl
  rw [hindex, row_coeff059]
  have hpattern : literalPattern 2 ({0,1,3,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_28 :
    (sourceRow (planeIndex ({2,3,4} : Finset (Fin 6)))).2 = planeGapRow ({2,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_28"
  have hindex : planeIndex ({2,3,4} : Finset (Fin 6)) = (60 : Fin 96) := by rfl
  rw [hindex, row_coeff060]
  have hpattern : literalPattern 2 ({2,3,4} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_29 :
    (sourceRow (planeIndex ({0,2,3,4} : Finset (Fin 6)))).2 = planeGapRow ({0,2,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_29"
  have hindex : planeIndex ({0,2,3,4} : Finset (Fin 6)) = (61 : Fin 96) := by rfl
  rw [hindex, row_coeff061]
  have hpattern : literalPattern 2 ({0,2,3,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_30 :
    (sourceRow (planeIndex ({1,2,3,4} : Finset (Fin 6)))).2 = planeGapRow ({1,2,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_30"
  have hindex : planeIndex ({1,2,3,4} : Finset (Fin 6)) = (62 : Fin 96) := by rfl
  rw [hindex, row_coeff062]
  have hpattern : literalPattern 2 ({1,2,3,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_31 :
    (sourceRow (planeIndex ({0,1,2,3,4} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,3,4} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_31"
  have hindex : planeIndex ({0,1,2,3,4} : Finset (Fin 6)) = (63 : Fin 96) := by rfl
  rw [hindex, row_coeff063]
  have hpattern : literalPattern 2 ({0,1,2,3,4} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_32 :
    (sourceRow (planeIndex ({5} : Finset (Fin 6)))).2 = planeGapRow ({5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_32"
  have hindex : planeIndex ({5} : Finset (Fin 6)) = (64 : Fin 96) := by rfl
  rw [hindex, row_coeff064]
  have hpattern : literalPattern 2 ({5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_33 :
    (sourceRow (planeIndex ({0,5} : Finset (Fin 6)))).2 = planeGapRow ({0,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_33"
  have hindex : planeIndex ({0,5} : Finset (Fin 6)) = (65 : Fin 96) := by rfl
  rw [hindex, row_coeff065]
  have hpattern : literalPattern 2 ({0,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_34 :
    (sourceRow (planeIndex ({1,5} : Finset (Fin 6)))).2 = planeGapRow ({1,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_34"
  have hindex : planeIndex ({1,5} : Finset (Fin 6)) = (66 : Fin 96) := by rfl
  rw [hindex, row_coeff066]
  have hpattern : literalPattern 2 ({1,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_35 :
    (sourceRow (planeIndex ({0,1,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_35"
  have hindex : planeIndex ({0,1,5} : Finset (Fin 6)) = (67 : Fin 96) := by rfl
  rw [hindex, row_coeff067]
  have hpattern : literalPattern 2 ({0,1,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_36 :
    (sourceRow (planeIndex ({2,5} : Finset (Fin 6)))).2 = planeGapRow ({2,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_36"
  have hindex : planeIndex ({2,5} : Finset (Fin 6)) = (68 : Fin 96) := by rfl
  rw [hindex, row_coeff068]
  have hpattern : literalPattern 2 ({2,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_37 :
    (sourceRow (planeIndex ({0,2,5} : Finset (Fin 6)))).2 = planeGapRow ({0,2,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_37"
  have hindex : planeIndex ({0,2,5} : Finset (Fin 6)) = (69 : Fin 96) := by rfl
  rw [hindex, row_coeff069]
  have hpattern : literalPattern 2 ({0,2,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_38 :
    (sourceRow (planeIndex ({1,2,5} : Finset (Fin 6)))).2 = planeGapRow ({1,2,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_38"
  have hindex : planeIndex ({1,2,5} : Finset (Fin 6)) = (70 : Fin 96) := by rfl
  rw [hindex, row_coeff070]
  have hpattern : literalPattern 2 ({1,2,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_39 :
    (sourceRow (planeIndex ({0,1,2,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_39"
  have hindex : planeIndex ({0,1,2,5} : Finset (Fin 6)) = (71 : Fin 96) := by rfl
  rw [hindex, row_coeff071]
  have hpattern : literalPattern 2 ({0,1,2,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_40 :
    (sourceRow (planeIndex ({3,5} : Finset (Fin 6)))).2 = planeGapRow ({3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_40"
  have hindex : planeIndex ({3,5} : Finset (Fin 6)) = (72 : Fin 96) := by rfl
  rw [hindex, row_coeff072]
  have hpattern : literalPattern 2 ({3,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_41 :
    (sourceRow (planeIndex ({0,3,5} : Finset (Fin 6)))).2 = planeGapRow ({0,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_41"
  have hindex : planeIndex ({0,3,5} : Finset (Fin 6)) = (73 : Fin 96) := by rfl
  rw [hindex, row_coeff073]
  have hpattern : literalPattern 2 ({0,3,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_42 :
    (sourceRow (planeIndex ({1,3,5} : Finset (Fin 6)))).2 = planeGapRow ({1,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_42"
  have hindex : planeIndex ({1,3,5} : Finset (Fin 6)) = (74 : Fin 96) := by rfl
  rw [hindex, row_coeff074]
  have hpattern : literalPattern 2 ({1,3,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_43 :
    (sourceRow (planeIndex ({0,1,3,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_43"
  have hindex : planeIndex ({0,1,3,5} : Finset (Fin 6)) = (75 : Fin 96) := by rfl
  rw [hindex, row_coeff075]
  have hpattern : literalPattern 2 ({0,1,3,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_44 :
    (sourceRow (planeIndex ({2,3,5} : Finset (Fin 6)))).2 = planeGapRow ({2,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_44"
  have hindex : planeIndex ({2,3,5} : Finset (Fin 6)) = (76 : Fin 96) := by rfl
  rw [hindex, row_coeff076]
  have hpattern : literalPattern 2 ({2,3,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_45 :
    (sourceRow (planeIndex ({0,2,3,5} : Finset (Fin 6)))).2 = planeGapRow ({0,2,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_45"
  have hindex : planeIndex ({0,2,3,5} : Finset (Fin 6)) = (77 : Fin 96) := by rfl
  rw [hindex, row_coeff077]
  have hpattern : literalPattern 2 ({0,2,3,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_46 :
    (sourceRow (planeIndex ({1,2,3,5} : Finset (Fin 6)))).2 = planeGapRow ({1,2,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_46"
  have hindex : planeIndex ({1,2,3,5} : Finset (Fin 6)) = (78 : Fin 96) := by rfl
  rw [hindex, row_coeff078]
  have hpattern : literalPattern 2 ({1,2,3,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_47 :
    (sourceRow (planeIndex ({0,1,2,3,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,3,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_47"
  have hindex : planeIndex ({0,1,2,3,5} : Finset (Fin 6)) = (79 : Fin 96) := by rfl
  rw [hindex, row_coeff079]
  have hpattern : literalPattern 2 ({0,1,2,3,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_48 :
    (sourceRow (planeIndex ({4,5} : Finset (Fin 6)))).2 = planeGapRow ({4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_48"
  have hindex : planeIndex ({4,5} : Finset (Fin 6)) = (80 : Fin 96) := by rfl
  rw [hindex, row_coeff080]
  have hpattern : literalPattern 2 ({4,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_49 :
    (sourceRow (planeIndex ({0,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_49"
  have hindex : planeIndex ({0,4,5} : Finset (Fin 6)) = (81 : Fin 96) := by rfl
  rw [hindex, row_coeff081]
  have hpattern : literalPattern 2 ({0,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_50 :
    (sourceRow (planeIndex ({1,4,5} : Finset (Fin 6)))).2 = planeGapRow ({1,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_50"
  have hindex : planeIndex ({1,4,5} : Finset (Fin 6)) = (82 : Fin 96) := by rfl
  rw [hindex, row_coeff082]
  have hpattern : literalPattern 2 ({1,4,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_51 :
    (sourceRow (planeIndex ({0,1,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_51"
  have hindex : planeIndex ({0,1,4,5} : Finset (Fin 6)) = (83 : Fin 96) := by rfl
  rw [hindex, row_coeff083]
  have hpattern : literalPattern 2 ({0,1,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_52 :
    (sourceRow (planeIndex ({2,4,5} : Finset (Fin 6)))).2 = planeGapRow ({2,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_52"
  have hindex : planeIndex ({2,4,5} : Finset (Fin 6)) = (84 : Fin 96) := by rfl
  rw [hindex, row_coeff084]
  have hpattern : literalPattern 2 ({2,4,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_53 :
    (sourceRow (planeIndex ({0,2,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,2,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_53"
  have hindex : planeIndex ({0,2,4,5} : Finset (Fin 6)) = (85 : Fin 96) := by rfl
  rw [hindex, row_coeff085]
  have hpattern : literalPattern 2 ({0,2,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_54 :
    (sourceRow (planeIndex ({1,2,4,5} : Finset (Fin 6)))).2 = planeGapRow ({1,2,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_54"
  have hindex : planeIndex ({1,2,4,5} : Finset (Fin 6)) = (86 : Fin 96) := by rfl
  rw [hindex, row_coeff086]
  have hpattern : literalPattern 2 ({1,2,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_55 :
    (sourceRow (planeIndex ({0,1,2,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_55"
  have hindex : planeIndex ({0,1,2,4,5} : Finset (Fin 6)) = (87 : Fin 96) := by rfl
  rw [hindex, row_coeff087]
  have hpattern : literalPattern 2 ({0,1,2,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_56 :
    (sourceRow (planeIndex ({3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_56"
  have hindex : planeIndex ({3,4,5} : Finset (Fin 6)) = (88 : Fin 96) := by rfl
  rw [hindex, row_coeff088]
  have hpattern : literalPattern 2 ({3,4,5} : Finset (Fin 6)) = false := by decide
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

private theorem plane_row_57 :
    (sourceRow (planeIndex ({0,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_57"
  have hindex : planeIndex ({0,3,4,5} : Finset (Fin 6)) = (89 : Fin 96) := by rfl
  rw [hindex, row_coeff089]
  have hpattern : literalPattern 2 ({0,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_58 :
    (sourceRow (planeIndex ({1,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({1,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_58"
  have hindex : planeIndex ({1,3,4,5} : Finset (Fin 6)) = (90 : Fin 96) := by rfl
  rw [hindex, row_coeff090]
  have hpattern : literalPattern 2 ({1,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_59 :
    (sourceRow (planeIndex ({0,1,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_59"
  have hindex : planeIndex ({0,1,3,4,5} : Finset (Fin 6)) = (91 : Fin 96) := by rfl
  rw [hindex, row_coeff091]
  have hpattern : literalPattern 2 ({0,1,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_60 :
    (sourceRow (planeIndex ({2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({2,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_60"
  have hindex : planeIndex ({2,3,4,5} : Finset (Fin 6)) = (92 : Fin 96) := by rfl
  rw [hindex, row_coeff092]
  have hpattern : literalPattern 2 ({2,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_61 :
    (sourceRow (planeIndex ({0,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,2,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_61"
  have hindex : planeIndex ({0,2,3,4,5} : Finset (Fin 6)) = (93 : Fin 96) := by rfl
  rw [hindex, row_coeff093]
  have hpattern : literalPattern 2 ({0,2,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_62 :
    (sourceRow (planeIndex ({1,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({1,2,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_62"
  have hindex : planeIndex ({1,2,3,4,5} : Finset (Fin 6)) = (94 : Fin 96) := by rfl
  rw [hindex, row_coeff094]
  have hpattern : literalPattern 2 ({1,2,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_63 :
    (sourceRow (planeIndex ({0,1,2,3,4,5} : Finset (Fin 6)))).2 = planeGapRow ({0,1,2,3,4,5} : Finset (Fin 6)) := by
  trace "CELL2_PROGRESS plane_row_63"
  have hindex : planeIndex ({0,1,2,3,4,5} : Finset (Fin 6)) = (95 : Fin 96) := by rfl
  rw [hindex, row_coeff095]
  have hpattern : literalPattern 2 ({0,1,2,3,4,5} : Finset (Fin 6)) = true := by decide
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

private theorem plane_row_exact :
    ∀ I : Finset (Fin 6), I ≠ ∅ → I ≠ winner6 →
      (sourceRow (planeIndex I)).2 = planeGapRow I := by
  trace "CELL2_PROGRESS plane_row_exact"
  intro I hne hw
  fin_cases I
  · exact (hne (by decide)).elim
  · exact plane_row_01
  · exact plane_row_02
  · exact plane_row_03
  · exact plane_row_04
  · exact plane_row_05
  · exact (hw (by decide)).elim
  · exact plane_row_07
  · exact plane_row_08
  · exact plane_row_09
  · exact plane_row_10
  · exact plane_row_11
  · exact plane_row_12
  · exact plane_row_13
  · exact plane_row_14
  · exact plane_row_15
  · exact plane_row_16
  · exact plane_row_17
  · exact plane_row_18
  · exact plane_row_19
  · exact plane_row_20
  · exact plane_row_21
  · exact plane_row_22
  · exact plane_row_23
  · exact plane_row_24
  · exact plane_row_25
  · exact plane_row_26
  · exact plane_row_27
  · exact plane_row_28
  · exact plane_row_29
  · exact plane_row_30
  · exact plane_row_31
  · exact plane_row_32
  · exact plane_row_33
  · exact plane_row_34
  · exact plane_row_35
  · exact plane_row_36
  · exact plane_row_37
  · exact plane_row_38
  · exact plane_row_39
  · exact plane_row_40
  · exact plane_row_41
  · exact plane_row_42
  · exact plane_row_43
  · exact plane_row_44
  · exact plane_row_45
  · exact plane_row_46
  · exact plane_row_47
  · exact plane_row_48
  · exact plane_row_49
  · exact plane_row_50
  · exact plane_row_51
  · exact plane_row_52
  · exact plane_row_53
  · exact plane_row_54
  · exact plane_row_55
  · exact plane_row_56
  · exact plane_row_57
  · exact plane_row_58
  · exact plane_row_59
  · exact plane_row_60
  · exact plane_row_61
  · exact plane_row_62
  · exact plane_row_63

private theorem plane_gap_eval (I : Finset (Fin 6)) (t : Point8) :
    evalRow (planeGapRow I) t =
      R t - chosenOldPlane (literalPattern 2) t I := by
  trace "CELL2_PROGRESS plane_gap_eval"
  fin_cases I
  · change evalRow (planeGapRow (∅ : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t (∅ : Finset (Fin 6))
    have hp : literalPattern 2 (∅ : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0} : Finset (Fin 6))
    have hp : literalPattern 2 ({0} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1} : Finset (Fin 6))
    have hp : literalPattern 2 ({1} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2} : Finset (Fin 6))
    have hp : literalPattern 2 ({2} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({3} : Finset (Fin 6))
    have hp : literalPattern 2 ({3} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,3} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,3} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,3} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,3} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,3} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,3} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,3} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,3} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,3} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({4} : Finset (Fin 6))
    have hp : literalPattern 2 ({4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({3,4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,3,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,3,4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,3,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,3,4} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,3,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,3,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,3,4} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,3,4} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,3,4} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({5} : Finset (Fin 6))
    have hp : literalPattern 2 ({5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({3,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,3,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,3,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,3,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,3,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,3,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,3,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,3,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,3,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,3,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({4,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,4,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,4,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({3,4,5} : Finset (Fin 6)) = false := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({2,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({2,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,2,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,2,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({1,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({1,2,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({1,2,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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
  · change evalRow (planeGapRow ({0,1,2,3,4,5} : Finset (Fin 6))) t =
      P2OriginalAscendingEighthCapDictionary.R t -
        chosenOldPlane (literalPattern 2) t ({0,1,2,3,4,5} : Finset (Fin 6))
    have hp : literalPattern 2 ({0,1,2,3,4,5} : Finset (Fin 6)) = true := by decide
    simp only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      planeGapRow, hp, chosenOldPlane, subsetSum,
      P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d,
      VariableEnvelope.A, VariableEnvelope.C,
      Finset.exists_mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.notMem_empty, Finset.exists_mem_empty_iff, exists_eq_left, exists_false,
      or_and_right, exists_or, false_and, and_false, true_and, and_true]
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

/-- The 62 recorded planes and the one omitted equality provide every
one of the 63 nonempty old-subset tests. -/
theorem literalRows_old_planes (t : Point8) (h : literalRows t) :
    OldPlaneRows (literalPattern 2) t := by
  trace "CELL2_PROGRESS literalRows_old_planes"
  intro I hI
  have hne : I ≠ ∅ := by simpa [oldMasks] using hI
  by_cases hw : I = winner6
  · subst I
    have hp : literalPattern 2 winner6 = true := by decide
    simpa only [chosenOldPlane, hp, if_true,
      P2OriginalAscendingEighthCapDictionary.winner6_sum,
      P2OriginalAscendingEighthCapDictionary.R] using
      (le_refl (VariableEnvelope.C (P2OriginalAscendingEighthCapDictionary.d t)))
  · have hr := h (planeIndex I)
    change 0 < evalRow (sourceRow (planeIndex I)).2 t at hr
    rw [plane_row_exact I hne hw] at hr
    rw [plane_gap_eval] at hr
    linarith

private theorem literalRows_order (t : Point8) (h : literalRows t) : StrictAnti t := by
  trace "CELL2_PROGRESS literalRows_order"
  have h01 := h (3 : Fin 96)
  change 0 < evalRow (sourceRow (3 : Fin 96)).2 t at h01
  rw [row_coeff003] at h01
  have h12 := h (4 : Fin 96)
  change 0 < evalRow (sourceRow (4 : Fin 96)).2 t at h12
  rw [row_coeff004] at h12
  have h23 := h (5 : Fin 96)
  change 0 < evalRow (sourceRow (5 : Fin 96)).2 t at h23
  rw [row_coeff005] at h23
  have h34 := h (6 : Fin 96)
  change 0 < evalRow (sourceRow (6 : Fin 96)).2 t at h34
  rw [row_coeff006] at h34
  have h45 := h (7 : Fin 96)
  change 0 < evalRow (sourceRow (7 : Fin 96)).2 t at h45
  rw [row_coeff007] at h45
  have h56 := h (8 : Fin 96)
  change 0 < evalRow (sourceRow (8 : Fin 96)).2 t at h56
  rw [row_coeff008] at h56
  have h67 := h (9 : Fin 96)
  change 0 < evalRow (sourceRow (9 : Fin 96)).2 t at h67
  rw [row_coeff009] at h67
  norm_num [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Fin.succ, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty, Fin.ext_iff, Matrix.vecCons, Fin.cons, -Matrix.Fin.cons_vecCons, -Matrix.Fin.cons_vecEmpty] at h01 h12 h23 h34 h45 h56 h67
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

private theorem literalRows_ascending (t : Point8) (h : literalRows t) :
    A (selectedSum t) < C (selectedSum t) := by
  trace "CELL2_PROGRESS literalRows_ascending"
  have hr := h (17 : Fin 96)
  change 0 < evalRow (sourceRow (17 : Fin 96)).2 t at hr
  rw [row_coeff017] at hr
  norm_num [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Fin.succ, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty, Fin.ext_iff, Matrix.vecCons, Fin.cons, -Matrix.Fin.cons_vecCons, -Matrix.Fin.cons_vecEmpty] at hr
  dsimp [VariableEnvelope.A, VariableEnvelope.C, P2OriginalAscendingEighthCapDictionary.selectedSum]
  linarith

private def fullIndex : Fin 8 → Fin 96 := ![18,19,21,23,25,27,29,31]

private theorem full_square_row (t : Point8) (j : Fin 8)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (sourceRow (fullIndex j)).2 t = M t - fullSquare t j := by
  trace "CELL2_PROGRESS full_square_row"
  rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
  fin_cases j
  · change evalRow (sourceRow (18 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (0 : Fin 8)
    rw [row_coeff018]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (19 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (1 : Fin 8)
    rw [row_coeff019]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (21 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (2 : Fin 8)
    rw [row_coeff021]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (23 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (3 : Fin 8)
    rw [row_coeff023]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (25 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (4 : Fin 8)
    rw [row_coeff025]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (27 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (5 : Fin 8)
    rw [row_coeff027]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (29 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (6 : Fin 8)
    rw [row_coeff029]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (31 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - fullSquare t (7 : Fin 8)
    rw [row_coeff031]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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

private theorem selected_square_row (t : Point8) (j : Fin 8)
    (hj0 : 0 < j) (hj7 : j < 7)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (sourceRow ⟨18 + 2 * j.val, by omega⟩).2 t =
      M t - selectedRemainingSquare t j := by
  trace "CELL2_PROGRESS selected_square_row"
  rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
  fin_cases j
  · norm_num [Fin.lt_def] at hj0
  · change evalRow (sourceRow (20 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (1 : Fin 8)
    rw [row_coeff020]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (22 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (2 : Fin 8)
    rw [row_coeff022]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (24 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (3 : Fin 8)
    rw [row_coeff024]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (26 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (4 : Fin 8)
    rw [row_coeff026]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (28 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (5 : Fin 8)
    rw [row_coeff028]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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
  · change evalRow (sourceRow (30 : Fin 96)).2 t =
      VariableEnvelope.A (P2OriginalAscendingEighthCapDictionary.selectedSum t) -
        P2OriginalAscendingEighthCapDictionary.eta - selectedRemainingSquare t (6 : Fin 8)
    rw [row_coeff030]
    norm_num only [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, P2OriginalAscendingEighthCapDictionary.prefixSum,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
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

/-- Complete finite row-to-semantics bridge for original cell 2.
The inherited cap is deliberately absent: it is determined by its own
actual causal tree, rather than by the navigation's comparison R. -/
theorem literalRows_cellGuard (t : Point8) (h : literalRows t) :
    CellGuard (literalPattern 2) t := by
  trace "CELL2_PROGRESS literalRows_cellGuard"
  have h0 := h (0 : Fin 96)
  change 0 < evalRow (sourceRow (0 : Fin 96)).2 t at h0
  rw [row_coeff000] at h0
  have h1 := h (1 : Fin 96)
  change 0 < evalRow (sourceRow (1 : Fin 96)).2 t at h1
  rw [row_coeff001] at h1
  have h2 := h (2 : Fin 96)
  change 0 < evalRow (sourceRow (2 : Fin 96)).2 t at h2
  rw [row_coeff002] at h2
  have h10 := h (10 : Fin 96)
  change 0 < evalRow (sourceRow (10 : Fin 96)).2 t at h10
  rw [row_coeff010] at h10
  have h11 := h (11 : Fin 96)
  change 0 < evalRow (sourceRow (11 : Fin 96)).2 t at h11
  rw [row_coeff011] at h11
  have h12 := h (12 : Fin 96)
  change 0 < evalRow (sourceRow (12 : Fin 96)).2 t at h12
  rw [row_coeff012] at h12
  have h13 := h (13 : Fin 96)
  change 0 < evalRow (sourceRow (13 : Fin 96)).2 t at h13
  rw [row_coeff013] at h13
  have h15 := h (15 : Fin 96)
  change 0 < evalRow (sourceRow (15 : Fin 96)).2 t at h15
  rw [row_coeff015] at h15
  have h32 := h (32 : Fin 96)
  change 0 < evalRow (sourceRow (32 : Fin 96)).2 t at h32
  rw [row_coeff032] at h32
  have h33 := h (33 : Fin 96)
  change 0 < evalRow (sourceRow (33 : Fin 96)).2 t at h33
  rw [row_coeff033] at h33
  norm_num [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ, Fin.succ, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty, Fin.ext_iff, Matrix.vecCons, Fin.cons, -Matrix.Fin.cons_vecCons, -Matrix.Fin.cons_vecEmpty] at h0 h1 h2 h10 h11 h12 h13 h15 h32 h33
  have ha := literalRows_ascending t h
  have hc := literalRows_core t h
  have hsemantic := cell0_affine_semantic t hc
  refine {
    order := literalRows_order t h
    last_pos := by linarith
    largest := by dsimp [VariableEnvelope.mu]; linarith
    third_activation := by linarith
    compact_cutoff := by linarith
    first_history := ?_
    history3 := ?_
    history5 := ?_
    history7 := ?_
    old_descending := hsemantic.1
    old_W := ?_
    old_planes := literalRows_old_planes t h
    new_ascending := ha
    improvement := hsemantic.2
    full_squares := ?_
    selected_squares := ?_
    old_residual := ?_
    new_residual := ?_ }
  · dsimp [P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · norm_num [oddCube, P2OriginalAscendingEighthCapDictionary.prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · dsimp [VariableEnvelope.B, VariableEnvelope.cap, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · intro j
    have hr := h (fullIndex j)
    change 0 < evalRow (sourceRow (fullIndex j)).2 t at hr
    rw [full_square_row t j ha] at hr
    linarith
  · intro j hj0 hj7
    have hr := h (⟨18 + 2 * j.val, by omega⟩ : Fin 96)
    change 0 < evalRow (sourceRow (⟨18 + 2 * j.val, by omega⟩ : Fin 96)).2 t at hr
    rw [selected_square_row t j hj0 hj7 ha] at hr
    linarith
  · norm_num [P2OriginalAscendingEighthCapDictionary.S, Fin.sum_univ_succ, Fin.succ, Fin.lt_def, Fin.coe_ofNat_eq_mod, P2OriginalAscendingEighthCapDictionary.R, P2OriginalAscendingEighthCapDictionary.d, VariableEnvelope.C]; linarith
  · rw [P2OriginalAscendingEighthCapDictionary.M, min_eq_left ha.le]
    norm_num [P2OriginalAscendingEighthCapDictionary.S, Fin.sum_univ_succ, VariableEnvelope.A, P2OriginalAscendingEighthCapDictionary.selectedSum, P2OriginalAscendingEighthCapDictionary.eta, Fin.succ, Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty, Fin.ext_iff, Matrix.vecCons, Fin.cons, -Matrix.Fin.cons_vecCons, -Matrix.Fin.cons_vecEmpty]
    linarith


end
end ImbalancedChen.P4AOriginalAscendingCell2Affine
