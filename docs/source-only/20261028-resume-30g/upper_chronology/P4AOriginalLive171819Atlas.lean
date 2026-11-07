import ImbalancedChen.P4AOriginalRemainingAscendingSlots1619

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
LIVE original slots17/18/19 source atlas: fifteen descending129 cells,
thirteen winner9 unequal cells plus the two actual winner50 branches,
and thirteen ascending138 cells. Literal common rows and original branch
patterns, not ascending-domain exclusions, define these domains.
-/
namespace ImbalancedChen.P4AOriginalLive171819Atlas
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
abbrev Point := Fin 8 → ℝ
abbrev Affine := Fin 9 → ℚ
abbrev eval := P4AOriginalSeed7Unequal15Literal.evalAffine

def common17 : Fin 34 → String × (Fin 9 → ℚ) :=
  ![
    ("largest below mu", ![25/128,-1,0,0,0,0,0,0,0]),
    ("third original cutoff", ![-1/100,0,0,1,0,0,0,0,0]),
    ("eighth compact cutoff", ![-53/13824,0,0,0,0,0,0,0,1]),
    ("order 1", ![0,1,-1,0,0,0,0,0,0]),
    ("order 2", ![0,0,1,-1,0,0,0,0,0]),
    ("order 3", ![0,0,0,1,-1,0,0,0,0]),
    ("order 4", ![0,0,0,0,1,-1,0,0,0]),
    ("order 5", ![0,0,0,0,0,1,-1,0,0]),
    ("order 6", ![0,0,0,0,0,0,1,-1,0]),
    ("order 7", ![0,0,0,0,0,0,0,1,-1]),
    ("old first history", ![57/64,-3,-3/2,-3/2,0,0,0,0,0]),
    ("old H3 below L3", ![57/64,-1,-5/2,-9/2,0,0,0,0,0]),
    ("old H5 below L3", ![57/64,-1,-5/2,-5/2,-1,-3,0,0,0]),
    ("old H7 below L3", ![57/64,-1,-5/2,-5/2,-1,-1,-1,-3,0]),
    ("old winner6 descending below ascending", ![-25/64,0,2,2,0,0,0,0,0]),
    ("old W below R6", ![75/256,0,-3/2,-9/8,0,0,0,0,0]),
    ("new cap improvement", ![-1/1000000,-3/2,3/2,3/2,0,0,0,0,-3/2]),
    ("new ascending license buffered", ![-25/64,2,0,0,0,0,0,0,2]),
    ("full square 1", ![13916/15625,-7/2,0,0,0,0,0,0,-3/2]),
    ("full square 2", ![13916/15625,-5/2,-2,0,0,0,0,0,-3/2]),
    ("selected129 remaining square 2", ![13916/15625,-5/2,-2,0,0,0,0,0,-5/2]),
    ("full square 3", ![13916/15625,-5/2,-1,-2,0,0,0,0,-3/2]),
    ("selected129 remaining square 3", ![13916/15625,-5/2,-1,-2,0,0,0,0,-5/2]),
    ("full square 4", ![13916/15625,-5/2,-1,-1,-2,0,0,0,-3/2]),
    ("selected129 remaining square 4", ![13916/15625,-5/2,-1,-1,-2,0,0,0,-5/2]),
    ("full square 5", ![13916/15625,-5/2,-1,-1,-1,-2,0,0,-3/2]),
    ("selected129 remaining square 5", ![13916/15625,-5/2,-1,-1,-1,-2,0,0,-5/2]),
    ("full square 6", ![13916/15625,-5/2,-1,-1,-1,-1,-2,0,-3/2]),
    ("selected129 remaining square 6", ![13916/15625,-5/2,-1,-1,-1,-1,-2,0,-5/2]),
    ("full square 7", ![13916/15625,-5/2,-1,-1,-1,-1,-1,-2,-3/2]),
    ("selected129 remaining square 7", ![13916/15625,-5/2,-1,-1,-1,-1,-1,-2,-5/2]),
    ("full square 8", ![13916/15625,-5/2,-1,-1,-1,-1,-1,-1,-7/2]),
    ("old residual above t8", ![57/64,-1,-5/2,-5/2,-1,-1,-1,-1,-2]),
    ("new residual below3t8", ![-13916/15625,5/2,1,1,1,1,1,1,11/2])
  ]

def common19 : Fin 35 → String × (Fin 9 → ℚ) :=
  ![
    ("largest below mu", ![25/128,-1,0,0,0,0,0,0,0]),
    ("third original cutoff", ![-1/100,0,0,1,0,0,0,0,0]),
    ("eighth compact cutoff", ![-53/13824,0,0,0,0,0,0,0,1]),
    ("order 1", ![0,1,-1,0,0,0,0,0,0]),
    ("order 2", ![0,0,1,-1,0,0,0,0,0]),
    ("order 3", ![0,0,0,1,-1,0,0,0,0]),
    ("order 4", ![0,0,0,0,1,-1,0,0,0]),
    ("order 5", ![0,0,0,0,0,1,-1,0,0]),
    ("order 6", ![0,0,0,0,0,0,1,-1,0]),
    ("order 7", ![0,0,0,0,0,0,0,1,-1]),
    ("first history below B3", ![1/2,-3,1/2,1/2,0,0,0,0,0]),
    ("H3 below B3", ![1/2,-1,-1/2,-5/2,0,0,0,0,0]),
    ("H5 below B3", ![1/2,-1,-1/2,-1/2,-1,-3,0,0,0]),
    ("H7 below B3", ![1/2,-1,-1/2,-1/2,-1,-1,-1,-3,0]),
    ("R6 above B3", ![0,1/2,-1/2,-1/2,1/2,0,0,0,0]),
    ("winner9 ascending half", ![25/64,-2,0,0,-2,0,0,0,0]),
    ("W below R6", ![-25/256,1/2,0,3/8,1/2,0,0,0,0]),
    ("new region s23 below mu", ![25/128,0,-1,-1,0,0,0,0,0]),
    ("new cap improvement", ![-1/1000000,-1/2,1/2,0,0,0,0,0,1/2]),
    ("new descending license buffered", ![25/64,0,-2,0,-2,0,0,0,-2]),
    ("full square 1", ![499999/1000000,-2,1/2,0,1/2,0,0,0,1/2]),
    ("selected138 remaining square 1", ![499999/1000000,-2,-1/2,0,-1/2,0,0,0,-1/2]),
    ("full square 2", ![499999/1000000,-1,-3/2,0,1/2,0,0,0,1/2]),
    ("full square 3", ![499999/1000000,-1,-1/2,-2,1/2,0,0,0,1/2]),
    ("selected138 remaining square 3", ![499999/1000000,-1,-1/2,-2,-1/2,0,0,0,-1/2]),
    ("full square 4", ![499999/1000000,-1,-1/2,-1,-3/2,0,0,0,1/2]),
    ("full square 5", ![499999/1000000,-1,-1/2,-1,-1/2,-2,0,0,1/2]),
    ("selected138 remaining square 5", ![499999/1000000,-1,-1/2,-1,-1/2,-2,0,0,-1/2]),
    ("full square 6", ![499999/1000000,-1,-1/2,-1,-1/2,-1,-2,0,1/2]),
    ("selected138 remaining square 6", ![499999/1000000,-1,-1/2,-1,-1/2,-1,-2,0,-1/2]),
    ("full square 7", ![499999/1000000,-1,-1/2,-1,-1/2,-1,-1,-2,1/2]),
    ("selected138 remaining square 7", ![499999/1000000,-1,-1/2,-1,-1/2,-1,-1,-2,-1/2]),
    ("full square 8", ![499999/1000000,-1,-1/2,-1,-1/2,-1,-1,-1,-3/2]),
    ("R6 residual above r", ![1/2,-1/2,-1,-1,-1/2,-1,-1,-1,-2]),
    ("M residual below3r", ![-499999/1000000,1,1/2,1,1/2,1,1,1,7/2])
  ]

/-- The exact old branch is an original navigation assignment. -/
def gap17 (i : Fin 15) (m : ℕ) : Affine := fun j =>
  if j = 0 then
    if m ∈ OriginalDescendingFifteenCellOwnership.leftMasks i then 25/64 else 0
  else
    (if j.val = 2 ∨ j.val = 3 then (-3/2 : ℚ) else 0) -
    (if m.testBit (j.val-1) then
      if m ∈ OriginalDescendingFifteenCellOwnership.leftMasks i then (1/2 : ℚ) else -3/2
     else 0)

def gap19 (i : Fin 13) (m : ℕ) : Affine := fun j =>
  if j = 0 then
    if m ∈ OriginalAscendingThirteenCellOwnership.leftMasks i then 0 else -25/64
  else
    (if j.val = 1 ∨ j.val = 4 then (1/2 : ℚ) else 0) -
    (if m.testBit (j.val-1) then
      if m ∈ OriginalAscendingThirteenCellOwnership.leftMasks i then (1/2 : ℚ) else -3/2
     else 0)

def mask17 (k : Fin 96) : ℕ := if k.val < 39 then k.val-33 else k.val-32
def mask19 (k : Fin 97) : ℕ := if k.val < 43 then k.val-34 else k.val-33

def rows17 (i : Fin 15) (k : Fin 96) : Affine :=
  if h : k.val < 34 then (common17 ⟨k.val,h⟩).2 else gap17 i (mask17 k)
def rows19 (i : Fin 13) (k : Fin 97) : Affine :=
  if h : k.val < 35 then (common19 ⟨k.val,h⟩).2 else gap19 i (mask19 k)

inductive LiveCell where
  | descending17 : Fin 15 → LiveCell
  | unequal18 : P4AOriginalSeed7Unequal15Literal.UnequalCell → LiveCell
  | ascending19 : Fin 13 → LiveCell
  deriving DecidableEq, Fintype

def rowCount : LiveCell → ℕ
  | .descending17 _ => 96
  | .unequal18 (.nine _) => 97
  | .unequal18 .fiftyAsc => 95
  | .unequal18 .fiftyDesc => 96
  | .ascending19 _ => 97

def rows : (c : LiveCell) → Fin (rowCount c) → Affine
  | .descending17 i => rows17 i
  | .unequal18 (.nine i) => fun k => (P4AOriginalSeed7Unequal15Literal.nineRows i k).2
  | .unequal18 .fiftyAsc => fun k => (P4AOriginalSeed7Unequal15Literal.fiftyAscRows k).2
  | .unequal18 .fiftyDesc => fun k => (P4AOriginalSeed7Unequal15Literal.fiftyDescRows k).2
  | .ascending19 i => rows19 i

def sourceRows (c : LiveCell) (t : Point) : Prop := ∀ k, 0 < eval (rows c k) t

def originalSource : LiveCell → Point → Prop
  | .descending17 i, t => OriginalDescendingFifteenCellOwnership.StrictRows i t
  | .unequal18 u, t => P4AOriginalSeed7Unequal15Literal.unequalSourceRows u t
  | .ascending19 i, t => OriginalAscendingThirteenCellOwnership.StrictRows i t

def oldCap : LiveCell → Point → ℝ
  | .descending17 _, t => P2OriginalDescendingEighthLogSemantics.oldRaw t
  | .unequal18 u, t => P4AOriginalSeed7Unequal15Literal.oldCap u t
  | .ascending19 _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t

def newCap : LiveCell → Point → ℝ
  | .descending17 _, t => P2OriginalDescendingEighthLogSemantics.newCap t
  | .unequal18 u, t => P4AOriginalSeed7Unequal15Literal.newCap u t
  | .ascending19 _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.newCap t

def selectedMask : LiveCell → Finset (Fin 8)
  | .descending17 _ => {0,7}
  | .unequal18 (.nine _) => {1,3,7}
  | .unequal18 .fiftyAsc => {3,4,5,7}
  | .unequal18 .fiftyDesc => {1,2,7}
  | .ascending19 _ => {1,3,7}

/-- Original order 15+15+13 is retained, including both winner50 branches. -/
def sourceIndex : LiveCell → Fin 87
  | .descending17 i => ⟨15+i.val, by omega⟩
  | .unequal18 (.nine i) => ⟨30+i.val, by omega⟩
  | .unequal18 .fiftyAsc => 43
  | .unequal18 .fiftyDesc => 44
  | .ascending19 i => ⟨45+i.val, by omega⟩

theorem forty_three_sources : Fintype.card LiveCell = 43 := by decide

theorem sourceIndex_injective : Function.Injective sourceIndex := by decide

theorem sourceIndex_live (c : LiveCell) : 15 ≤ (sourceIndex c).val ∧ (sourceIndex c).val < 58 := by
  cases c with
  | descending17 i => simp [sourceIndex]; omega
  | unequal18 u => cases u <;> simp [sourceIndex] <;> omega
  | ascending19 i => simp [sourceIndex]; omega

private theorem gap17_eval (i : Fin 15) (m : Fin 64) (t : Point) :
    eval (gap17 i m.val) t = P2OriginalDescendingEighthLogSemantics.oldRaw t -
      OriginalDescendingFifteenCellOwnership.branchPlane i m.val t := by
  fin_cases m <;>
    simp [gap17, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
      OriginalDescendingFifteenCellOwnership.branchPlane,
      OriginalDescendingFifteenCellOwnership.subsetSum,
      OriginalDescendingFifteenCellOwnership.maskSlots,
      P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, A, C,
      Finset.sum_filter, Fin.sum_univ_succ] <;> split_ifs <;> ring

private theorem gap19_eval (i : Fin 13) (m : Fin 64) (t : Point) :
    eval (gap19 i m.val) t = P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t -
      OriginalAscendingThirteenCellOwnership.branchPlane i m.val t := by
  fin_cases m <;>
    simp [gap19, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
      OriginalAscendingThirteenCellOwnership.branchPlane,
      OriginalAscendingThirteenCellOwnership.subsetSum,
      OriginalAscendingThirteenCellOwnership.maskSlots,
      P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap, A, C,
      Finset.sum_filter, Fin.sum_univ_succ] <;> split_ifs <;> ring

private def plane17 (m : Fin 64) : Fin 96 :=
  ⟨if m.val < 6 then 33+m.val else 32+m.val, by split_ifs <;> omega⟩
private def plane19 (m : Fin 64) : Fin 97 :=
  ⟨if m.val < 9 then 34+m.val else 33+m.val, by split_ifs <;> omega⟩

private theorem row17_plane (i : Fin 15) (m : Fin 64) (hm : m ≠ 0) (hm6 : m ≠ 6) :
    rows17 i (plane17 m) = gap17 i m.val := by
  fin_cases m <;> norm_num [rows17, plane17, mask17] at hm hm6 ⊢
private theorem row19_plane (i : Fin 13) (m : Fin 64) (hm : m ≠ 0) (hm9 : m ≠ 9) :
    rows19 i (plane19 m) = gap19 i m.val := by
  fin_cases m <;> norm_num [rows19, plane19, mask19] at hm hm9 ⊢

private theorem source17_branches (i : Fin 15) (t : Point)
    (hs : sourceRows (.descending17 i) t) :
    ∀ m ∈ Finset.Icc 1 63, m ≠ 6 →
      OriginalDescendingFifteenCellOwnership.branchPlane i m t <
        P2OriginalDescendingEighthLogSemantics.oldRaw t := by
  intro m hm hm6
  have hb := Finset.mem_Icc.mp hm
  let mf : Fin 64 := ⟨m,by omega⟩
  have hr := hs (plane17 mf)
  change 0 < eval (rows17 i (plane17 mf)) t at hr
  rw [row17_plane i mf (by apply Fin.ne_of_val_ne; dsimp [mf]; omega)
    (by apply Fin.ne_of_val_ne; exact hm6), gap17_eval] at hr
  linarith

private theorem source19_branches (i : Fin 13) (t : Point)
    (hs : sourceRows (.ascending19 i) t) :
    ∀ m ∈ Finset.Icc 1 63, m ≠ 9 →
      OriginalAscendingThirteenCellOwnership.branchPlane i m t <
        P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t := by
  intro m hm hm9
  have hb := Finset.mem_Icc.mp hm
  let mf : Fin 64 := ⟨m,by omega⟩
  have hr := hs (plane19 mf)
  change 0 < eval (rows19 i (plane19 mf)) t at hr
  rw [row19_plane i mf (by apply Fin.ne_of_val_ne; dsimp [mf]; omega)
    (by apply Fin.ne_of_val_ne; exact hm9), gap19_eval] at hr
  linarith

private def full17 : Fin 8 → Fin 34 := ![18,19,21,23,25,27,29,31]
private def full19 : Fin 8 → Fin 35 := ![20,22,23,25,26,28,30,32]
private def comp19 : Fin 8 → Fin 35 := ![21,21,24,21,27,29,31,21]

private theorem full17_eval (t : Point) (j : Fin 8) :
    eval (common17 (full17 j)).2 t = P2OriginalDescendingEighthLogSemantics.newCap t -
      prefixSquareExpr t j := by
  fin_cases j <;> norm_num [common17, full17, eval,
    P4AOriginalSeed7Unequal15Literal.evalAffine, prefixSquareExpr,
    P2OriginalDescendingEighthLogSemantics.newCap,
    P2OriginalDescendingEighthLogSemantics.selectedSum,
    P2OriginalDescendingEighthLogSemantics.eta, A, C,
    Finset.sum_filter, Fin.sum_univ_succ] <;> ring

private theorem comp17_eval (t : Point) (j : Fin 8) (h0 : j ≠ 0) (h7 : j ≠ 7) :
    eval (common17 ⟨18+2*j.val,by omega⟩).2 t =
      P2OriginalDescendingEighthLogSemantics.newCap t -
        (P2OriginalDescendingEighthLogSemantics.selectedSum t +
          (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < j), t k) + 2*t j) := by
  fin_cases j <;> norm_num at h0 h7 ⊢ <;>
    norm_num [common17, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalDescendingEighthLogSemantics.newCap,
      P2OriginalDescendingEighthLogSemantics.selectedSum,
      P2OriginalDescendingEighthLogSemantics.eta, A, C,
      Finset.sum_filter, Fin.sum_univ_succ] <;> ring

private theorem full19_eval (t : Point) (j : Fin 8) :
    eval (common19 (full19 j)).2 t =
      P2OriginalThirdMinorantLogDictionarySourceOnly.newCap t - prefixSquareExpr t j := by
  fin_cases j <;> norm_num [common19, full19, eval,
    P4AOriginalSeed7Unequal15Literal.evalAffine, prefixSquareExpr,
    P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
    P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
    P2OriginalThirdMinorantLogDictionarySourceOnly.eta, A, C,
    Finset.sum_filter, Fin.sum_univ_succ] <;> ring

private theorem comp19_eval (t : Point) (j : Fin 8)
    (h1 : j ≠ 1) (h3 : j ≠ 3) (h7 : j ≠ 7) :
    eval (common19 (comp19 j)).2 t =
      P2OriginalThirdMinorantLogDictionarySourceOnly.newCap t -
        (P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum t +
          (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2*t j) := by
  fin_cases j <;> norm_num at h1 h3 h7 ⊢ <;>
    norm_num [common19, comp19, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
      P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
      P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
      P2OriginalThirdMinorantLogDictionarySourceOnly.eta, A, C,
      Finset.sum_filter, Fin.sum_univ_succ] <;> ring

/-- All original 96 descending rows, including every branch and both
families of physical squares, enter the actual live slot17 owner. -/
theorem source17_guard (i : Fin 15) (t : Point) (hs : sourceRows (.descending17 i) t) :
    OriginalDescendingFifteenCellOwnership.StrictRows i t := by
  have hc (k : Fin 34) : 0 < eval (common17 k).2 t := by
    simpa only [sourceRows, rows, rows17, dif_pos k.isLt] using hs ⟨k.val,by omega⟩
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  have h9 := hc 9
  have h10 := hc 10
  have h11 := hc 11
  have h12 := hc 12
  have h13 := hc 13
  have h14 := hc 14
  have h15 := hc 15
  have h16 := hc 16
  have h17 := hc 17
  have h32 := hc 32
  have h33 := hc 33
  norm_num [common17, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h32 h33
  refine {
    largest := by dsimp [mu]; linarith
    thirdFloor := by linarith
    lastFloor := by linarith
    order := ?_
    firstHistory := ?_
    thirdHistory := ?_
    fifthHistory := ?_
    seventhHistory := ?_
    oldWinner := ?_
    oldW := ?_
    improvement := ?_
    descending := ?_
    fullSquares := ?_
    complementSquares := ?_
    oldResidual := ?_
    terminal := ?_
    branches := source17_branches i t hs }
  · intro j; fin_cases j <;> norm_num <;> linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.history3,
      P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.history5,
      P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.history7,
      P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.d, mu]; linarith
  · dsimp [cap, P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d,
      P2OriginalDescendingEighthLogSemantics.newCap,
      P2OriginalDescendingEighthLogSemantics.selectedSum,
      P2OriginalDescendingEighthLogSemantics.eta, C]; linarith
  · dsimp [P2OriginalDescendingEighthLogSemantics.selectedSum, mu]; linarith
  · intro j
    have hr := hc (full17 j)
    rw [full17_eval] at hr
    linarith
  · intro j hj0 hj7
    have hr := hc (⟨18+2*j.val,by omega⟩ : Fin 34)
    rw [comp17_eval t j hj0 hj7] at hr
    linarith
  · norm_num [P2OriginalDescendingEighthLogSemantics.total,
      P2OriginalDescendingEighthLogSemantics.oldRaw,
      P2OriginalDescendingEighthLogSemantics.d, C, Fin.sum_univ_succ]; linarith
  · norm_num [P2OriginalDescendingEighthLogSemantics.total,
      P2OriginalDescendingEighthLogSemantics.newCap,
      P2OriginalDescendingEighthLogSemantics.selectedSum,
      P2OriginalDescendingEighthLogSemantics.eta, C, Fin.sum_univ_succ]; linarith

/-- All original 97 ascending-minorant rows enter the live slot19 owner;
the old third minorant remains distinct from its old rank6 comparison. -/
theorem source19_guard (i : Fin 13) (t : Point) (hs : sourceRows (.ascending19 i) t) :
    OriginalAscendingThirteenCellOwnership.StrictRows i t := by
  have hc (k : Fin 35) : 0 < eval (common19 k).2 t := by
    simpa only [sourceRows, rows, rows19, dif_pos k.isLt] using hs ⟨k.val,by omega⟩
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  have h5 := hc 5
  have h6 := hc 6
  have h7 := hc 7
  have h8 := hc 8
  have h9 := hc 9
  have h10 := hc 10
  have h11 := hc 11
  have h12 := hc 12
  have h13 := hc 13
  have h14 := hc 14
  have h15 := hc 15
  have h16 := hc 16
  have h17 := hc 17
  have h18 := hc 18
  have h19 := hc 19
  have h33 := hc 33
  have h34 := hc 34
  norm_num [common19, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h33 h34
  refine {
    largest := by dsimp [mu]; linarith
    thirdFloor := by linarith
    lastFloor := by linarith
    order := ?_
    firstHistory := ?_
    thirdHistory := ?_
    fifthHistory := ?_
    seventhHistory := ?_
    aboveThird := ?_
    oldWinner := ?_
    oldW := ?_
    ascendingThird := ?_
    improvement := ?_
    ascendingNew := ?_
    fullSquares := ?_
    complementSquares := ?_
    oldResidual := ?_
    terminal := ?_
    branches := source19_branches i t hs }
  all_goals try { dsimp [P2OriginalThirdMinorantLogDictionarySourceOnly.thirdMinorant,
    P2OriginalThirdMinorantLogDictionarySourceOnly.history3,
    P2OriginalThirdMinorantLogDictionarySourceOnly.history5,
    P2OriginalThirdMinorantLogDictionarySourceOnly.history7,
    P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
    P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
    P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
    P2OriginalThirdMinorantLogDictionarySourceOnly.eta, cap, mu, A]; linarith }
  · intro j; fin_cases j <;> norm_num <;> linarith
  · intro j
    have hr := hc (full19 j)
    rw [full19_eval] at hr
    linarith
  · intro j hj1 hj3 hj7
    have hr := hc (comp19 j)
    rw [comp19_eval t j hj1 hj3 hj7] at hr
    linarith
  · norm_num [P2OriginalThirdMinorantLogDictionarySourceOnly.total,
      P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap, A,
      Fin.sum_univ_succ]; linarith
  · norm_num [P2OriginalThirdMinorantLogDictionarySourceOnly.total,
      P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
      P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
      P2OriginalThirdMinorantLogDictionarySourceOnly.eta, A, Fin.sum_univ_succ]; linarith

/-- Each literal live atlas membership supplies its own original source
predicate, rather than exclusion from another source domain. -/
theorem source_original (c : LiveCell) (t : Point) (hs : sourceRows c t) : originalSource c t := by
  cases c with
  | descending17 i => exact source17_guard i t hs
  | unequal18 u => cases u <;> exact hs
  | ascending19 i => exact source19_guard i t hs

/-- The source-tag dictionary preserves the actual old cap, selected
mask and buffered new cap of the independently held87 interface. It does
not claim equality of its broad PhysicalRows guard with this atlas. -/
theorem source_formula_dictionary (c : LiveCell) (t : Point) :
    oldCap c t = P5OriginalAdoptedEighthPhysicalMasks.oldComparison (sourceIndex c) t ∧
    selectedMask c = P5OriginalAdoptedEighthPhysicalMasks.selectedMask (sourceIndex c) := by
  cases c with
  | descending17 i =>
      have hi := i.isLt
      simp [oldCap, selectedMask, sourceIndex,
        P5OriginalAdoptedEighthPhysicalMasks.oldComparison,
        P5OriginalAdoptedEighthPhysicalMasks.selectedMask,
        P5OriginalAdoptedEighthPhysicalMasks.mask129,
        P2OriginalDescendingEighthLogSemantics.oldRaw,
        P2OriginalDescendingEighthLogSemantics.d,
        P5OriginalAdoptedEighthPhysicalMasks.d, show 15+i.val<30 by omega]
  | unequal18 u => cases u with
    | nine i =>
        have hi := i.isLt
        simp [oldCap, selectedMask, sourceIndex,
          P4AOriginalSeed7Unequal15Literal.oldCap, P4AOriginalSeed7Unequal15Literal.A,
          P5OriginalAdoptedEighthPhysicalMasks.oldComparison,
          P5OriginalAdoptedEighthPhysicalMasks.selectedMask,
          P5OriginalAdoptedEighthPhysicalMasks.mask138,
          P5OriginalAdoptedEighthPhysicalMasks.e,A,
          show ¬30+i.val<30 by omega,show 30+i.val≠43 by omega,show 30+i.val≠44 by omega]
    | fiftyAsc => rfl
    | fiftyDesc => rfl
  | ascending19 i =>
      have hi := i.isLt
      simp [oldCap, selectedMask, sourceIndex,
        P5OriginalAdoptedEighthPhysicalMasks.oldComparison,
        P5OriginalAdoptedEighthPhysicalMasks.selectedMask,
        P5OriginalAdoptedEighthPhysicalMasks.mask138,
        P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
        P5OriginalAdoptedEighthPhysicalMasks.e,
        show ¬45+i.val<30 by omega, show 45+i.val≠43 by omega,
        show 45+i.val≠44 by omega]

theorem source_newCap_dictionary (c : LiveCell) (t : Point) (hs : sourceRows c t) :
    newCap c t = P5OriginalAdoptedEighthPhysicalMasks.newCap (sourceIndex c) t := by
  cases c with
  | descending17 i =>
      have hi := i.isLt
      have hside := (source17_guard i t hs).descending
      simp [newCap,sourceIndex,P5OriginalAdoptedEighthPhysicalMasks.newCap,
        P2OriginalDescendingEighthLogSemantics.newCap,
        P2OriginalDescendingEighthLogSemantics.selectedSum,
        P2OriginalDescendingEighthLogSemantics.eta,
        P5OriginalAdoptedEighthPhysicalMasks.eta,
        show 15+i.val<30 by omega,v_eq_C hside.le]
  | unequal18 u => cases u with
    | nine i =>
        have hi := i.isLt
        simp [newCap,sourceIndex,P4AOriginalSeed7Unequal15Literal.newCap,
          P4AOriginalSeed7Unequal15Literal.A,P5OriginalAdoptedEighthPhysicalMasks.newCap,
          P5OriginalAdoptedEighthPhysicalMasks.eta,A,
          show ¬30+i.val<30 by omega,show 30+i.val≠43 by omega,show 30+i.val≠44 by omega]
    | fiftyAsc => rfl
    | fiftyDesc => rfl
  | ascending19 i =>
      have hi := i.isLt
      simp [newCap,sourceIndex,P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
        P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
        P2OriginalThirdMinorantLogDictionarySourceOnly.eta,
        P5OriginalAdoptedEighthPhysicalMasks.newCap,P5OriginalAdoptedEighthPhysicalMasks.eta,
        show ¬45+i.val<30 by omega,show 45+i.val≠43 by omega,show 45+i.val≠44 by omega]

/-- The held physical interface has identical guards at all of its first
thirty labels. This is why a Fin87 name cannot replace literal navigation
ownership; no source-cell identity is inferred from this interface alone. -/
theorem held_first_thirty_guard_alias (t : Point) (lambda3 current : ℝ) :
    P5OriginalAdoptedEighthPhysicalMasks.PhysicalRows 0 t lambda3 current ↔
      P5OriginalAdoptedEighthPhysicalMasks.PhysicalRows 29 t lambda3 current := by
  constructor <;> intro h <;> exact {
    group_side := h.group_side
    last_positive := h.last_positive
    ordered_last := h.ordered_last
    first_cube := h.first_cube
    third_cube := h.third_cube
    fifth_cube := h.fifth_cube
    third_history := h.third_history
    selected_license := h.selected_license
    third_to_sixth := h.third_to_sixth
    sixth_upper := h.sixth_upper
    improvement := h.improvement
    terminal := h.terminal
    full_squares := h.full_squares
    complement_squares := h.complement_squares }

end
end ImbalancedChen.P4AOriginalLive171819Atlas
