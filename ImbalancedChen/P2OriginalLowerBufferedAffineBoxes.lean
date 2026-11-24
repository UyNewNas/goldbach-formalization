import ImbalancedChen.P2OriginalLowerSelectedCapConstructor

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Construct the finite rational candidate rows from a selected affine
-- chamber policy by taking its whole-box lower vertex minus one buffer.
-- The selector, wall trimming, and quantitative density convergence are
-- separate; no selected final lower bound is a premise of this module.

namespace ImbalancedChen.P2OriginalLowerBufferedAffineBoxes

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2OriginalLowerSelectedCapConstructor

def qa : ℚ := 417 / 5000
def qh : ℚ := 19 / 125

def gridPoint (mesh index : ℕ) : ℚ :=
  qa + index * ((qh - qa) / (mesh + 1))

def cellLo (mesh : ℕ) : CellCode mesh → ℚ
  | none => qh
  | some j => gridPoint mesh j.val

def cellHi (mesh : ℕ) : CellCode mesh → ℚ
  | none => qh
  | some j => gridPoint mesh (j.val + 1)

structure RationalBox where
  lo : Fin 5 → ℚ
  hi : Fin 5 → ℚ

def boxOfCode {mesh : ℕ} (code : Code mesh) : RationalBox :=
  { lo := fun i => cellLo mesh (code i).1
    hi := fun i => cellHi mesh (code i).1 }

def inBox (box : RationalBox) (x : Fin 5 → ℝ) : Prop :=
  ∀ i, (box.lo i : ℝ) ≤ x i ∧ x i ≤ (box.hi i : ℝ)

-- A real affine function with rational coefficients. The finite policy
-- selector owns its branch labels and may expose them as this tuple.
abbrev BranchData := ℚ × (Fin 5 → ℚ) × ℚ

def affineValue (constant : ℚ) (slope : Fin 5 → ℚ)
    (x : Fin 5 → ℝ) : ℝ :=
  constant + ∑ i : Fin 5, (slope i : ℝ) * x i

def lowerVertex (slope : Fin 5 → ℚ) (box : RationalBox)
    (i : Fin 5) : ℚ :=
  if 0 ≤ slope i then box.lo i else box.hi i

def wholeBoxInfimum (constant : ℚ) (slope : Fin 5 → ℚ)
    (box : RationalBox) : ℚ :=
  constant + ∑ i : Fin 5, slope i * lowerVertex slope box i

theorem lowerVertex_term_le (slope : Fin 5 → ℚ) (box : RationalBox)
    (x : Fin 5 → ℝ) (hx : inBox box x) (i : Fin 5) :
    (slope i : ℝ) * (lowerVertex slope box i : ℝ) ≤
      (slope i : ℝ) * x i := by
  by_cases hnonneg : 0 ≤ slope i
  · have hs : (0 : ℝ) ≤ slope i := by exact_mod_cast hnonneg
    simpa only [lowerVertex, if_pos hnonneg] using
      mul_le_mul_of_nonneg_left (hx i).1 hs
  · have hs : (slope i : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hnonneg))
    simpa only [lowerVertex, if_neg hnonneg] using
      mul_le_mul_of_nonpos_left (hx i).2 hs

theorem wholeBoxInfimum_le_affine (constant : ℚ)
    (slope : Fin 5 → ℚ) (box : RationalBox)
    (x : Fin 5 → ℝ) (hx : inBox box x) :
    (wholeBoxInfimum constant slope box : ℝ) ≤
      affineValue constant slope x := by
  have hsum :
      (∑ i : Fin 5, (slope i : ℝ) * (lowerVertex slope box i : ℝ)) ≤
        ∑ i : Fin 5, (slope i : ℝ) * x i := by
    exact Finset.sum_le_sum (fun i _ => lowerVertex_term_le slope box x hx i)
  unfold wholeBoxInfimum affineValue
  push_cast
  exact add_le_add_left hsum _

theorem buffered_infimum_below_affine (constant : ℚ)
    (slope : Fin 5 → ℚ) (box : RationalBox) (buffer : ℚ)
    (hbuffer : 0 < buffer) (x : Fin 5 → ℝ) (hx : inBox box x) :
    ((wholeBoxInfimum constant slope box - buffer : ℚ) : ℝ) <
      affineValue constant slope x := by
  have hb : (0 : ℝ) < buffer := by exact_mod_cast hbuffer
  have hi := wholeBoxInfimum_le_affine constant slope box x hx
  push_cast
  linarith

-- The finite selector returns one branch or the literal inherit label at
-- each rank/chamber. Masking occurs before both the selector and box reader.
def boxedTable {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option BranchData)
    (buffer : ℚ) : BranchTable mesh :=
  ⟨fun rank code =>
    (select rank (prefixCode rank.val code)).map (fun branch =>
      (wholeBoxInfimum branch.1 branch.2.1
          (boxOfCode (prefixCode rank.val code)) - buffer,
        branch.2.2))⟩

@[simp] theorem boxedTable_inherit {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option BranchData)
    (buffer : ℚ) (rank : Fin 6) (code : Code mesh)
    (hinherit : select rank (prefixCode rank.val code) = none) :
    (boxedTable select buffer).row rank code = none := by
  simp [boxedTable, hinherit]

-- This explicitly produces one finite CapPlan from a finite chamber
-- selector, rational mesh and rational buffer. The preceding checkedChoice
-- still rejects any cell whose incoming or selected square gate fails.
def boxedPlan {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option BranchData)
    (buffer : ℚ) (rho : ℝ) : CapPlan 5 mesh :=
  selectedPlan (boxedTable select buffer) rho

theorem boxedPlan_cap_chain {mesh : ℕ}
    (select : Fin 6 → Code mesh → Option BranchData)
    (buffer : ℚ) (rho : ℝ) (code : Code mesh)
    (hseed : seedCap rho ≤ Lambda) :
    seedCap rho ≤ cap3 (boxedTable select buffer) rho code ∧
      cap3 (boxedTable select buffer) rho code ≤
        cap4 (boxedTable select buffer) rho code ∧
      cap4 (boxedTable select buffer) rho code ≤
        cap5 (boxedTable select buffer) rho code ∧
      cap5 (boxedTable select buffer) rho code ≤ Lambda :=
  cap_chain (boxedTable select buffer) rho code hseed

end
end ImbalancedChen.P2OriginalLowerBufferedAffineBoxes
