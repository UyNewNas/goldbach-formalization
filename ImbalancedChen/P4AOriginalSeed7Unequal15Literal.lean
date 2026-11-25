import ImbalancedChen.P4AOriginalSeed7Unequal15SourceDefinitions
/- Source-only mechanical reuse. Original declarations unchanged.
Only non-Lean envelope removed. See SOURCE_RECEIPT.json. -/

import ImbalancedChen.FirstExitHistoricalLevels
import Mathlib.Data.Fin.VecNotation

namespace ImbalancedChen.P4AOriginalSeed7Unequal15Literal
noncomputable section
open scoped Classical BigOperators

abbrev Point := Fin 8 → ℝ
def A (s : ℝ) : ℝ := (1 + s) / 2
def D (s : ℝ) : ℝ := 57 / 64 - 3 * s / 2
def D23 (t : Point) : ℝ := D (t 1 + t 2)
def H7 (t : Point) : ℝ :=
  t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6
def evalAffine (row : Fin 9 → ℚ) (t : Point) : ℝ :=
  (row 0 : ℝ) + ∑ j : Fin 8, (row j.succ : ℝ) * t j

/-- Adopted equal-parent source cell7, mask129. -/
def seed7Left : Finset ℕ := {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,50,52,56}
def seed7Right : Finset ℕ := {3,5,6,7,9,11,13,14,15,17,19,21,22,23,25,26,27,29,30,31,33,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63}

/-- Thirteen winner9 patterns, including adopted duplicated cell11. -/
def nineLeft : Fin 13 → Finset ℕ :=
  ![
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,49,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56,60},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56,60},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,49,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,49,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48}
  ]
def nineRight : Fin 13 → Finset ℕ :=
  ![
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,52,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63}
  ]

def fiftyAscLeft : Finset ℕ := {1,2,4,6,8,10,12,16,17,18,20,24,32,33,34,36,40,48,50,52,56}
def fiftyAscRight : Finset ℕ := {3,5,7,9,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63}

def fiftyDescLeft : Finset ℕ := {1,2,4,6,8,10,12,16,18,20,24,28,32,34,36,40,44,48,52,56}
def fiftyDescRight : Finset ℕ := {3,5,7,9,11,13,14,15,17,19,21,22,23,25,26,27,29,30,31,33,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63}





inductive UnequalCell where
  | nine : Fin 13 → UnequalCell
  | fiftyAsc : UnequalCell
  | fiftyDesc : UnequalCell
  deriving DecidableEq, Fintype

theorem fifteen_cells : Fintype.card UnequalCell = 15 := by decide

def unequalSourceRows : UnequalCell → Point → Prop
  | .nine i, t => ∀ k : Fin 97, 0 < evalAffine (nineRows i k).2 t
  | .fiftyAsc, t => ∀ k : Fin 95, 0 < evalAffine (fiftyAscRows k).2 t
  | .fiftyDesc, t => ∀ k : Fin 96, 0 < evalAffine (fiftyDescRows k).2 t

def oldCap (c : UnequalCell) (t : Point) : ℝ :=
  match c with
  | .nine _ => A (t 0 + t 3)
  | .fiftyAsc => A (t 1 + t 4 + t 5)
  | .fiftyDesc => D (t 1 + t 4 + t 5)

def newCap (c : UnequalCell) (t : Point) : ℝ :=
  match c with
  | .nine _ => A (t 1 + t 3 + t 7) - 1 / 1000000
  | .fiftyAsc => A (t 3 + t 4 + t 5 + t 7) - 1 / 1000000
  | .fiftyDesc => D (t 1 + t 2 + t 7) - 1 / 1000000

def seed7SourceRows (t : Point) : Prop :=
  ∀ k : Fin 96, 0 < evalAffine (seed7Rows k).2 t

def currentSixth (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  lambda6 (rosserAncestor 6 pre)

/-- Same actual rank-eight parent and source-specific physical cap. The
improvement and H7 inequalities repeat named source rows pending their
affine-to-semantic rewrite. -/
def ActualUnequalCell (N : ℝ) (lambda6 : List ℕ → ℝ)
    (c : UnequalCell) (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
  let t := primeHistoryLogCoordinates N 8 pre
  unequalSourceRows c t ∧ H7 t < currentSixth lambda6 pre ∧
    currentSixth lambda6 pre ≤ oldCap c t ∧ oldCap c t < newCap c t

def ActualSeed7 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
  let t := primeHistoryLogCoordinates N 8 pre
  seed7SourceRows t ∧ H7 t < currentSixth lambda6 pre ∧
    currentSixth lambda6 pre ≤ D23 t ∧
      D23 t < A (t 0 + t 7) - 1 / 1000000

def seed7Raised (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  if ActualSeed7 N lambda6 pre then
    A ((primeHistoryLogCoordinates N 8 pre) 0 +
      (primeHistoryLogCoordinates N 8 pre) 7) - 1 / 1000000
  else currentSixth lambda6 pre

theorem current_le_seed7Raised (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    currentSixth lambda6 pre ≤ seed7Raised N lambda6 pre := by
  by_cases h : ActualSeed7 N lambda6 pre
  · simp only [seed7Raised, if_pos h]
    obtain ⟨_, _rows, _history, hcap, himp⟩ := h
    exact hcap.trans himp.le
  · simp [seed7Raised, h]

/-- A literal finite maximum over exactly thirteen winner9 and two
winner50 source cells. Ties remain admitted; numerical gains are counted
only after source domain disjointness is proved. -/
def unequalRaised (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  let cur := currentSixth lambda6 pre
  let t := primeHistoryLogCoordinates N 8 pre
  (Finset.univ : Finset UnequalCell).sup' (by
    exact ⟨.nine 0, Finset.mem_univ _⟩)
    (fun c => if ActualUnequalCell N lambda6 c pre then newCap c t else cur)

theorem current_le_unequalRaised (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    currentSixth lambda6 pre ≤ unequalRaised N lambda6 pre := by
  have hmem : (UnequalCell.nine 0) ∈
      (Finset.univ : Finset UnequalCell) := Finset.mem_univ _
  have hle := Finset.le_sup' (s := (Finset.univ : Finset UnequalCell))
    (f := fun c => if ActualUnequalCell N lambda6 c pre then
      newCap c (primeHistoryLogCoordinates N 8 pre)
      else currentSixth lambda6 pre) hmem
  by_cases h : ActualUnequalCell N lambda6 (.nine 0) pre
  · simp only [if_pos h] at hle
    obtain ⟨_, _, _, hcap, himp⟩ := h
    exact (hcap.trans himp.le).trans hle
  · simpa [unequalRaised, h] using hle

end
end ImbalancedChen.P4AOriginalSeed7Unequal15Literal
