import ImbalancedChen.P4AOriginalH5H7SourceDefinitions
/- Source-only mechanical reuse. Original declarations unchanged.
Only non-Lean envelope removed. See SOURCE_RECEIPT.json. -/

import ImbalancedChen.FirstExitHistoricalLevels
import Mathlib.Data.Fin.VecNotation

namespace ImbalancedChen.P4AOriginalFirstFailureH5H7Literal
noncomputable section
open scoped Classical BigOperators

abbrev Point := Fin 8 → ℝ
def A (s : ℝ) : ℝ := (1 + s) / 2
def D (s : ℝ) : ℝ := 57 / 64 - 3 * s / 2
def D23 (t : Point) : ℝ := D (t 1 + t 2)
def R6 (t : Point) : ℝ := A (t 0 + t 3)
def M8 (t : Point) : ℝ := A (t 1 + t 3 + t 7) - 1 / 1000000
def H1 (t : Point) : ℝ := 3 * t 0
def H3 (t : Point) : ℝ := t 0 + t 1 + 3 * t 2
def H5 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def H7 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6

/-- Literal complementary old-subset branch maps, masks 1..63. -/
def h5LeftMasks : Fin 7 → Finset ℕ :=
  ![
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,56}
  ]

def h5RightMasks : Fin 7 → Finset ℕ :=
  ![
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,52,53,54,55,57,58,59,60,61,62,63}
  ]

def h7LeftMasks : Fin 10 → Finset ℕ :=
  ![
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56,60},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56,60},
    {1,2,4,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,49,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,50,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,52,56},
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,56}
  ]

def h7RightMasks : Fin 10 → Finset ℕ :=
  ![
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,53,54,55,57,58,59,60,61,62,63},
    {3,5,6,7,11,13,14,15,19,21,22,23,25,26,27,28,29,30,31,35,37,38,39,41,42,43,44,45,46,47,49,50,51,52,53,54,55,57,58,59,60,61,62,63}
  ]

def evalAffine (row : Fin 9 → ℚ) (t : Point) : ℝ :=
  (row 0 : ℝ) + ∑ j : Fin 8, (row j.succ : ℝ) * t j

/-- Exact named rational affine rows from the pinned navigation JSON. -/


def H5AffineGuard (i : Fin 7) (t : Point) : Prop :=
  ∀ k : Fin 100, 0 < evalAffine (h5AffineRows i k).2 t

def H7AffineGuard (i : Fin 10) (t : Point) : Prop :=
  ∀ k : Fin 101, 0 < evalAffine (h7AffineRows i k).2 t

/-- Source ORDER=(1,3,5,7): preceding histories pass D23; the first
named history fails it. The true retained tree can still admit all four. -/
def H5Priority (t : Point) : Prop :=
  H1 t < D23 t ∧ H3 t < D23 t ∧ D23 t < H5 t

def H7Priority (t : Point) : Prop :=
  H1 t < D23 t ∧ H3 t < D23 t ∧ H5 t < D23 t ∧ D23 t < H7 t

theorem H5_H7_priority_disjoint (t : Point)
    (h5 : H5Priority t) (h7 : H7Priority t) : False := by
  exact (not_lt_of_ge h7.2.2.1.le) h5.2.2

def H5ActualGuard (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
  ∃ i : Fin 7,
    let t := primeHistoryLogCoordinates N 8 pre
    H5AffineGuard i t ∧ H5Priority t ∧
      H7 t < A (t 0) ∧ H7 t < lambda6 (rosserAncestor 6 pre) ∧
      lambda6 (rosserAncestor 6 pre) ≤ R6 t ∧ R6 t < M8 t

def H7ActualGuard (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
  ∃ i : Fin 10,
    let t := primeHistoryLogCoordinates N 8 pre
    H7AffineGuard i t ∧ H7Priority t ∧
      H7 t < A (t 0) ∧ H7 t < lambda6 (rosserAncestor 6 pre) ∧
      lambda6 (rosserAncestor 6 pre) ≤ R6 t ∧ R6 t < M8 t

def H5Raised (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if H5ActualGuard N lambda6 pre then M8 (primeHistoryLogCoordinates N 8 pre)
  else lambda6 (rosserAncestor 6 pre)

def H7Raised (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if H7ActualGuard N lambda6 pre then M8 (primeHistoryLogCoordinates N 8 pre)
  else lambda6 (rosserAncestor 6 pre)

/-- In both families the source's named row 19 is `M8-R6>0`.
The explicit physical guard records that same comparison until the
affine-to-semantic rewrite is compiled. -/
theorem H5_parent_le (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    lambda6 (rosserAncestor 6 pre) ≤ H5Raised N lambda6 pre := by
  by_cases h : H5ActualGuard N lambda6 pre
  · simp only [H5Raised, if_pos h]
    obtain ⟨_, i, _haffine, _hpriority, _hB3, _hhistory, hcap, hgap⟩ := h
    exact hcap.trans hgap.le
  · simp [H5Raised, h]

theorem H7_parent_le (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    lambda6 (rosserAncestor 6 pre) ≤ H7Raised N lambda6 pre := by
  by_cases h : H7ActualGuard N lambda6 pre
  · simp only [H7Raised, if_pos h]
    obtain ⟨_, i, _haffine, _hpriority, _hB3, _hhistory, hcap, hgap⟩ := h
    exact hcap.trans hgap.le
  · simp [H7Raised, h]

end
end ImbalancedChen.P4AOriginalFirstFailureH5H7Literal
