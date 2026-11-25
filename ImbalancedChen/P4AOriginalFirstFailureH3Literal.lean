import ImbalancedChen.P4AOriginalH3SourceDefinitions
/-
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Mechanical reuse of the complete Lean segment in frozen source
97ac074bbef4df78305f7664c542824c480371081ee6585f70c52e9edcade141.
Only the non-Lean prose envelope is removed; all declarations and literal
rows are unchanged. See SOURCE_RECEIPT.json for byte and archive provenance.
-/

import ImbalancedChen.P2OriginalThirdMinorantLogDictionary
import ImbalancedChen.FirstExitHistoricalLevels
import Mathlib.Data.Fin.VecNotation

namespace ImbalancedChen.P4AOriginalFirstFailureH3Literal
noncomputable section
open scoped Classical BigOperators


def mu : ℝ := 25 / 128


def D (s : ℝ) : ℝ := 57 / 64 - 3 * s / 2

def B3 (t : Point) : ℝ := A (t 0)

def S8 (t : Point) : ℝ := ∑ j, t j
def selected138 (t : Point) : ℝ := t 1 + t 3 + t 7
def D23 (t : Point) : ℝ := D (t 1 + t 2)
def H1 (t : Point) : ℝ := 3 * t 0
def H3 (t : Point) : ℝ := t 0 + t 1 + 3 * t 2
def H5 (t : Point) : ℝ := t 0 + t 1 + t 2 + t 3 + 3 * t 4
def H7 (t : Point) : ℝ :=
  t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + 3 * t 6
def W (t : Point) : ℝ := 153 / 256 - 3 * t 2 / 8

/-- Twelve source left-plane masks in navigation order. Right is the
complement in the nonempty six-coordinate masks 1..63. -/
def leftMasks : Fin 12 → Finset ℕ :=
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
    {1,2,4,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,56}
  ]

def oldSubsetSum (mask : ℕ) (t : Point) : ℝ :=
  ∑ j : Fin 6, if decide (mask / 2 ^ j.val % 2 = 1) then t j.castSucc.castSucc else 0

def oldPlane (i : Fin 12) (mask : ℕ) (t : Point) : ℝ :=
  if mask ∈ leftMasks i then A (oldSubsetSum mask t)
  else D (oldSubsetSum mask t)

/-- Literal physical H3-first-failure source rows. No false ``first exit``
interpretation is attached to a failed sufficient D23 minorant. -/
structure StrictH3 (i : Fin 12) (t : Point) : Prop where
  largest : t 0 < mu
  third_cutoff : 1 / 100 < t 2
  eighth_cutoff : 53 / 13824 < t 7
  ordered : ∀ j : Fin 7, t j.succ < t j.castSucc
  first_below_B3 : H1 t < B3 t
  H3_below_B3 : H3 t < B3 t
  H5_below_B3 : H5 t < B3 t
  H7_below_B3 : H7 t < B3 t
  R6_above_B3 : B3 t < R6 t
  winner9_ascending : R6 t < D (t 0 + t 3)
  W_below_R6 : W t < R6 t
  d23_high : mu < t 1 + t 2
  first_H3_failure : D23 t < H3 t
  previous_H1_pass : H1 t < D23 t
  improved : R6 t < M8 t
  selected_descending_license : M8 t < D (selected138 t) - eta
  full_squares : ∀ j : Fin 8,
    (∑ k : Fin 8, if k < j then t k else 0) + 2 * t j < M8 t
  selected_remaining_squares : ∀ j : Fin 8,
    j ≠ 1 → j ≠ 3 → j ≠ 7 →
      selected138 t +
        (∑ k : Fin 8, if k < j ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7 then t k else 0) +
        2 * t j < M8 t
  old_residual : S8 t + t 7 < R6 t
  new_residual : M8 t < S8 t + 3 * t 7
  old_planes : ∀ mask ∈ Finset.Icc 1 63, mask ≠ 9 →
    oldPlane i mask t < R6 t


/-- Prefixes must already be retained by the actual inherited sixth tree;
the source comparison cap R6 bounds that actual cap only under this guard. -/
def ActualH3Guard (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
  ∃ i : Fin 12,
    let t := primeHistoryLogCoordinates N 8 pre
    StrictH3 i t ∧ sourceAffineGuard i t ∧
      H7 t < lambda6 (rosserAncestor 6 pre) ∧
      lambda6 (rosserAncestor 6 pre) ≤ R6 t

def h3Exponent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  if ActualH3Guard N lambda6 pre then
    M8 (primeHistoryLogCoordinates N 8 pre)
  else lambda6 (rosserAncestor 6 pre)

theorem h3_parent_le (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    lambda6 (rosserAncestor 6 pre) ≤ h3Exponent N lambda6 pre := by
  by_cases h : ActualH3Guard N lambda6 pre
  · simp only [h3Exponent, if_pos h]
    obtain ⟨_, i, hi, _haffine, _, hparent⟩ := h
    exact hparent.trans hi.improved.le
  · simp [h3Exponent, h]

theorem h3_inherits_outside (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (h : ¬ ActualH3Guard N lambda6 pre) :
    h3Exponent N lambda6 pre = lambda6 (rosserAncestor 6 pre) := by
  simp [h3Exponent, h]

end
end ImbalancedChen.P4AOriginalFirstFailureH3Literal
