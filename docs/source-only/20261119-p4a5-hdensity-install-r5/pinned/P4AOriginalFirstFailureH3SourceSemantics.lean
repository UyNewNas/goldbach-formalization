import ImbalancedChen.P4AOriginalFirstFailureH3Literal
import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.VariableEnvelope
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original twelve H3 first-failure cells have 99 literal strict affine
rows each. This file proves the missing row-to-semantic dictionary on the
ENTIRE original open cell, including all eight full squares and all five
mask138 complement squares. No small box, branch licence, selected-square
claim, or target cap bound is assumed. The finite symbolic row identities
below are UNEVALUATED; no Lean/compiler or numerical replay was run.

The final dictionary removes the redundant StrictH3 conjunct from the
EXISTING ActualH3Guard and leaves h3Exponent exactly unchanged. Its actual
sixth-parent comparisons remain explicit. This is not a construction of
the whole 87-domain policy, its missing actual sixth parent, or its rho.
-/

namespace ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFirstFailureH3Literal

/-- The physical square expressions in the independent source, with its
original zero-based chronological slots. -/
def fullExpr (t : Point) (j : Fin 8) : ℝ :=
  (∑ k : Fin 8, if k < j then t k else 0) + 2 * t j

def complementExpr (t : Point) (j : Fin 8) : ℝ :=
  selected138 t +
    (∑ k : Fin 8, if k < j ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7 then t k else 0) +
    2 * t j

/-- Exactly the first 37 strict slacks, in the archived row order.
The constant ascending-licence identity is absent from the archive and
is not incorrectly required to be strictly positive. -/
def commonSlack (t : Point) : Fin 37 → ℝ :=
  ![mu - t 0, t 2 - 1 / 100, t 7 - 53 / 13824,
    t 0 - t 1, t 1 - t 2, t 2 - t 3, t 3 - t 4,
    t 4 - t 5, t 5 - t 6, t 6 - t 7,
    B3 t - H1 t, B3 t - H3 t, B3 t - H5 t, B3 t - H7 t,
    R6 t - B3 t, D (t 0 + t 3) - R6 t, R6 t - W t,
    t 1 + t 2 - mu, H3 t - D23 t, M8 t - R6 t,
    (D (selected138 t) - eta) - M8 t,
    M8 t - fullExpr t 0, M8 t - complementExpr t 0,
    M8 t - fullExpr t 1, M8 t - fullExpr t 2,
    M8 t - complementExpr t 2, M8 t - fullExpr t 3,
    M8 t - fullExpr t 4, M8 t - complementExpr t 4,
    M8 t - fullExpr t 5, M8 t - complementExpr t 5,
    M8 t - fullExpr t 6, M8 t - complementExpr t 6,
    M8 t - fullExpr t 7, R6 t - (S8 t + t 7),
    (S8 t + 3 * t 7) - M8 t, D23 t - H1 t]

def commonRow (k : Fin 37) : Fin 99 := ⟨k.val, by omega⟩

/-- The 62 proper old masks in the source are 1,...,8,10,...,63.
Mask9 is the winning raw identity and is not a strict row. -/
def branchMask (k : Fin 62) : ℕ :=
  if k.val < 8 then k.val + 1 else k.val + 2

def branchRow (k : Fin 62) : Fin 99 := ⟨37 + k.val, by omega⟩

/-- UNEVALUATED symbolic equality against every original common row.
The free real tuple is never sampled or replaced by a centre. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem source_common_row (i : Fin 12) (k : Fin 37) (t : Point) :
    evalAffine (sourceAffineRows i (commonRow k)).2 t = commonSlack t k := by
  fin_cases i <;> fin_cases k <;>
    norm_num [sourceAffineRows, commonRow, evalAffine, commonSlack,
      fullExpr, complementExpr, selected138, mu, eta, A, D, R6, B3,
      M8, S8, H1, H3, H5, H7, W, D23, Fin.sum_univ_succ] <;> ring

/-- UNEVALUATED symbolic equality against the original 12-by-62
assigned old planes; no payload-equality hypothesis is accepted. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem source_branch_row (i : Fin 12) (k : Fin 62) (t : Point) :
    evalAffine (sourceAffineRows i (branchRow k)).2 t =
      R6 t - oldPlane i (branchMask k) t := by
  fin_cases i <;> fin_cases k <;>
    norm_num [sourceAffineRows, branchRow, branchMask, evalAffine,
      oldPlane, leftMasks, oldSubsetSum, R6, A, D, Fin.sum_univ_succ] <;> ring

theorem branchMask_mem (k : Fin 62) :
    branchMask k ∈ Finset.Icc 1 63 ∧ branchMask k ≠ 9 := by
  have hk := k.isLt
  unfold branchMask
  split_ifs <;> simp only [Finset.mem_Icc] <;> omega

theorem branchMask_covers (m : ℕ) (hm : m ∈ Finset.Icc 1 63)
    (hm9 : m ≠ 9) : ∃ k : Fin 62, branchMask k = m := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hm
  by_cases h : m < 9
  · refine ⟨⟨m - 1, by omega⟩, ?_⟩
    simp only [branchMask]
    have hh : m - 1 < 8 := by omega
    rw [if_pos hh]
    omega
  · refine ⟨⟨m - 2, by omega⟩, ?_⟩
    simp only [branchMask]
    have hh : ¬m - 2 < 8 := by omega
    rw [if_neg hh]
    omega

/-- A lossless split of all 99 rows; neither the old-plane family nor
the short physical square rows can disappear during the conversion. -/
theorem sourceAffineGuard_iff_common_and_branches (i : Fin 12) (t : Point) :
    sourceAffineGuard i t ↔
      (∀ k : Fin 37, 0 < commonSlack t k) ∧
      (∀ k : Fin 62, oldPlane i (branchMask k) t < R6 t) := by
  constructor
  · intro h
    constructor
    · intro k
      rw [← source_common_row i k t]
      exact h (commonRow k)
    · intro k
      have hk := h (branchRow k)
      rw [source_branch_row] at hk
      exact sub_pos.mp hk
  · rintro ⟨hc, hb⟩ k
    by_cases hk : k.val < 37
    · let j : Fin 37 := ⟨k.val, hk⟩
      have hj : commonRow j = k := Fin.ext rfl
      rw [← hj, source_common_row]
      exact hc j
    · let j : Fin 62 := ⟨k.val - 37, by have := k.isLt; omega⟩
      have hj : branchRow j = k := by
        apply Fin.ext
        dsimp [branchRow, j]
        omega
      rw [← hj, source_branch_row]
      exact sub_pos.mpr (hb j)

def fullRow : Fin 8 → Fin 37 := ![21, 23, 24, 26, 27, 29, 31, 33]
def remainingSlot : Fin 5 → Fin 8 := ![0, 2, 4, 5, 6]
def complementRow : Fin 5 → Fin 37 := ![22, 25, 28, 30, 32]

private theorem commonSlack_full (j : Fin 8) (t : Point) :
    commonSlack t (fullRow j) = M8 t - fullExpr t j := by
  fin_cases j <;> simp [commonSlack, fullRow]

private theorem commonSlack_complement (j : Fin 5) (t : Point) :
    commonSlack t (complementRow j) = M8 t - complementExpr t (remainingSlot j) := by
  fin_cases j <;> simp [commonSlack, complementRow, remainingSlot]

private theorem remainingSlot_covers (j : Fin 8)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj7 : j ≠ 7) :
    ∃ k : Fin 5, remainingSlot k = j := by
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact (hj1 rfl).elim
  · exact ⟨1, rfl⟩
  · exact (hj3 rfl).elim
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact (hj7 rfl).elim

private theorem strictH3_of_common_and_branches {i : Fin 12} {t : Point}
    (hc : ∀ k : Fin 37, 0 < commonSlack t k)
    (hb : ∀ k : Fin 62, oldPlane i (branchMask k) t < R6 t) :
    StrictH3 i t where
  largest := by simpa [commonSlack] using sub_pos.mp (hc 0)
  third_cutoff := by simpa [commonSlack] using sub_pos.mp (hc 1)
  eighth_cutoff := by simpa [commonSlack] using sub_pos.mp (hc 2)
  ordered := by
    intro j
    fin_cases j
    · simpa [commonSlack] using sub_pos.mp (hc 3)
    · simpa [commonSlack] using sub_pos.mp (hc 4)
    · simpa [commonSlack] using sub_pos.mp (hc 5)
    · simpa [commonSlack] using sub_pos.mp (hc 6)
    · simpa [commonSlack] using sub_pos.mp (hc 7)
    · simpa [commonSlack] using sub_pos.mp (hc 8)
    · simpa [commonSlack] using sub_pos.mp (hc 9)
  first_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 10)
  H3_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 11)
  H5_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 12)
  H7_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 13)
  R6_above_B3 := by simpa [commonSlack] using sub_pos.mp (hc 14)
  winner9_ascending := by simpa [commonSlack] using sub_pos.mp (hc 15)
  W_below_R6 := by simpa [commonSlack] using sub_pos.mp (hc 16)
  d23_high := by simpa [commonSlack] using sub_pos.mp (hc 17)
  first_H3_failure := by simpa [commonSlack] using sub_pos.mp (hc 18)
  previous_H1_pass := by simpa [commonSlack] using sub_pos.mp (hc 36)
  improved := by simpa [commonSlack] using sub_pos.mp (hc 19)
  selected_descending_license := by simpa [commonSlack] using sub_pos.mp (hc 20)
  full_squares := by
    intro j
    have h := hc (fullRow j)
    rw [commonSlack_full] at h
    exact sub_pos.mp h
  selected_remaining_squares := by
    intro j hj1 hj3 hj7
    obtain ⟨k, rfl⟩ := remainingSlot_covers j hj1 hj3 hj7
    have h := hc (complementRow k)
    rw [commonSlack_complement] at h
    exact sub_pos.mp h
  old_residual := by simpa [commonSlack] using sub_pos.mp (hc 34)
  new_residual := by simpa [commonSlack] using sub_pos.mp (hc 35)
  old_planes := by
    intro m hm hm9
    obtain ⟨k, rfl⟩ := branchMask_covers m hm hm9
    exact hb k

private theorem strictH3_common_pos {i : Fin 12} {t : Point}
    (h : StrictH3 i t) : ∀ k : Fin 37, 0 < commonSlack t k := by
  intro k
  fin_cases k
  · simpa [commonSlack] using sub_pos.mpr h.largest
  · simpa [commonSlack] using sub_pos.mpr h.third_cutoff
  · simpa [commonSlack] using sub_pos.mpr h.eighth_cutoff
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 0)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 1)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 2)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 3)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 4)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 5)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 6)
  · simpa [commonSlack] using sub_pos.mpr h.first_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H3_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H5_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H7_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.R6_above_B3
  · simpa [commonSlack] using sub_pos.mpr h.winner9_ascending
  · simpa [commonSlack] using sub_pos.mpr h.W_below_R6
  · simpa [commonSlack] using sub_pos.mpr h.d23_high
  · simpa [commonSlack] using sub_pos.mpr h.first_H3_failure
  · simpa [commonSlack] using sub_pos.mpr h.improved
  · simpa [commonSlack] using sub_pos.mpr h.selected_descending_license
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 0)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 0 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 1)
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 2)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 2 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 3)
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 4)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 4 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 5)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 5 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 6)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 6 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 7)
  · simpa [commonSlack] using sub_pos.mpr h.old_residual
  · simpa [commonSlack] using sub_pos.mpr h.new_residual
  · simpa [commonSlack] using sub_pos.mpr h.previous_H1_pass

/-- Exact equivalence on every real point, including all boundary ties.
This eliminates the redundant semantic input from the original H3 guard. -/
theorem sourceAffineGuard_iff_StrictH3 (i : Fin 12) (t : Point) :
    sourceAffineGuard i t ↔ StrictH3 i t := by
  rw [sourceAffineGuard_iff_common_and_branches]
  constructor
  · rintro ⟨hc, hb⟩
    exact strictH3_of_common_and_branches hc hb
  · intro h
    refine ⟨strictH3_common_pos h, ?_⟩
    intro k
    exact h.old_planes (branchMask k) (branchMask_mem k).1 (branchMask_mem k).2

/-- The selected tent permission follows from the original strict rows.
The identity M8=A(selected)-eta is used, not assumed as a licence. -/
theorem source_selected_license {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) :
    M8 t < VariableEnvelope.v (selected138 t) := by
  have hs := (sourceAffineGuard_iff_StrictH3 i t).mp h
  rw [VariableEnvelope.v_eq_min]
  apply lt_min
  · dsimp [M8, A, eta, selected138, VariableEnvelope.A]
    linarith
  · have hd := hs.selected_descending_license
    dsimp [D, eta, VariableEnvelope.C] at hd ⊢
    linarith

theorem source_newCap_lt_Lambda {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) : M8 t < (153 / 256 : ℝ) := by
  exact (source_selected_license h).trans_le (VariableEnvelope.v_le_cap _)

/-- The selected physical mask is the unchanged source mask138. -/
def selectedSlots : Finset (Fin 8) := {1, 3, 7}

theorem source_full_and_selected_squares {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) :
    (∀ j, prefixSquareExpr t j < M8 t) ∧
      (∀ j ∉ selectedSlots, selectedSquareExpr selectedSlots t j < M8 t) := by
  have hs := (sourceAffineGuard_iff_StrictH3 i t).mp h
  constructor
  · intro j
    simpa [prefixSquareExpr, Finset.sum_filter] using hs.full_squares j
  · intro j hj
    have hnot : j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 7 := by
      simpa [selectedSlots] using hj
    have hh := hs.selected_remaining_squares j hnot.1 hnot.2.1 hnot.2.2
    simpa [selectedSquareExpr, selectedSlots, selected138, Finset.sum_filter,
      add_assoc, and_assoc] using hh

/-- Same N, same tuple, same M8: actual integer square support is now
supplied by source-domain membership rather than a PhysicalRows field. -/
theorem source_integer_square_gates {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) (N : ℝ) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ j, (p j : ℝ) ≤ N ^ t j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ M8 t) ∧
    (∀ j ∉ selectedSlots,
      ((∏ k ∈ selectedSlots, p k : ℕ) : ℝ) *
        ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selectedSlots),
          p k : ℕ) : ℝ) * (p j : ℝ) ^ 2 < N ^ M8 t) := by
  have hs := source_full_and_selected_squares h
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hs.1 j),
    fun j hj => selectedSquareExpr_actual_gate selectedSlots N hN p t hp j (hs.2 j hj)⟩

/-- Exact original guard, with only the duplicated semantic conjunct
removed. The actual retained-parent and upper-parent conditions are
explicitly still required and are not replaced by a branch licence. -/
theorem actualH3Guard_iff_source (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    ActualH3Guard N lambda6 pre ↔
      pre.length = 8 ∧ ∃ i : Fin 12,
        sourceAffineGuard i (primeHistoryLogCoordinates N 8 pre) ∧
        H7 (primeHistoryLogCoordinates N 8 pre) < lambda6 (rosserAncestor 6 pre) ∧
        lambda6 (rosserAncestor 6 pre) ≤ R6 (primeHistoryLogCoordinates N 8 pre) := by
  constructor
  · rintro ⟨hlen, i, _, hrows, hlo, hhi⟩
    exact ⟨hlen, i, hrows, hlo, hhi⟩
  · rintro ⟨hlen, i, hrows, hlo, hhi⟩
    exact ⟨hlen, i, (sourceAffineGuard_iff_StrictH3 i _).mp hrows, hrows, hlo, hhi⟩

/-- A dictionary for the EXISTING physical exponent. No replacement
policy, ambient prime universe, coefficient, or rho is introduced. -/
theorem h3Exponent_eq_source_dispatch (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    h3Exponent N lambda6 pre =
      if pre.length = 8 ∧ ∃ i : Fin 12,
          sourceAffineGuard i (primeHistoryLogCoordinates N 8 pre) ∧
          H7 (primeHistoryLogCoordinates N 8 pre) < lambda6 (rosserAncestor 6 pre) ∧
          lambda6 (rosserAncestor 6 pre) ≤ R6 (primeHistoryLogCoordinates N 8 pre)
      then M8 (primeHistoryLogCoordinates N 8 pre)
      else lambda6 (rosserAncestor 6 pre) := by
  rw [h3Exponent, actualH3Guard_iff_source]

end
end ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics
