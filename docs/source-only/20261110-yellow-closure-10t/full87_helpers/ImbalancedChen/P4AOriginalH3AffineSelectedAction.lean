import ImbalancedChen.P4AOriginalFirstFailureH3Literal
import ImbalancedChen.P4AOriginalActualElevenSixthCandidate
import ImbalancedChen.FirstExitHistoricalLevels

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The first-failure H3 source has twelve literal 99-row cells.  Rows 19,
20, and 37 are respectively H3-D23, M8-R6, and D23-H1.  This source
binding makes those three comparisons consequences of the literal affine
rows, then applies the improved cap on the rank-eight prefix and its
rank-six ancestor.  The last section instantiates the ancestor by the
full eleven-cell sixth candidate.  It does not identify the preceding 58-domain
policy or charge an integral gain.
-/

namespace ImbalancedChen.P4AOriginalH3AffineSelectedAction

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFirstFailureH3Literal

private theorem failure_row (i : Fin 12) :
    (sourceAffineRows i 19).2 =
      ![-57/64, 1, 5/2, 9/2, 0, 0, 0, 0, 0] := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

private theorem improvement_row (i : Fin 12) :
    (sourceAffineRows i 20).2 =
      ![-1/1000000, -1/2, 1/2, 0, 0, 0, 0, 0, 1/2] := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

private theorem previous_row (i : Fin 12) :
    (sourceAffineRows i 37).2 =
      ![57/64, -3, -3/2, -3/2, 0, 0, 0, 0, 0] := by
  funext j
  fin_cases i <;> fin_cases j <;> decide

/-- The exact source row family, rather than separately supplied priority
inequalities, selects the first failing history. -/
theorem affine_h3_priority_and_improvement (i : Fin 12) (t : Point)
    (hrows : sourceAffineGuard i t) :
    H1 t < D23 t ∧ D23 t < H3 t ∧ R6 t < M8 t := by
  have hfirst := hrows (37 : Fin 99)
  have hfail := hrows (19 : Fin 99)
  have hgain := hrows (20 : Fin 99)
  rw [previous_row] at hfirst
  rw [failure_row] at hfail
  rw [improvement_row] at hgain
  simp [evalAffine, Fin.sum_univ_succ] at hfirst hfail hgain
  dsimp [H1, H3, D23, D, R6, M8, A, eta]
  constructor
  · linarith
  constructor <;> linarith

def selectedH3 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
    ∃ i : Fin 12,
      let t := primeHistoryLogCoordinates N 8 pre
      sourceAffineGuard i t ∧
        H7 t < lambda6 (rosserAncestor 6 pre) ∧
        lambda6 (rosserAncestor 6 pre) ≤ R6 t

def selectedCap (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  if selectedH3 N lambda6 pre then
    M8 (primeHistoryLogCoordinates N 8 pre)
  else lambda6 (rosserAncestor 6 pre)

theorem selectedH3_priority (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) (h : selectedH3 N lambda6 pre) :
    H1 (primeHistoryLogCoordinates N 8 pre) <
      D23 (primeHistoryLogCoordinates N 8 pre) ∧
    D23 (primeHistoryLogCoordinates N 8 pre) <
      H3 (primeHistoryLogCoordinates N 8 pre) := by
  obtain ⟨_, i, hrows, _, _⟩ := h
  exact ⟨(affine_h3_priority_and_improvement i _ hrows).1,
    (affine_h3_priority_and_improvement i _ hrows).2.1⟩

theorem actual_sixth_le_selectedCap (N : ℝ)
    (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    lambda6 (rosserAncestor 6 pre) ≤ selectedCap N lambda6 pre := by
  by_cases h : selectedH3 N lambda6 pre
  · obtain ⟨_, i, hrows, _, hparent⟩ := h
    simp only [selectedCap, if_pos h]
    exact hparent.trans
      (affine_h3_priority_and_improvement i _ hrows).2.2.le
  · simp [selectedCap, h]

open P4AOriginalActualElevenSixthCandidate
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics
open P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The concrete all-eleven sixth cap, with its own actual fifth ancestor,
is the parent value for this H3 source action. -/
def actualElevenSixthCap (pre : List ℕ) : ℝ :=
  P4AOriginalActualElevenSixthCandidate.sixthSourceCap
    e chi m omega N rows4 licensed4 J5 rows5 pre

def afterActualElevenH3Cap (pre : List ℕ) : ℝ :=
  selectedCap N
    (actualElevenSixthCap e chi m omega N rows4 licensed4 J5 rows5)
    pre

theorem actualEleven_ancestor_le_H3_cap (pre : List ℕ) :
    actualElevenSixthCap e chi m omega N rows4 licensed4 J5 rows5
      (rosserAncestor 6 pre) ≤
    afterActualElevenH3Cap e chi m omega N rows4 licensed4 J5 rows5
      pre := by
  exact actual_sixth_le_selectedCap N
    (actualElevenSixthCap e chi m omega N rows4 licensed4 J5 rows5) pre

end
end ImbalancedChen.P4AOriginalH3AffineSelectedAction
