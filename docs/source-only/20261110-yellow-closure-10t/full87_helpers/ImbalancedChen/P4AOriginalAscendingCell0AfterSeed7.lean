import ImbalancedChen.P4AOriginalActualSeed7Slot15
import ImbalancedChen.P4AOriginalAscending14Literal42
import ImbalancedChen.P4AOriginalPrior58Chronology

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Chronological slot 16, one named ascending source cell 0.  The literal
cell-0 navigation has row 14 for its descending old winner, row 16 for
the new cap, row 17 for the ascending license, and row 58 for old mask
26 on the left plane. Adopted
seed7 has the opposite mask-26 row 58.  These exact rows separate their
physical interiors before slot 16 is applied to the actual eleven-cell
sixth parent.  Full affine-to-CellGuard interpretation for all 96 rows
and the other thirteen ascending cells remains open.
-/

namespace ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7

noncomputable section
open scoped Classical BigOperators
open P4AOriginalAscending14Literal42
open P4AOriginalPrior58Chronology
open P4AOriginalActualSeed7Slot15
open P4AOriginalSeed7Unequal15Literal
open P2OriginalAscendingEighthCapDictionary
open P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics

abbrev Point8 := Fin 8 → ℝ

/-- Three exact affine rows of ascending source cell 0, in the archived
96-row order. The remaining rows enter through `CellGuard` below. -/
def cell0Row14 : Fin 9 → ℚ :=
  ![-25/64, 0, 2, 2, 0, 0, 0, 0, 0]
def cell0Row16 : Fin 9 → ℚ :=
  ![-195313/500000, 1/2, 3/2, 3/2, 0, 0, 0, 0, 1/2]
def cell0Row17 : Fin 9 → ℚ :=
  ![25/64, -2, 0, 0, 0, 0, 0, 0, -2]
def cell0Row58 : Fin 9 → ℚ :=
  ![25/64, 0, -2, -3/2, -1/2, -1/2, 0, 0, 0]

structure Cell0Affine (t : Point8) : Prop where
  winner : 0 < evalAffine cell0Row14 t
  gain : 0 < evalAffine cell0Row16 t
  license : 0 < evalAffine cell0Row17 t
  mask26 : 0 < evalAffine cell0Row58 t

theorem cell0_affine_semantic (t : Point8) (h : Cell0Affine t) :
    C (d t) < A (d t) ∧ R t < M t := by
  have hw := h.winner
  have hg := h.gain
  have hl := h.license
  simp [evalAffine, cell0Row14, cell0Row16, cell0Row17,
    Fin.sum_univ_succ] at hw hg hl
  have hbranch : A (selectedSum t) ≤ C (selectedSum t) := by
    dsimp [A, C, selectedSum]
    linarith
  have hm : M t = A (selectedSum t) - eta := by
    simp [M, min_eq_left hbranch]
  constructor
  · dsimp [A, C, d]
    linarith
  · rw [hm]
    dsimp [R, C, d, A, selectedSum, eta]
    linarith

private theorem seed7Row58 :
    (seed7Rows 58).2 =
      ![0, 0, 0, -3/2, 3/2, 3/2, 0, 0, 0] := by
  funext j
  fin_cases j <;> decide

/-- The archive's two mask-26 plane decisions are incompatible on a
point whose old winner is on the strict descending side. -/
theorem cell0_seed7_affine_disjoint (t : Point8)
    (hcell : Cell0Affine t)
    (hseed : seed7SourceRows t) : False := by
  have hseed26 := hseed (58 : Fin 96)
  rw [seed7Row58] at hseed26
  have hwin := hcell.winner
  have hmask := hcell.mask26
  simp [evalAffine, cell0Row14, cell0Row58,
    Fin.sum_univ_succ] at hwin hmask hseed26
  linarith

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

def sixth (pre : List ℕ) : ℝ :=
  actualSixth e chi m omega N rows4 licensed4 J5 rows5 pre

/-- This is a conservative semantic subdomain of named source cell 0:
its source-specific rows 14, 16, and 58 are literal, while `CellGuard`
retains the rest of the physical source conditions. -/
def cell0Selected (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
    let t := primeHistoryLogCoordinates N 8 pre
    CellGuard (literalPattern 0) t ∧
      CurrentParentGuard t
        (sixth e chi m omega N rows4 licensed4 J5 rows5
          (rosserAncestor 6 pre)) ∧
      Cell0Affine t

theorem cell0_not_seed7 (pre : List ℕ)
    (h : cell0Selected e chi m omega N rows4 licensed4 J5 rows5 pre) :
    ¬ sourceSeed7 e chi m omega N rows4 licensed4 J5 rows5 pre := by
  intro hs
  have hrows := hs.2.1
  exact cell0_seed7_affine_disjoint _ h.2.2.2 hrows

theorem cell0_owns_ascending14 (pre : List ℕ)
    (h : cell0Selected e chi m omega N rows4 licensed4 J5 rows5 pre) :
    ascending14Owns (primeHistoryLogCoordinates N 8 pre) := by
  exact ⟨0, (mem_selectedCellIndices 0).2 (by decide), h.2.1⟩

/-- On named cell 0, slot 15 has inherited the actual sixth cap.  Slot
16 then chooses its ascending cap, with no second adoption of seed7. -/
theorem chronological_slot16_cell0 (pre : List ℕ)
    (h : cell0Selected e chi m omega N rows4 licensed4 J5 rows5 pre) :
    slot16 N (sixth e chi m omega N rows4 licensed4 J5 rows5) pre =
      M (primeHistoryLogCoordinates N 8 pre) := by
  let t := primeHistoryLogCoordinates N 8 pre
  have hnot := cell0_not_seed7 e chi m omega N rows4 licensed4 J5 rows5 pre h
  have ha := cell0_owns_ascending14 e chi m omega N rows4 licensed4 J5 rows5 pre h
  have hparent : CurrentParentGuard t
      (sixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre)) := h.2.2.1
  have h16 : literal16Exponent N
      (sixth e chi m omega N rows4 licensed4 J5 rows5) pre = M t := by
    simp [literal16Exponent, familyNextExponent, ha, hparent, t,
      inheritedExponent]
  have h15 : slot15 N
      (sixth e chi m omega N rows4 licensed4 J5 rows5) pre =
      sixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) := by
    rw [slot15_source_identity e chi m omega N rows4 licensed4 J5 rows5 pre]
    simp [hnot]
  have hle : sixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) ≤ M t :=
    hparent.2.trans (cell0_affine_semantic t h.2.2.2).2.le
  simp only [slot16, h15, h16, max_eq_right hle]

end
end ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7
