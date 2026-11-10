import ImbalancedChen.P4AOriginalSeed7Unequal15Literal
import ImbalancedChen.P4AOriginalPrior58Chronology
import ImbalancedChen.P4AOriginalActualElevenSixthCandidate

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The adopted equal-parent seed is chronological slot 15.  Its source
affine rows 13 and 16 are the old H7 history below D23 and the new
ascending cap above D23.  This module removes the duplicated improvement
premise from the seed's selected domain after substituting the concrete
eleven-cell sixth cap.  The later four slots are assembled over that
same sixth policy, without claiming that their maximum equals the
published selected 58-domain policy.
-/

namespace ImbalancedChen.P4AOriginalActualSeed7Slot15

noncomputable section
open scoped Classical BigOperators
open P4AOriginalSeed7Unequal15Literal
open P4AOriginalActualElevenSixthCandidate
open P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics

private theorem seed_history_row :
    (seed7Rows 13).2 =
      ![57/64, -1, -5/2, -5/2, -1, -1, -1, -3, 0] := by
  funext j
  fin_cases j <;> decide

private theorem seed_improvement_row :
    (seed7Rows 16).2 =
      ![-195313/500000, 1/2, 3/2, 3/2, 0, 0, 0, 0, 1/2] := by
  funext j
  fin_cases j <;> decide

/-- Two source inequalities on the same physical eight-tuple. -/
theorem seed7_affine_history_and_gain (t : Point)
    (hrows : seed7SourceRows t) :
    H7 t < D23 t ∧ D23 t < A (t 0 + t 7) - 1 / 1000000 := by
  have hhistory := hrows (13 : Fin 96)
  have himprovement := hrows (16 : Fin 96)
  rw [seed_history_row] at hhistory
  rw [seed_improvement_row] at himprovement
  simp [evalAffine, Fin.sum_univ_succ] at hhistory himprovement
  dsimp [H7, D23, D, A]
  constructor <;> linarith

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

def actualSixth (pre : List ℕ) : ℝ :=
  P4AOriginalActualElevenSixthCandidate.sixthSourceCap
    e chi m omega N rows4 licensed4 J5 rows5 pre

/-- The literal row domain with the actual all-eleven sixth parent.
History and parent attachment remain physical premises; improvement is
deduced from row 16. -/
def sourceSeed7 (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
    let t := primeHistoryLogCoordinates N 8 pre
    seed7SourceRows t ∧
      H7 t < actualSixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) ∧
      actualSixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) ≤ D23 t

/-- Exact slot-15 source condition: the extra old-to-new comparison in
ActualSeed7 is a consequence of the recorded affine row, not an input. -/
theorem sourceSeed7_iff_actualSeed7 (pre : List ℕ) :
    sourceSeed7 e chi m omega N rows4 licensed4 J5 rows5 pre ↔
      ActualSeed7 N
        (actualSixth e chi m omega N rows4 licensed4 J5 rows5)
        pre := by
  constructor
  · rintro ⟨hlen, hrows, hhistory, hparent⟩
    exact ⟨hlen, hrows, hhistory, hparent,
      (seed7_affine_history_and_gain _ hrows).2⟩
  · rintro ⟨hlen, hrows, hhistory, hparent, _⟩
    exact ⟨hlen, hrows, hhistory, hparent⟩

theorem sourceSeed7_priority (pre : List ℕ)
    (h : sourceSeed7 e chi m omega N rows4 licensed4 J5 rows5 pre) :
    H7 (primeHistoryLogCoordinates N 8 pre) <
      actualSixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) ∧
    actualSixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre) ≤
      D23 (primeHistoryLogCoordinates N 8 pre) ∧
    D23 (primeHistoryLogCoordinates N 8 pre) <
      A ((primeHistoryLogCoordinates N 8 pre) 0 +
        (primeHistoryLogCoordinates N 8 pre) 7) - 1 / 1000000 := by
  obtain ⟨_, hrows, hh, hp⟩ := h
  exact ⟨hh, hp, (seed7_affine_history_and_gain _ hrows).2⟩

/-- Slot 15 is exactly the adopted seed action on its affine domain,
and otherwise inherits the actual eleven-cell sixth cap. -/
theorem slot15_source_identity (pre : List ℕ) :
    P4AOriginalPrior58Chronology.slot15 N
      (actualSixth e chi m omega N rows4 licensed4 J5 rows5) pre =
    if sourceSeed7 e chi m omega N rows4 licensed4 J5 rows5 pre then
      A ((primeHistoryLogCoordinates N 8 pre) 0 +
        (primeHistoryLogCoordinates N 8 pre) 7) - 1 / 1000000
    else actualSixth e chi m omega N rows4 licensed4 J5 rows5
      (rosserAncestor 6 pre) := by
  simp [P4AOriginalPrior58Chronology.slot15, seed7Raised,
    sourceSeed7_iff_actualSeed7]

/-- A concrete causal starting tree for the slot-15 to slot-19
candidate.  Equality with all source-selected 58 domains is open. -/
def actual58Candidate : Bool → List ℕ → Bool :=
  P4AOriginalPrior58Chronology.candidate58Policy N
    (actualSixth e chi m omega N rows4 licensed4 J5 rows5)
    (P4AOriginalActualElevenSixthCandidate.sixthSourcePolicy
      e chi m omega N rows4 licensed4 J5 rows5)

theorem actual58_through_eight (b : Bool) (pre : List ℕ)
    (h : pre.length ≤ 8) :
    actual58Candidate e chi m omega N rows4 licensed4 J5 rows5 b pre =
      P4AOriginalActualElevenSixthCandidate.sixthSourcePolicy
        e chi m omega N rows4 licensed4 J5 rows5 b pre := by
  exact P4AOriginalPrior58Chronology.candidate58_through_eight N
    (actualSixth e chi m omega N rows4 licensed4 J5 rows5)
    (P4AOriginalActualElevenSixthCandidate.sixthSourcePolicy
      e chi m omega N rows4 licensed4 J5 rows5) b pre h

end
end ImbalancedChen.P4AOriginalActualSeed7Slot15
