import ImbalancedChen.P1OriginalVariableFifthFullModulusBound
import ImbalancedChen.P2OriginalSixthElevenLogSemantics
import ImbalancedChen.FirstExitHistoricalLevels

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One actual fifth predecessor and all eleven literal sixth physical source
cells are combined by a finite maximum.  The selected rank-six frontier is
the frontier of the original fifth policy.  Every local source action keeps
its actual H5/fifth-parent comparison and source PhysicalCell predicate.
This writes a conservative cap policy, not an identification with the
published eleven-cell savings or a proof that the carriers are populated.
-/

namespace ImbalancedChen.P4AOriginalActualElevenSixthCandidate

noncomputable section
open scoped Classical
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics
open ImbalancedChen.P1OriginalVariableFifthContinuation
open ImbalancedChen.P1OriginalVariableFourthContinuation

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

def actualParent5 (pre : List ℕ) : ℝ :=
  exponent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre)

def physical6 (pre : List ℕ) : Physical := primeHistoryLogCoordinates N 6 pre

/-- The source-specific physical cell is read on a genuinely retained sixth
prefix; its cap comparison is with the actual fifth ancestor, not a supplied
lambda6 function. The global parent-domain bridge is still open. -/
def eligibleCell (c : Cell) (pre : List ℕ) : Prop :=
  pre.length = 6 ∧
  PhysicalCell c (physical6 N pre) ∧
  H5 (physical6 N pre) <
    actualParent5 e chi m omega N rows4 licensed4 J5 rows5 pre ∧
  actualParent5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤
    oldCap c (physical6 N pre)

def sixthSourceCap (pre : List ℕ) : ℝ :=
  finiteMax allCells.toFinset
    (fun c => eligibleCell e chi m omega N rows4 licensed4 J5 rows5 c pre)
    (fun c => newCap c (physical6 N pre))
    (actualParent5 e chi m omega N rows4 licensed4 J5 rows5 pre)

def sixthSourceLevel (pre : List ℕ) : ℝ :=
  N ^ sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 pre

def sixthSourcePolicy : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6
    (policy5 e chi m omega N rows4 licensed4 J5 rows5)
    (frozenParityRosserPolicy false 6
      (sixthSourceLevel e chi m omega N rows4 licensed4 J5 rows5))

def selectedSixthFrontier (Nnat cap : ℕ) (w z : ℝ) :
    List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 6
      (policy5 e chi m omega N rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse Nnat cap w z)).filter
    (fun s => decide (∃ c ∈ allCells,
      eligibleCell e chi m omega N rows4 licensed4 J5 rows5 c s.selectedPrefix))

theorem actualParent5_le_sixthSourceCap (pre : List ℕ) :
    actualParent5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤
      sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 pre := by
  exact finiteMax_seed_le _ _ _ _

theorem eligible_actualParent5_lt_newCap (c : Cell) (pre : List ℕ)
    (hc : eligibleCell e chi m omega N rows4 licensed4 J5 rows5 c pre) :
    actualParent5 e chi m omega N rows4 licensed4 J5 rows5 pre <
      newCap c (physical6 N pre) := by
  exact hc.2.2.2.trans_lt hc.2.1.positiveGap

theorem eligible_newCap_le_sixthSourceCap (c : Cell) (pre : List ℕ)
    (hc : eligibleCell e chi m omega N rows4 licensed4 J5 rows5 c pre) :
    newCap c (physical6 N pre) ≤
      sixthSourceCap e chi m omega N rows4 licensed4 J5 rows5 pre := by
  exact finiteMax_row_le _ _ _ _ c
    (List.mem_toFinset.mpr (allCells_complete c)) hc

theorem sixthSourcePolicy_through_six (positive : Bool) (pre : List ℕ)
    (h : pre.length ≤ 6) :
    sixthSourcePolicy e chi m omega N rows4 licensed4 J5 rows5 positive pre =
      policy5 e chi m omega N rows4 licensed4 J5 rows5 positive pre := by
  simp [sixthSourcePolicy, firstExitDepthSplicePolicy, h]

theorem sixthSourcePolicy_frontier_six (Nnat cap : ℕ) (w z : ℝ) :
    firstExitDepthFrontier 6
      (sixthSourcePolicy e chi m omega N rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse Nnat cap w z) =
    firstExitDepthFrontier 6
      (policy5 e chi m omega N rows4 licensed4 J5 rows5)
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse Nnat cap w z) := by
  exact firstExitDepthFrontier_depthSplice_eq 6 6 (by omega)
    (policy5 e chi m omega N rows4 licensed4 J5 rows5)
    (frozenParityRosserPolicy false 6
      (sixthSourceLevel e chi m omega N rows4 licensed4 J5 rows5))
    (fun p => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse Nnat cap w z) true 1

theorem sixthSourcePolicy_even (pre : List ℕ) :
    sixthSourcePolicy e chi m omega N rows4 licensed4 J5 rows5 true pre = true := by
  by_cases h : pre.length ≤ 6
  · rw [sixthSourcePolicy_through_six e chi m omega N rows4 licensed4 J5 rows5 true pre h]
    exact P1OriginalVariableFifthFullModulusBound.variable5_even_retained
      e chi m omega N rows4 licensed4 J5 rows5 pre
  · simp [sixthSourcePolicy, firstExitDepthSplicePolicy, h]

end
end ImbalancedChen.P4AOriginalActualElevenSixthCandidate
