import ImbalancedChen.P4AOriginalAscending14Literal42
import ImbalancedChen.P4AOriginalSeed7Unequal15Literal
import ImbalancedChen.OriginalDescendingFifteenCellOwnership
import ImbalancedChen.OriginalAscendingThirteenCellOwnership
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

namespace ImbalancedChen.P4AOriginalPrior58Chronology

noncomputable section
open scoped Classical

def slot15 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  P4AOriginalSeed7Unequal15Literal.seed7Raised N lambda6 pre

def slot16 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  max (slot15 N lambda6 pre)
    (P4AOriginalAscending14Literal42.literal16Exponent N lambda6 pre)

def slot17 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  max (slot16 N lambda6 pre)
    (OriginalDescendingFifteenCellOwnership.ownedRaisedExponent N lambda6 pre)

def slot18 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  max (slot17 N lambda6 pre)
    (P4AOriginalSeed7Unequal15Literal.unequalRaised N lambda6 pre)

def slot19 (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  max (slot18 N lambda6 pre)
    (OriginalAscendingThirteenCellOwnership.ownedRaisedExponent N lambda6 pre)

theorem slot15_le_slot16 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : slot15 N lambda6 pre ≤ slot16 N lambda6 pre :=
  le_max_left _ _

theorem slot16_le_slot17 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : slot16 N lambda6 pre ≤ slot17 N lambda6 pre :=
  le_max_left _ _

theorem slot17_le_slot18 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : slot17 N lambda6 pre ≤ slot18 N lambda6 pre :=
  le_max_left _ _

theorem slot18_le_slot19 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : slot18 N lambda6 pre ≤ slot19 N lambda6 pre :=
  le_max_left _ _

theorem actual_sixth_le_slot19 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    P4AOriginalSeed7Unequal15Literal.currentSixth lambda6 pre ≤
      slot19 N lambda6 pre := by
  exact (P4AOriginalSeed7Unequal15Literal.current_le_seed7Raised
    N lambda6 pre).trans
    ((slot15_le_slot16 N lambda6 pre).trans
      ((slot16_le_slot17 N lambda6 pre).trans
        ((slot17_le_slot18 N lambda6 pre).trans
          (slot18_le_slot19 N lambda6 pre))))

/-- One eighth replacement after the actual sixth parent. This keeps
every rank-eight admission and every prime ancestor of the parent. -/
def candidate58Policy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (baseSixth : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 baseSixth)
    (frozenParityRosserPolicy false 8
      (fun pre => N ^ slot19 N lambda6 pre))

theorem candidate58_through_eight (N : ℝ) (lambda6 : List ℕ → ℝ)
    (baseSixth : Bool → List ℕ → Bool) (b : Bool) (pre : List ℕ)
    (h : pre.length ≤ 8) :
    candidate58Policy N lambda6 baseSixth b pre =
      P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 baseSixth
        b pre := by
  simp [candidate58Policy, firstExitDepthSplicePolicy, h]

theorem candidate58_frontier_eight (N : ℝ) (lambda6 : List ℕ → ℝ)
    (baseSixth : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (candidate58Policy N lambda6 baseSixth)
      h pre positive mass carrier =
    firstExitDepthFrontier 8
      (P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 baseSixth)
      h pre positive mass carrier := by
  exact firstExitDepthFrontier_depthSplice_eq 8 8 (by omega)
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 baseSixth)
    (frozenParityRosserPolicy false 8
      (fun pre => N ^ slot19 N lambda6 pre))
    h pre carrier positive mass

theorem candidate58_even (N : ℝ) (lambda6 : List ℕ → ℝ)
    (baseSixth : Bool → List ℕ → Bool)
    (hbase : ∀ pre,
      P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 baseSixth
        true pre = true) (pre : List ℕ) :
    candidate58Policy N lambda6 baseSixth true pre = true := by
  by_cases h : pre.length ≤ 8
  · rw [candidate58_through_eight N lambda6 baseSixth true pre h]
    exact hbase pre
  · simp [candidate58Policy, firstExitDepthSplicePolicy, h]

end
end ImbalancedChen.P4AOriginalPrior58Chronology
