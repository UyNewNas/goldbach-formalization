import ImbalancedChen.P1HistoricalFifthCommonChildContributions
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The full original source/child finite residual is attached to the adopted
ORIGINAL fifth saving and its two actual physical rough densities. Both
strict own-cube gates, the actual common3 frontier and the signed small-prime
negative-mass correction are kept. This is a finite identity at rough
cutoff 0. It does not prove uniform positive-cutoff approximation, a full
common-rho telescope, NPY authenticity, or any stored numerical reserve.
-/
namespace ImbalancedChen.P1HistoricalFifthIndexedChildPhysicalAttachment
noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs
open P1HistoricalFifthOriginalIndexedChildren P1HistoricalFifthCommonChildContributions
open P1OriginalFifthGrid400RefinedFullBoxCover
open P5OriginalCommonRefinedConstructor
open P4AOriginalVariableFifthPhysicalLedger

variable (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (e : ℚ) (q : ℕ) (chi omega : ℝ)

/-- Same actual original saving, normalized exactly as in its production
consumer. Each of the 18728512 original positions occurs once, with its
parent's own mask, fourth ancestor and complete finite Rosser residual. -/
theorem normalized_original_saving_eq_all_original_children
    (N cap : ℕ) (z : ℝ) :
    P1OriginalVariableFifthContinuation.actualFifthSaving e chi (refinedMesh q) omega
        rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ s : ArchiveChild, ∑ p ∈ firstExitFrontierTuples 4
        (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ k, 1 / ((p k : ℝ) - 1)) * indexedChildLiteral s rows4 licensed4 e q chi omega N cap p := by
  rw [fifthSaving_normalized_eq_tupleCharge]
  exact original_actual_charge_eq_all_original_child_contributions
    rows4 licensed4 e q chi omega N cap z

/-- The ORIGINAL adopted finite physical density difference consumes the
full child source ledger with exactly its original beta-plus weight.
The two actual negative rough masses supply the signed correction; no
asserted sign, equality of policies, or discarded correction is used. -/
theorem normalized_original_physical_difference_eq_all_original_children
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z L : ℝ) :
    (physical (P1OriginalVariableFourthContinuation.producerPolicy4
        (e : ℝ) chi (refinedMesh q) omega (N : ℝ) rows4 licensed4) N cap 0 z L -
      physical (P1OriginalVariableFifthContinuation.policy5 e chi (refinedMesh q) omega (N : ℝ)
        rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega)) N cap 0 z L) *
        Real.log (N : ℝ) / singularSeries N =
      (∑ s : ArchiveChild, ∑ p ∈ firstExitFrontierTuples 4
        (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ k, 1 / ((p k : ℝ) - 1)) * indexedChildLiteral s rows4 licensed4 e q chi omega N cap p) *
          smallPlus N cap 0 L +
        ((negative (P1OriginalVariableFourthContinuation.producerPolicy4
            (e : ℝ) chi (refinedMesh q) omega (N : ℝ) rows4 licensed4) N cap 0 z -
          negative (P1OriginalVariableFifthContinuation.policy5 e chi (refinedMesh q) omega (N : ℝ)
            rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega)) N cap 0 z) *
          Real.log (N : ℝ) / singularSeries N) * (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  rw [normalized_physical_difference_eq_tupleCharge e chi (refinedMesh q) omega rows4 licensed4
    (globalOwners e q chi omega) (licensedRows e q chi omega) N cap hN z L,
    original_actual_charge_eq_all_original_child_contributions rows4 licensed4 e q chi omega N cap z]

end
end ImbalancedChen.P1HistoricalFifthIndexedChildPhysicalAttachment
