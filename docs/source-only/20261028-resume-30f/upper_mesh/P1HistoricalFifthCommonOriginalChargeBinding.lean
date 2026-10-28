import ImbalancedChen.P1HistoricalFifthCommonLiteralContribution
import ImbalancedChen.P5OriginalFifthArchiveFiniteIdentity
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The independent physical owner's source-specific below-mu separation and
actual finite-carrier identity are consumed in one direction. They connect
our full original typed-index partition to the ORIGINAL finite fifth charge.
This does not identify that charge with the common physical-rho difference,
or with a limiting integral or saved Q80 floor.
-/
namespace ImbalancedChen.P1HistoricalFifthCommonOriginalChargeBinding
noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs
open P1HistoricalFifthCommonSourceContribution P1HistoricalFifthCommonLiteralContribution
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P5OriginalCommonRefinedFifthGainDefect P5OriginalFifthArchiveFallbackSeparation
open P5OriginalFifthArchiveFiniteIdentity

/-- Raising the common parent has ZERO local fifth-gain debt for this
actual original source, by the independent below-mu proof. The original
fourth seed and the common fourth seed are not globally identified. -/
theorem full_indexed_profile_sum_eq_original_gain
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    (∑ i : ArchiveIndex, indexedCommonGain i rows4 licensed4 e q chi omega N pre) =
      oldGain (sourceData rows4 licensed4 e q chi omega) N pre := by
  rw [← commonFifthGain_eq_indexed_source_sum rows4 licensed4 e q chi omega N pre hlen]
  have h := actual_archive_fifth_gain_unchanged rows4 licensed4 e q chi omega N pre hlen
  simpa only [commonFifthGain, commonGain, commonInherited,
    P1OriginalFifthIntegral.cellKernel] using h

/-- The actual ORIGINAL literal finite Rosser residual is the sum of
the same source positions, including its two original own-cube gates. -/
theorem original_literal_eq_full_indexed_sources
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    P1CorrectedFifthCausalTupleDictionary.literalTupleDifference
      (oldQ4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (oldQ5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p =
        ∑ i : ArchiveIndex, indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := by
  exact (actual_literal_same_increment rows4 licensed4 e q chi omega N cap p).symm.trans
    (actual_literal_eq_source_sum rows4 licensed4 e q chi omega N cap p)

/-- The finite source sum is now attached to the REAL common3 frontier
and the ORIGINAL actual fifth tuple charge. Carrier differences were paid
by the independent source-specific zero extension, not assumed absent. -/
theorem full_indexed_common_charge_eq_original_actual_charge
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (z : ℝ) :
    (∑ i : ArchiveIndex, ∑ p ∈ firstExitFrontierTuples 4
        (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
      (∏ k, 1 / ((p k : ℝ) - 1)) * indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p) =
      P4AOriginalVariableFifthPhysicalLedger.fifthTupleCharge e chi
        (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) N cap z := by
  have hs := actual_frontier_tuple_sum_eq_indexed_sources rows4 licensed4 e q chi omega N cap z
    (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
  have ho := commonLiteralCharge_eq_original rows4 licensed4 e q chi omega N cap z
  exact hs.symm.trans (by simpa only [commonLiteralCharge] using ho)

end
end ImbalancedChen.P1HistoricalFifthCommonOriginalChargeBinding
