import ImbalancedChen.P1HistoricalFifthOriginalIndexedChildren
import ImbalancedChen.P1HistoricalFifthCommonOriginalChargeBinding
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The independently defined actual common finite Rosser charge is restricted
to the original64 children of each original source. Summing those children
recovers the parent ONCE, then the actual original143-block charge ledger.
Neither a saved child floor nor a new per-child cap replaces this source.
-/
namespace ImbalancedChen.P1HistoricalFifthCommonChildContributions
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs
open P1HistoricalFifthCommonSourceContribution P1HistoricalFifthCommonLiteralContribution
open P1HistoricalFifthCommonOriginalChargeBinding P1HistoricalFifthOriginalBlockContributions
open P1HistoricalFifthOriginalIndexedChildren P5OldFifthExact64ChildTiling
open P5OriginalCommonRefinedConstructor

def indexedChildLiteral (s : ArchiveChild) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  if actualPrimeTupleLog N p ∈ archiveChildBox s then
    indexedLiteralTupleDifference s.1 rows4 licensed4 e q chi omega N cap p
  else 0

/-- The real raw geometry supplies all64 source children. No candidate is
removed by a child own-cube/admission test and no gain is multiplied by64. -/
theorem indexed_literal_eq_sum_actual_64_children
    (i : ArchiveIndex) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p =
      ∑ c : ChildIndex, indexedChildLiteral (i, c) rows4 licensed4 e q chi omega N cap p := by
  by_cases ht : actualPrimeTupleLog N p ∈ (archiveRow i).originalBox
  · obtain ⟨c, hc⟩ := parent_covered_by_child (archiveRow i)
      (P1HistoricalFifthTypedBaseGeometry.archiveRow_grid i) _ ht
    have hsum : (∑ d : ChildIndex, indexedChildLiteral (i, d) rows4 licensed4 e q chi omega N cap p) =
        indexedChildLiteral (i, c) rows4 licensed4 e q chi omega N cap p := by
      apply Finset.sum_eq_single c
      · intro d _hd hdc
        have hn : actualPrimeTupleLog N p ∉ archiveChildBox (i, d) := by
          intro hd
          exact hdc (common_child_point_eq (archiveRow i) d c _ hd hc)
        exact if_neg hn
      · intro hnot
        exact (hnot (Finset.mem_univ c)).elim
    have hterm : indexedChildLiteral (i, c) rows4 licensed4 e q chi omega N cap p =
        indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := if_pos hc
    exact (hsum.trans hterm).symm
  · have hsource : actualPrimeTupleLog N p ∉ sourceCellDomain i e q chi omega := by
      intro hs
      exact ht (sourceCellDomain_subset_raw i e q chi omega hs)
    have hzero : indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p = 0 :=
      if_neg hsource
    simp only [hzero, indexedChildLiteral, ite_self, Finset.sum_const_zero]

/-- All18728512 actual source/child positions contribute to the SAME
independent common Q4/Q5 finite residual with BOTH original own-cube gates. -/
theorem actual_common_literal_eq_all_original_children
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    P1CorrectedFifthCausalTupleDictionary.literalTupleDifference
      (level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p =
        ∑ s : ArchiveChild, indexedChildLiteral s rows4 licensed4 e q chi omega N cap p := by
  rw [actual_literal_eq_source_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ =>
    indexed_literal_eq_sum_actual_64_children i rows4 licensed4 e q chi omega N cap p)

/-- Exact direct binding to the original143 ordered typed blocks. The
source-index lookup recovers each original row occurrence, not a row-value
Finset or a newly named bank. This also preserves its original mask. -/
theorem child_literal_sum_eq_original_143_block_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    (∑ s : ArchiveChild, indexedChildLiteral s rows4 licensed4 e q chi omega N cap p) =
      (Data.P1HistoricalFifthSavedTableData.blocks.toList.map (fun block =>
        (block.toList.map (fun raw => originalIndexContribution raw (fun i =>
          ∑ c : ChildIndex, indexedChildLiteral (i, c) rows4 licensed4 e q chi omega N cap p))).sum)).sum := by
  rw [Fintype.sum_prod_type]
  exact indexed_sum_eq_original_143_blocks _

/-- The actual common3 frontier, target, cap, rough universe and original
reciprocal-prime factors survive this complete child partition. The result
is the ORIGINAL production fifthTupleCharge, not a declared new charge. -/
theorem original_actual_charge_eq_all_original_child_contributions
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (z : ℝ) :
    P4AOriginalVariableFifthPhysicalLedger.fifthTupleCharge e chi
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega rows4 licensed4
      (globalOwners e q chi omega) (licensedRows e q chi omega) N cap z =
      ∑ s : ArchiveChild, ∑ p ∈ firstExitFrontierTuples 4
        (common3 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ k, 1 / ((p k : ℝ) - 1)) * indexedChildLiteral s rows4 licensed4 e q chi omega N cap p := by
  rw [← full_indexed_common_charge_eq_original_actual_charge rows4 licensed4 e q chi omega N cap z,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← Finset.mul_sum, ← indexed_literal_eq_sum_actual_64_children]

end
end ImbalancedChen.P1HistoricalFifthCommonChildContributions
