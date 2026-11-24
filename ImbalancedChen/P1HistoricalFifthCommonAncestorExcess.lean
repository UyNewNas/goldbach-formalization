import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs
import ImbalancedChen.P5OriginalCommonRefinedPreservation
import Mathlib

/-! SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The genuine new-common ancestor has a nonnegative, explicit cap excess.
This supplies the exact changed-parent residual instead of replacing the
new parent by the old one inside the archive's kernel/gain argument. -/
namespace ImbalancedChen.P1HistoricalFifthCommonAncestorExcess
noncomputable section
open Set
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs

def parentExcess (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) : ℝ :=
  P5OriginalCommonRefinedConstructor.exponent4 (sourceData rows4 licensed4 e q chi omega)
    N (rosserAncestor 4 pre) - inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre

theorem parentExcess_nonneg (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) :
    0 ≤ parentExcess rows4 licensed4 e q chi omega N pre := by
  apply sub_nonneg.mpr
  exact P5OriginalCommonRefinedPreservation.original_exponent4_le_common
    (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre)

/-- On genuine fifth prefixes the changed-parent set is exactly the
strictly positive old-to-common cap excess, not an arbitrary held flag. -/
theorem changedParent_iff_positive_excess (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) :
    pre ∈ changedParentPrefixes rows4 licensed4 e q chi omega N ↔
      0 < parentExcess rows4 licensed4 e q chi omega N pre := by
  have hn := parentExcess_nonneg rows4 licensed4 e q chi omega N pre
  constructor
  · rintro ⟨_hlen, hne⟩
    have hx : parentExcess rows4 licensed4 e q chi omega N pre ≠ 0 := by
      intro h
      apply hne
      exact sub_eq_zero.mp h
    exact lt_of_le_of_ne hn (Ne.symm hx)
  · intro hp
    refine ⟨hlen, ?_⟩
    intro heq
    have hz : parentExcess rows4 licensed4 e q chi omega N pre = 0 := sub_eq_zero.mpr heq
    linarith

theorem zero_excess_common_fifth_eq_old (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (hzero : parentExcess rows4 licensed4 e q chi omega N pre = 0) :
    P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) pre := by
  apply common_exponent5_eq_old_off_changed_parent rows4 licensed4 e q chi omega N pre hlen
  intro hchanged
  have hp := (changedParent_iff_positive_excess rows4 licensed4 e q chi omega N pre hlen).mp hchanged
  linarith

/-- Actual cap containment is retained for this full-source data instance.
It is not coefficientwise signed monotonicity or a preservation of gain. -/
theorem original_archive_fifth_le_common (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) :
    P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
      (globalOwners e q chi omega) (licensedRows e q chi omega) pre ≤
        P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre :=
  P5OriginalCommonRefinedPreservation.original_exponent5_le_common
    (sourceData rows4 licensed4 e q chi omega) N pre

end
end ImbalancedChen.P1HistoricalFifthCommonAncestorExcess
