import ImbalancedChen.P1HistoricalFifthCommonAncestorExcess
import ImbalancedChen.P1LiteralVariableFifthCompactSupplier
import ImbalancedChen.PrimeOwnCubeAffineGates

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two independently defined archive-bound old/common fifth maxima share
their actual candidate rows and gates but inherit DIFFERENT fourth seeds.
The exact seed excess controls their cap difference. This is not a claim
that excess is small, nor a transfer of the old-kernel B13 to the new gain.
-/
namespace ImbalancedChen.P5HistoricalChangedParentCapControl
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs
open P1HistoricalFifthCommonAncestorExcess P1LiteralVariableFifthCompactSupplier

/-- Nonexpansiveness is applied to actual separately defined source and
common-policy maxima, not to two aliases of a candidate. -/
theorem actual_fifth_cap_difference_le_parentExcess
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    |P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre -
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) pre| ≤
      parentExcess rows4 licensed4 e q chi omega N pre := by
  have hn := parentExcess_nonneg rows4 licensed4 e q chi omega N pre
  have hs : |P5OriginalCommonRefinedConstructor.exponent4 (sourceData rows4 licensed4 e q chi omega)
        N (rosserAncestor 4 pre) - inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre| ≤
      parentExcess rows4 licensed4 e q chi omega N pre := by
    change |parentExcess rows4 licensed4 e q chi omega N pre| ≤ _
    simpa only [abs_of_nonneg hn] using (le_refl (parentExcess rows4 licensed4 e q chi omega N pre))
  have h := finiteMax_moving_abs_sub_le (licensedRows e q chi omega)
    (fun r => eligible e chi (refinedMesh q) omega (globalOwners e q chi omega) r
      (primeHistoryLogCoordinates N 5 pre))
    (fun r => candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre))
    (fun r => candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre))
    (P5OriginalCommonRefinedConstructor.exponent4 (sourceData rows4 licensed4 e q chi omega)
      N (rosserAncestor 4 pre))
    (inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre)
    (parentExcess rows4 licensed4 e q chi omega N pre) hs
    (fun _ _ _ => by simpa only [sub_self, abs_zero] using hn)
  simpa only [P5OriginalCommonRefinedConstructor.exponent5, sourceData,
    P1OriginalVariableFifthContinuation.exponent5, if_pos hlen] using h

def actualChangedFifthCubeQueries (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) : Set (List ℕ) :=
  {pre | pre.length = 5 ∧
    primeTupleOwnCubeForm (primeHistoryLogCoordinates N 5 pre) <
      P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre ∧
    ¬ primeTupleOwnCubeForm (primeHistoryLogCoordinates N 5 pre) <
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) pre}

/-- The actual newly admitted LOG own-cube difference is enclosed by the
old-cap graph with width exactly the true parent excess. Neither that
graph's chamber-wise affine realization nor a small width is presumed. -/
theorem actual_changed_cube_query_width
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hp : pre ∈ actualChangedFifthCubeQueries rows4 licensed4 e q chi omega N) :
    |primeOwnCubeLinearForm 4 (primeHistoryLogCoordinates N 5 pre) -
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q) omega N rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) pre| ≤
      parentExcess rows4 licensed4 e q chi omega N pre := by
  have hd := actual_fifth_cap_difference_le_parentExcess rows4 licensed4 e q chi omega N pre hp.1
  have hlo := le_of_not_gt hp.2.2
  rw [primeOwnCubeLinearForm_apply, abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hu := (abs_le.mp hd).2
  linarith [hp.2.1]

theorem actual_changed_cube_query_has_changed_parent
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hp : pre ∈ actualChangedFifthCubeQueries rows4 licensed4 e q chi omega N) :
    pre ∈ changedParentPrefixes rows4 licensed4 e q chi omega N := by
  apply (changedParent_iff_positive_excess rows4 licensed4 e q chi omega N pre hp.1).mpr
  have hd := actual_fifth_cap_difference_le_parentExcess rows4 licensed4 e q chi omega N pre hp.1
  have hlo := le_of_not_gt hp.2.2
  have hu := (abs_le.mp hd).2
  linarith [hp.2.1]

end
end ImbalancedChen.P5HistoricalChangedParentCapControl
