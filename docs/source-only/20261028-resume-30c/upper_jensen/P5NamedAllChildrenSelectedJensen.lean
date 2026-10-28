import ImbalancedChen.P5ChildSelectedOwnerJensenReserve
import ImbalancedChen.P5NamedFifthAllChildren

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The complete 64-child sums of the TWO original literal parents use their
exact signed child d values. Negative d contributes zero; no all-positive
claim, Q80 total, selected-volume reserve target or final K is assumed.
-/
namespace ImbalancedChen.P5NamedAllChildrenSelectedJensen
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1FifthMask6NamedParent0Owner P1FifthMask5NamedParent1Owner
open P1FifthGrid400UnitBoxPartition
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition
open P1OriginalFifthRawBoxSelectorEquivalence
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open P5NamedFifthPayloadSemantics
open P5NamedFifthAllChildren
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthActualChildJensenIntegral
open P5ChildSelectedOwnerJensenReserve

/-- The whole raw boxes, hence all 128 children, lie strictly below the
original ambient cutoff; this is a literal integer bound, not a compactness
or desired-integral assumption. -/
theorem named_upper_bound (b : Bool) (i : Fin 5) :
    ((namedParent b).upper i : ℝ) ≤ (19 / 96 : ℝ) := by
  cases b <;> fin_cases i <;>
    norm_num [namedParent, selectedParent0, selectedParent1, FifthWireRow.upper]

def namedCertifiedTotal (b : Bool) : ℝ :=
  ∑ c : ChildIndex, certifiedChildJensen (sourcePicks (namedParent b)) (namedParent b) c
    (savedRatio (namedParent b)) (sourceChildD (namedParent b) c)

def namedReserveTotal (b : Bool) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) : ℝ :=
  ∑ c : ChildIndex, childOwnerReserve (namedParent b) c e chi m omega J5

/-- No actual-child hleft, hnew, hconc, d-sign, d-identity, or Jensen-range
premise is left to the caller. The omitted selected-owner geometry is
still charged in namedReserveTotal rather than silently discarded. -/
theorem named_all64_Jensen_minus_reserve_le_positive_owner_sum
    (b : Bool) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    namedCertifiedTotal b - namedReserveTotal b e chi m omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        P1FifthPositivePartActualOwner.literalPositiveRawOwnerIntegral
          (namedParent b) e chi m omega j := by
  have h := all64_certified_sub_reserves_le_literal_owner_sum
    (sourcePicks (namedParent b)) (namedParent b) (named_grid b)
    (named_positive_indices b) (named_upper_bound b)
    (named_ratio_range b).1 (named_ratio_range b).2
    (fun c t ht => named_child_new_ratio b c t ht)
    (sourceChildD (namedParent b)) (namedChild_hd b) e chi m omega J5
  simpa only [namedCertifiedTotal, namedReserveTotal, Finset.sum_sub_distrib] using h

/-- The two actual local row families can now be consumed by the original
same-owner signed-source policy. All policy/ancestry premises remain exactly
those of the existing actual raw-owner comparison; no density estimate is
inserted as a primitive. -/
theorem named_all64_Jensen_minus_reserve_le_actual_owner_sum
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) (hkey : KeyInjective records)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (RefinedCell q))
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true)
    (b : Bool) (hr : namedParent b ∈ records) :
    namedCertifiedTotal b - namedReserveTotal b e chi (refinedMesh q) omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        rawOwnerIntegral (namedParent b) e chi (refinedMesh q) omega j rows4 licensed4 := by
  have h := all64_certified_sub_reserves_le_actual_owner_sum records q hq hgrid hmask hkey
    hpositive e he chi omega homega homegaRho rows4 licensed4 hgeometry J5 hgate
    (sourcePicks (namedParent b)) (namedParent b) hr (named_upper_bound b)
    (named_ratio_range b).1 (named_ratio_range b).2
    (fun c t ht => named_child_new_ratio b c t ht)
    (sourceChildD (namedParent b)) (namedChild_hd b)
  simpa only [namedCertifiedTotal, namedReserveTotal, Finset.sum_sub_distrib] using h

/-- The 64-cell reserve keeps both geometrically visible terms and the one
common source modulus. This is an exact sum identity, not a numerical budget. -/
theorem namedReserveTotal_eq_two_terms (b : Bool) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Owner m)) :
    namedReserveTotal b e chi m omega J5 =
      P1OriginalFifthLiteralKernelModulus.rowMassBound (namedParent b) *
          (∑ c : ChildIndex, volume.real (omittedChild (namedParent b) c e chi m omega J5)) +
        P1OriginalFifthLiteralKernelModulus.rowModulus (namedParent b) e *
          (∑ c : ChildIndex, volume.real (retainedChild (namedParent b) c e chi m omega J5)) :=
  sum_childOwnerReserve_eq_two_terms (namedParent b) e chi m omega J5

end
end ImbalancedChen.P5NamedAllChildrenSelectedJensen
