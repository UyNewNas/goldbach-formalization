import ImbalancedChen.P1HistoricalFifthPhysicalGateOverlap
import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.ActualHistoricalFifthCellIntegral

/-!
# Lebesgue boundary dictionary on the actual historical fifth joint cell

`AffinePrimeWallReserve` already supplies a genuine arithmetic strip
reserve. We do not reproduce it or apply a null-wall assertion to prime
atoms. Here the nonzero own-cube linear form proves Lebesgue nullity of
the two actual old/new walls after restriction to the same T3 joint cell.
Only the fifth own-cube endpoint is closed: the parent region and the
original half-open ownership remain unchanged.

The sibling source-only dependency is intended to be installed as
`ImbalancedChen.P1HistoricalFifthPhysicalGateOverlap` upon integration.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators
open P1HistoricalFifthPhysicalGates

namespace P1HistoricalFifthAffineWallBoundary

/-- Nullity follows from a proved nonzero linear form, not a premise. -/
theorem ownCubeWall_volume_zero (lambda : ℝ) :
    volume {t : Fin 5 → ℝ | primeTupleOwnCubeForm t = lambda} = 0 := by
  simpa only [primeOwnCubeLinearForm_apply] using
    affinePrimeWall_volume_zero (primeOwnCubeLinearForm 4)
      (primeOwnCubeLinearForm_ne_zero 4) lambda

/-- Restriction to the genuine historical parent/owner does not enlarge
the null own-cube wall, even if this joint cell itself is empty. -/
theorem jointCell_ownCubeWall_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (jointCell D j ∩ {t | primeTupleOwnCubeForm t = lambda}) = 0 := by
  exact measure_mono_null inter_subset_right (ownCubeWall_volume_zero lambda)

/-- Both actual historical levels are retained, including when equal. -/
theorem historical_two_walls_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume ((jointCell D j ∩ {t | primeTupleOwnCubeForm t = (D.old5 j : ℝ)}) ∪
      (jointCell D j ∩ {t | primeTupleOwnCubeForm t = (D.cap5 j : ℝ)})) = 0 := by
  exact measure_union_null (jointCell_ownCubeWall_volume_zero D j _)
    (jointCell_ownCubeWall_volume_zero D j _)

/-- The pointwise closed-minus-strict wall proved in the sibling module
is now proved to have zero Lebesgue volume on this actual joint cell. -/
theorem closedOwnRegion_diff_physicalRegion_volume_zero
    (D : HistoricalPrefixCapData) (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (closedOwnRegion D j lambda \ physicalRegion D j lambda) = 0 := by
  rw [closedOwnRegion_diff_strict]
  exact jointCell_ownCubeWall_volume_zero D j lambda

theorem historical_both_closed_differences_volume_zero
    (D : HistoricalPrefixCapData) (j : Fin 5 → Fin (D.m + 1)) :
    volume ((closedOwnRegion D j (D.old5 j : ℝ) \ physicalRegion D j (D.old5 j : ℝ)) ∪
      (closedOwnRegion D j (D.cap5 j : ℝ) \ physicalRegion D j (D.cap5 j : ℝ))) = 0 := by
  exact measure_union_null (closedOwnRegion_diff_physicalRegion_volume_zero D j _)
    (closedOwnRegion_diff_physicalRegion_volume_zero D j _)

/-- This equivalence holds almost everywhere for Lebesgue volume. It is
not a pointwise equivalence and is not an arithmetic prime statement. -/
theorem ownCube_strict_iff_closed_ae (lambda : ℝ) :
    ∀ᵐ t : Fin 5 → ℝ ∂volume,
      primeTupleOwnCubeForm t < lambda ↔ primeTupleOwnCubeForm t ≤ lambda := by
  have hwall : ∀ᵐ t : Fin 5 → ℝ ∂volume, primeTupleOwnCubeForm t ≠ lambda := by
    rw [ae_iff]
    simpa only [not_not] using ownCubeWall_volume_zero lambda
  filter_upwards [hwall] with t ht
  constructor
  · exact fun h => h.le
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact hlt
    · exact (ht heq).elim

theorem physicalRegion_ae_closedOwnRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    physicalRegion D j lambda =ᵐ[volume] closedOwnRegion D j lambda := by
  filter_upwards [ownCube_strict_iff_closed_ae lambda] with t ht
  apply propext
  change (t ∈ jointCell D j ∧ primeTupleOwnCubeForm t < lambda) ↔
    (t ∈ jointCell D j ∧ primeTupleOwnCubeForm t ≤ lambda)
  exact and_congr Iff.rfl ht

theorem physicalRegion_volume_eq_closedOwnRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (physicalRegion D j lambda) = volume (closedOwnRegion D j lambda) := by
  exact measure_congr (physicalRegion_ae_closedOwnRegion D j lambda)

/-- The two level-specific restricted measures agree separately. -/
theorem historical_restrict_eq_closed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume.restrict (physicalRegion D j (D.old5 j : ℝ)) =
        volume.restrict (closedOwnRegion D j (D.old5 j : ℝ)) ∧
      volume.restrict (physicalRegion D j (D.cap5 j : ℝ)) =
        volume.restrict (closedOwnRegion D j (D.cap5 j : ℝ)) := by
  exact ⟨Measure.restrict_congr_set (physicalRegion_ae_closedOwnRegion D j _),
    Measure.restrict_congr_set (physicalRegion_ae_closedOwnRegion D j _)⟩

/-- A change of a null integration domain needs no positivity or cap
ordering assumption, and applies to each original profile separately. -/
theorem setIntegral_physicalRegion_eq_closedOwnRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) (f : (Fin 5 → ℝ) → ℝ) :
    (∫ t in physicalRegion D j lambda, f t) =
      ∫ t in closedOwnRegion D j lambda, f t := by
  exact setIntegral_congr_set (physicalRegion_ae_closedOwnRegion D j lambda)

/-- This closes each own-cube row at its own actual historical cap. -/
def closedPhysicalDifference (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) (t : Fin 5 → ℝ) : ℝ :=
  (closedOwnRegion D j (D.cap5 j : ℝ)).indicator newProfile t -
    (closedOwnRegion D j (D.old5 j : ℝ)).indicator oldProfile t

/-- Separate gates are preserved; their differences agree a.e. even
when the two profiles differ throughout the old/new overlap. -/
theorem physicalDifference_ae_closedPhysicalDifference (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) :
    physicalDifference D j oldProfile newProfile =ᵐ[volume]
      closedPhysicalDifference D j oldProfile newProfile := by
  filter_upwards [physicalRegion_ae_closedOwnRegion D j (D.old5 j : ℝ),
    physicalRegion_ae_closedOwnRegion D j (D.cap5 j : ℝ)] with t ho hn
  simp only [physicalDifference, closedPhysicalDifference, Set.indicator, ho, hn]

/-- The a.e. dictionary remains valid under restriction to the SAME
actual T3 parent and fifth owner, with an arbitrary common weight. -/
theorem weighted_difference_ae_on_jointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile weight : (Fin 5 → ℝ) → ℝ) :
    (fun t => physicalDifference D j oldProfile newProfile t * weight t) =ᵐ[
        volume.restrict (jointCell D j)]
      (fun t => closedPhysicalDifference D j oldProfile newProfile t * weight t) := by
  filter_upwards [ae_restrict_of_ae
    (physicalDifference_ae_closedPhysicalDifference D j oldProfile newProfile)] with t ht
  rw [ht]

theorem integral_weighted_difference_eq_closed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile weight : (Fin 5 → ℝ) → ℝ) :
    (∫ t in jointCell D j, physicalDifference D j oldProfile newProfile t * weight t) =
      ∫ t in jointCell D j, closedPhysicalDifference D j oldProfile newProfile t * weight t := by
  exact integral_congr_ae (weighted_difference_ae_on_jointCell D j oldProfile newProfile weight)

/-- The real historical fifth cell integral itself is the difference of
the two CLOSED-own-cube integrals. The original T3 joint cell is unchanged. -/
theorem fifthCellIntegral_eq_closed_region_integrals (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      (∫ t in closedOwnRegion D j (D.cap5 j : ℝ),
        primeTupleMinusProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i) -
      (∫ t in closedOwnRegion D j (D.old5 j : ℝ),
        primeTupleMinusProfile (D.old5 j : ℝ) t * ∏ i, 1 / t i) := by
  unfold HistoricalPrefixCapData.fifthCellIntegral
  simp only [primeOwnCubeIcoIntegral]
  rw [← physicalRegion_eq_affine D j (D.cap5 j : ℝ),
    ← physicalRegion_eq_affine D j (D.old5 j : ℝ)]
  rw [setIntegral_physicalRegion_eq_closedOwnRegion,
    setIntegral_physicalRegion_eq_closedOwnRegion]

/-- The genuine single-integral difference keeps two separate closed
own-cube indicators and the original two continuous residual profiles. -/
theorem fifthCellIntegral_eq_closed_profiles (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ t in jointCell D j,
        ((if primeTupleOwnCubeForm t ≤ (D.cap5 j : ℝ)
          then primeTupleMinusProfile (D.cap5 j : ℝ) t else 0) -
        (if primeTupleOwnCubeForm t ≤ (D.old5 j : ℝ)
          then primeTupleMinusProfile (D.old5 j : ℝ) t else 0)) * ∏ i, 1 / t i := by
  rw [D.fifthCellIntegral_eq_integral ha hab j]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ownCube_strict_iff_closed_ae (D.old5 j : ℝ)),
    ae_restrict_of_ae (ownCube_strict_iff_closed_ae (D.cap5 j : ℝ))] with t ho hn
  simp only [primeOwnCubeGatedProfile, ho, hn]

end P1HistoricalFifthAffineWallBoundary

end

end ImbalancedChen
