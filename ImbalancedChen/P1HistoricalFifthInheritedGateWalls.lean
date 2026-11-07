import ImbalancedChen.P1HistoricalFifthAffineWallBoundary

/-!
# Complete continuous boundary dictionary for the historical fifth cell

The original arithmetic owner remains Ico and all six parent gates stay
strict in `jointCell`. Here their continuous integral domains may be
replaced by the explicitly closed mesh/parent region. The actual root
cap and the effective third-ancestor cap are kept different, as are the
two fifth residual caps. All exceptions lie in a displayed finite family
of genuine nonzero affine hyperplanes. No prime atom is deleted.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators
open P1HistoricalFifthPhysicalGates P1HistoricalFifthAffineWallBoundary

namespace P1HistoricalFifthInheritedGateWalls

/-- The root wall uses the original root cap, not the third cap. -/
theorem root_inherited_wall_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume {t : Fin 5 → ℝ | 3 * t 0 = (D.old : ℝ)} = 0 := by
  simpa [ordinaryUpperFiveGateForms, HistoricalPrefixCapData.fifthParentGateBounds] using
    affinePrimeWall_volume_zero (ordinaryUpperFiveGateForms 4)
      (ordinaryUpperFiveGateForms_ne_zero 4) (D.fifthParentGateBounds j 4)

/-- This threshold is the SAME fifth owner's effective selected third
ancestor, including its inherited fallback. -/
theorem third_inherited_wall_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume {t : Fin 5 → ℝ | t 0 + t 1 + 3 * t 2 =
      (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)} = 0 := by
  simpa [ordinaryUpperFiveGateForms, HistoricalPrefixCapData.fifthParentGateBounds] using
    affinePrimeWall_volume_zero (ordinaryUpperFiveGateForms 5)
      (ordinaryUpperFiveGateForms_ne_zero 5) (D.fifthParentGateBounds j 5)

/-- The finite exceptional set includes both mesh faces at every
coordinate and all six actual parent walls, including order walls. -/
def parentMeshWalls (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  {t | ∃ i : Fin 5,
    t i = logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j i ∨
    t i = logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i} ∪
  {t | ∃ r : Fin 6, ordinaryUpperFiveGateForms r t = D.fifthParentGateBounds j r}

private theorem coordinateForm_ne_zero (i : Fin 5) :
    (ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ) ≠ 0 := by
  intro h
  have hh := congrArg (fun F : (Fin 5 → ℝ) →L[ℝ] ℝ => F (fun _ => 1)) h
  norm_num at hh

theorem ae_not_mem_parentMeshWalls (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    ∀ᵐ t ∂volume, t ∉ parentMeshWalls D j := by
  have hlo := ae_primeAffineGate_no_wall
    (fun i : Fin 5 => (ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ))
    (logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j) coordinateForm_ne_zero
  have hhi := ae_primeAffineGate_no_wall
    (fun i : Fin 5 => (ContinuousLinearMap.proj i : (Fin 5 → ℝ) →L[ℝ] ℝ))
    (logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j) coordinateForm_ne_zero
  have hp := ae_primeAffineGate_no_wall ordinaryUpperFiveGateForms
    (D.fifthParentGateBounds j) ordinaryUpperFiveGateForms_ne_zero
  filter_upwards [hlo, hhi, hp] with t htl hth htp
  change ¬((∃ i : Fin 5,
    t i = logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j i ∨
    t i = logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i) ∨
    ∃ r : Fin 6, ordinaryUpperFiveGateForms r t = D.fifthParentGateBounds j r)
  rintro (⟨i, heq | heq⟩ | ⟨r, heq⟩)
  · exact htl i heq
  · exact hth i heq
  · exact htp r heq

theorem parentMeshWalls_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : volume (parentMeshWalls D j) = 0 := by
  have h := ae_not_mem_parentMeshWalls D j
  rw [ae_iff] at h
  simpa only [not_not] using h

def closedMeshCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  {t | ∀ i, logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j i ≤ t i ∧
    t i ≤ logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j i}

def closedParentRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  {t | ∀ r, ordinaryUpperFiveGateForms r t ≤ D.fifthParentGateBounds j r}

/-- Explicitly identifies both actual weak inherited tests and all four
order rows; no ordinary common-cap parent is substituted. -/
theorem mem_closedParentRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ) :
    t ∈ closedParentRegion D j ↔
      t 1 ≤ t 0 ∧ t 2 ≤ t 1 ∧ t 3 ≤ t 2 ∧ t 4 ≤ t 3 ∧
        3 * t 0 ≤ (D.old : ℝ) ∧ t 0 + t 1 + 3 * t 2 ≤
          (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  simp [closedParentRegion, ordinaryUpperFiveGateForms,
    HistoricalPrefixCapData.fifthParentGateBounds, Fin.forall_fin_succ, and_assoc]

def closedJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  closedMeshCell D j ∩ closedParentRegion D j

theorem jointCell_subset_closedJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : jointCell D j ⊆ closedJointCell D j := by
  intro t ht
  refine ⟨?_, fun r => (ht.2 r).le⟩
  intro i
  have hi := mem_logPrimeMeshCell.mp ht.1 i
  exact ⟨hi.1, hi.2.le⟩

theorem mem_jointCell_iff_closed_of_no_wall (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) {t : Fin 5 → ℝ}
    (hw : t ∉ parentMeshWalls D j) :
    t ∈ jointCell D j ↔ t ∈ closedJointCell D j := by
  constructor
  · exact fun ht => jointCell_subset_closedJointCell D j ht
  · intro ht
    refine ⟨mem_logPrimeMeshCell.mpr (fun i => ?_), fun r => ?_⟩
    · refine ⟨(ht.1 i).1, lt_of_le_of_ne (ht.1 i).2 ?_⟩
      intro heq
      exact hw (Or.inl ⟨i, Or.inr heq⟩)
    · apply lt_of_le_of_ne (ht.2 r)
      intro heq
      exact hw (Or.inr ⟨r, heq⟩)

/-- The actual pointwise discrepancy is confined to the displayed finite
hyperplanes. This is proved before deriving any a.e. replacement. -/
theorem closedJointCell_diff_subset_walls (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    closedJointCell D j \ jointCell D j ⊆ parentMeshWalls D j := by
  intro t ht
  by_contra hw
  exact ht.2 ((mem_jointCell_iff_closed_of_no_wall D j hw).mpr ht.1)

theorem closedJointCell_diff_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume (closedJointCell D j \ jointCell D j) = 0 := by
  exact measure_mono_null (closedJointCell_diff_subset_walls D j)
    (parentMeshWalls_volume_zero D j)

theorem jointCell_ae_closedJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : jointCell D j =ᵐ[volume] closedJointCell D j := by
  filter_upwards [ae_not_mem_parentMeshWalls D j] with t ht
  exact propext (mem_jointCell_iff_closed_of_no_wall D j ht)

theorem integral_jointCell_eq_closedJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (f : (Fin 5 → ℝ) → ℝ) :
    (∫ t in jointCell D j, f t) = ∫ t in closedJointCell D j, f t := by
  exact setIntegral_congr_set (jointCell_ae_closedJointCell D j)

def fullClosedPhysicalRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) : Set (Fin 5 → ℝ) :=
  closedJointCell D j ∩ {t | primeTupleOwnCubeForm t ≤ lambda}

def fullBoundaryWalls (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) : Set (Fin 5 → ℝ) :=
  parentMeshWalls D j ∪ {t | primeTupleOwnCubeForm t = lambda}

theorem physicalRegion_subset_fullClosed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    physicalRegion D j lambda ⊆ fullClosedPhysicalRegion D j lambda := by
  intro t ht
  exact ⟨jointCell_subset_closedJointCell D j ht.1, ht.2.le⟩

theorem fullBoundaryWalls_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (fullBoundaryWalls D j lambda) = 0 := by
  exact measure_union_null (parentMeshWalls_volume_zero D j) (ownCubeWall_volume_zero lambda)

theorem fullClosedPhysicalRegion_diff_subset_walls (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    fullClosedPhysicalRegion D j lambda \ physicalRegion D j lambda ⊆
      fullBoundaryWalls D j lambda := by
  intro t ht
  by_contra hw
  have hp : t ∉ parentMeshWalls D j := fun h => hw (Or.inl h)
  have ho : primeTupleOwnCubeForm t ≠ lambda := fun h => hw (Or.inr h)
  exact ht.2 ⟨(mem_jointCell_iff_closed_of_no_wall D j hp).mpr ht.1.1,
    lt_of_le_of_ne ht.1.2 ho⟩

theorem fullClosedPhysicalRegion_diff_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (fullClosedPhysicalRegion D j lambda \ physicalRegion D j lambda) = 0 := by
  exact measure_mono_null (fullClosedPhysicalRegion_diff_subset_walls D j lambda)
    (fullBoundaryWalls_volume_zero D j lambda)

theorem closedOwnRegion_ae_fullClosedPhysicalRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    closedOwnRegion D j lambda =ᵐ[volume] fullClosedPhysicalRegion D j lambda := by
  filter_upwards [jointCell_ae_closedJointCell D j] with t ht
  change (t ∈ jointCell D j ∧ primeTupleOwnCubeForm t ≤ lambda) =
    (t ∈ closedJointCell D j ∧ primeTupleOwnCubeForm t ≤ lambda)
  rw [ht]

theorem physicalRegion_ae_fullClosedPhysicalRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    physicalRegion D j lambda =ᵐ[volume] fullClosedPhysicalRegion D j lambda := by
  exact (physicalRegion_ae_closedOwnRegion D j lambda).trans
    (closedOwnRegion_ae_fullClosedPhysicalRegion D j lambda)

theorem physicalRegion_volume_eq_fullClosed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    volume (physicalRegion D j lambda) = volume (fullClosedPhysicalRegion D j lambda) := by
  exact measure_congr (physicalRegion_ae_fullClosedPhysicalRegion D j lambda)

/-- The complete old/new boundary reserve uses their actual distinct
levels and the SAME historical root/third-parent/owner walls. -/
theorem historical_complete_boundary_volume_zero (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    volume (fullBoundaryWalls D j (D.old5 j : ℝ) ∪
      fullBoundaryWalls D j (D.cap5 j : ℝ)) = 0 := by
  exact measure_union_null (fullBoundaryWalls_volume_zero D j _)
    (fullBoundaryWalls_volume_zero D j _)

theorem integral_physicalRegion_eq_fullClosed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) (f : (Fin 5 → ℝ) → ℝ) :
    (∫ t in physicalRegion D j lambda, f t) =
      ∫ t in fullClosedPhysicalRegion D j lambda, f t := by
  exact setIntegral_congr_set (physicalRegion_ae_fullClosedPhysicalRegion D j lambda)

/-- Complete closure of owner, all parent gates and each own cube,
retaining the two independent profiles even on their overlap. -/
theorem physicalDifference_ae_fullClosedDifference (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) :
    physicalDifference D j oldProfile newProfile =ᵐ[volume]
      (fun t => (fullClosedPhysicalRegion D j (D.cap5 j : ℝ)).indicator newProfile t -
        (fullClosedPhysicalRegion D j (D.old5 j : ℝ)).indicator oldProfile t) := by
  filter_upwards [physicalRegion_ae_fullClosedPhysicalRegion D j (D.old5 j : ℝ),
    physicalRegion_ae_fullClosedPhysicalRegion D j (D.cap5 j : ℝ)] with t ho hn
  simp only [physicalDifference, Set.indicator, ho, hn]

theorem integral_weighted_physicalDifference_eq_fullClosed (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile weight : (Fin 5 → ℝ) → ℝ) :
    (∫ t, physicalDifference D j oldProfile newProfile t * weight t) =
      ∫ t, ((fullClosedPhysicalRegion D j (D.cap5 j : ℝ)).indicator newProfile t -
        (fullClosedPhysicalRegion D j (D.old5 j : ℝ)).indicator oldProfile t) * weight t := by
  apply integral_congr_ae
  filter_upwards [physicalDifference_ae_fullClosedDifference D j oldProfile newProfile] with t ht
  rw [ht]

/-- The existing genuine fifth integral can therefore use the complete
closed historical regions, with every original threshold/profile intact. -/
theorem fifthCellIntegral_eq_fullClosed_region_integrals (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      (∫ t in fullClosedPhysicalRegion D j (D.cap5 j : ℝ),
        primeTupleMinusProfile (D.cap5 j : ℝ) t * ∏ i, 1 / t i) -
      (∫ t in fullClosedPhysicalRegion D j (D.old5 j : ℝ),
        primeTupleMinusProfile (D.old5 j : ℝ) t * ∏ i, 1 / t i) := by
  rw [fifthCellIntegral_eq_closed_region_integrals]
  exact congrArg₂ (fun x y : ℝ => x - y)
    (setIntegral_congr_set (closedOwnRegion_ae_fullClosedPhysicalRegion D j (D.cap5 j : ℝ)))
    (setIntegral_congr_set (closedOwnRegion_ae_fullClosedPhysicalRegion D j (D.old5 j : ℝ)))

/-- A single complete closed-cell formula also keeps the old and new
own-cube indicators separate; the inherited parent cap is unchanged. -/
theorem fifthCellIntegral_eq_fullClosed_profiles (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ t in closedJointCell D j,
        ((if primeTupleOwnCubeForm t ≤ (D.cap5 j : ℝ)
          then primeTupleMinusProfile (D.cap5 j : ℝ) t else 0) -
        (if primeTupleOwnCubeForm t ≤ (D.old5 j : ℝ)
          then primeTupleMinusProfile (D.old5 j : ℝ) t else 0)) * ∏ i, 1 / t i := by
  exact (fifthCellIntegral_eq_closed_profiles D ha hab j).trans
    (integral_jointCell_eq_closedJointCell D j _)

end P1HistoricalFifthInheritedGateWalls

end

end ImbalancedChen
