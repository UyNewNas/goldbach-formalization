import ImbalancedChen.HistoricalUpperFiveCellGeometry

/-!
# Historical fifth physical gates on the actual common T3 cell

The candidate domain has no fifth own-cube gate. Each residual attaches
its own strict physical gate to that same domain. In particular, a
new-minus-old residual need not vanish on the overlap of its two gates.
The boundary equalities below are pointwise set equalities, including at
arithmetic points; no null-set deletion is used.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set

namespace P1HistoricalFifthPhysicalGates

/-- The genuine fifth owner and its two actual historical parent tests. -/
def jointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

/-- This is a residual support gate, not a candidate-admission condition. -/
def physicalRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) : Set (Fin 5 → ℝ) :=
  jointCell D j ∩ {t | primeTupleOwnCubeForm t < lambda}

/-- Only the own-cube endpoint is closed. Parent tests stay strict. -/
def closedOwnRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) : Set (Fin 5 → ℝ) :=
  jointCell D j ∩ {t | primeTupleOwnCubeForm t ≤ lambda}

theorem mem_jointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ) :
    t ∈ jointCell D j ↔
      t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
      StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
        t 0 + t 1 + 3 * t 2 <
          (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ) := by
  rw [jointCell, Set.mem_inter_iff, D.mem_fifthParentGateRegion]

/-- All seven affine rows are literal physical tests; the last threshold
is independent of the root and third-ancestor thresholds. -/
theorem physicalRegion_eq_affine (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    physicalRegion D j lambda =
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
        primeAffineGateRegion (primeOwnCubeGateForms ordinaryUpperFiveGateForms)
          (primeOwnCubeGateBounds lambda (D.fifthParentGateBounds j)) := by
  ext t
  simp only [physicalRegion, jointCell, Set.mem_inter_iff, Set.mem_setOf_eq,
    mem_primeOwnCubeGateRegion]
  tauto

theorem physicalGateForms_ne_zero :
    ∀ i, primeOwnCubeGateForms ordinaryUpperFiveGateForms i ≠ 0 := by
  exact primeOwnCubeGateForms_ne_zero _ ordinaryUpperFiveGateForms_ne_zero

theorem physicalRegion_mono (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) {old new : ℝ} (h : old ≤ new) :
    physicalRegion D j old ⊆ physicalRegion D j new := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_le h⟩

/-- The two strict tests are not replaced by a test at the larger cap. -/
theorem physicalRegion_inter (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (old new : ℝ) :
    physicalRegion D j old ∩ physicalRegion D j new =
      physicalRegion D j (min old new) := by
  ext t
  simp only [physicalRegion, Set.mem_inter_iff, Set.mem_setOf_eq, lt_min_iff]
  tauto

/-- The old strict wall belongs to the newly admitted interval whenever
it lies strictly below the new cap. The new wall is still excluded. -/
theorem physicalRegion_diff (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (old new : ℝ) :
    physicalRegion D j new \ physicalRegion D j old =
      jointCell D j ∩
        {t | old ≤ primeTupleOwnCubeForm t ∧ primeTupleOwnCubeForm t < new} := by
  ext t
  simp only [physicalRegion, Set.mem_diff, Set.mem_inter_iff,
    Set.mem_setOf_eq, not_and, not_lt]
  tauto

theorem closedOwnRegion_diff_strict (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    closedOwnRegion D j lambda \ physicalRegion D j lambda =
      jointCell D j ∩ {t | primeTupleOwnCubeForm t = lambda} := by
  ext t
  constructor
  · rintro ⟨⟨hcell, hle⟩, hn⟩
    have hge : lambda ≤ primeTupleOwnCubeForm t := by
      apply le_of_not_gt
      intro hlt
      exact hn ⟨hcell, hlt⟩
    exact ⟨hcell, le_antisymm hle hge⟩
  · rintro ⟨hcell, heq⟩
    refine ⟨⟨hcell, heq.le⟩, ?_⟩
    intro ht
    exact (lt_irrefl lambda) (heq ▸ ht.2)

theorem own_wall_not_mem (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) {t : Fin 5 → ℝ}
    (ht : primeTupleOwnCubeForm t = lambda) :
    t ∉ physicalRegion D j lambda := by
  intro h
  exact (lt_irrefl lambda) (ht ▸ h.2)

/-- The comparison comes from the real selected historical cap table. -/
theorem old_region_subset_new (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    physicalRegion D j (D.old5 j : ℝ) ⊆ physicalRegion D j (D.cap5 j : ℝ) := by
  apply physicalRegion_mono
  exact_mod_cast (D.levelCheck_sound hcheck).2.2 j hj

theorem historical_overlap (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    physicalRegion D j (D.old5 j : ℝ) ∩ physicalRegion D j (D.cap5 j : ℝ) =
      physicalRegion D j (D.old5 j : ℝ) := by
  ext t
  constructor
  · exact fun ht => ht.1
  · exact fun ht => ⟨ht, old_region_subset_new D hcheck j hj ht⟩

theorem historical_new_only (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) :
    physicalRegion D j (D.cap5 j : ℝ) \ physicalRegion D j (D.old5 j : ℝ) =
      jointCell D j ∩ {t | (D.old5 j : ℝ) ≤ primeTupleOwnCubeForm t ∧
        primeTupleOwnCubeForm t < (D.cap5 j : ℝ)} := by
  exact physicalRegion_diff D j _ _

/-- At an actual old-cap wall, strict old rejection and strict new
admission coexist. No arithmetic boundary point is silently deleted. -/
theorem old_wall_mem_historical_new_only (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (hcap : D.old5 j < D.cap5 j)
    {t : Fin 5 → ℝ} (ht : t ∈ jointCell D j)
    (hwall : primeTupleOwnCubeForm t = (D.old5 j : ℝ)) :
    t ∈ physicalRegion D j (D.cap5 j : ℝ) \ physicalRegion D j (D.old5 j : ℝ) := by
  rw [historical_new_only]
  refine ⟨ht, hwall.ge, ?_⟩
  rw [hwall]
  exact_mod_cast hcap

/-- The difference retains both independent profiles on the overlap. -/
def physicalDifference (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) (t : Fin 5 → ℝ) : ℝ :=
  (physicalRegion D j (D.cap5 j : ℝ)).indicator newProfile t -
    (physicalRegion D j (D.old5 j : ℝ)).indicator oldProfile t

theorem physicalDifference_on_overlap (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) {t : Fin 5 → ℝ}
    (ht : t ∈ physicalRegion D j (D.old5 j : ℝ)) :
    physicalDifference D j oldProfile newProfile t = newProfile t - oldProfile t := by
  rw [physicalDifference, Set.indicator_of_mem
    (old_region_subset_new D hcheck j hj ht), Set.indicator_of_mem ht]

theorem physicalDifference_on_new_only (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1))
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) {t : Fin 5 → ℝ}
    (ht : t ∈ physicalRegion D j (D.cap5 j : ℝ) \
      physicalRegion D j (D.old5 j : ℝ)) :
    physicalDifference D j oldProfile newProfile t = newProfile t := by
  rw [physicalDifference, Set.indicator_of_mem ht.1,
    Set.indicator_of_notMem ht.2, sub_zero]

theorem physicalDifference_outside_new (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) {t : Fin 5 → ℝ}
    (ht : t ∉ physicalRegion D j (D.cap5 j : ℝ)) :
    physicalDifference D j oldProfile newProfile t = 0 := by
  have ho : t ∉ physicalRegion D j (D.old5 j : ℝ) :=
    fun h => ht (old_region_subset_new D hcheck j hj h)
  rw [physicalDifference, Set.indicator_of_notMem ht,
    Set.indicator_of_notMem ho, sub_self]

/-- This is support containment, not an assertion that the difference
vanishes on the old/new overlap. -/
theorem support_physicalDifference_subset (D : HistoricalPrefixCapData)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (oldProfile newProfile : (Fin 5 → ℝ) → ℝ) :
    Function.support (physicalDifference D j oldProfile newProfile) ⊆
      physicalRegion D j (D.cap5 j : ℝ) := by
  intro t ht
  by_contra hn
  exact ht (physicalDifference_outside_new D hcheck j hj oldProfile newProfile hn)

/-- The literal physical residual before its own strict cube indicator.
No analytic approximation or replacement profile is introduced here. -/
def actualUngatedResidual (N cap : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ) : ℝ :=
  actualSmallRosserMinusDensity N cap (p (Fin.last 4) : ℝ)
    ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) * Real.log (N : ℝ) / singularSeries N

/-- Both actual old/new own cubes, with the literal natural product and
their distinct quotient levels, are represented by their separate gates. -/
theorem actual_residual_difference_gate_dictionary (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (N cap : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    (if actualPrimeTupleLog N p ∈ jointCell D j then
      actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p else 0) =
      physicalDifference D j
        (fun _ => actualUngatedResidual N cap (D.old5 j : ℝ) p)
        (fun _ => actualUngatedResidual N cap (D.cap5 j : ℝ) p)
        (actualPrimeTupleLog N p) := by
  have ho := actualPrimeTupleOwnCube_iff hN p hpos (D.old5 j : ℝ)
  have hn := actualPrimeTupleOwnCube_iff hN p hpos (D.cap5 j : ℝ)
  by_cases hc : actualPrimeTupleLog N p ∈ jointCell D j <;>
    by_cases hgo : primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (D.old5 j : ℝ) <;>
    by_cases hgn : primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (D.cap5 j : ℝ) <;>
    simp [physicalDifference, physicalRegion, Set.indicator,
      actualPrimeTupleOwnCubeMinus, actualUngatedResidual, ho, hn, hc, hgo, hgn]

/-- The actual arithmetic filter agrees with the seven-row physical
region at every prime point, including all strict boundary values.
The initial frontier remains the common T3 rank-four frontier. -/
theorem frontier_cell_physical_filter (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (lambda : ℝ) :
    ((firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)).filter
        (fun p => (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 <
          (N : ℝ) ^ lambda) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ physicalRegion D j lambda) := by
  rw [historicalUpperFiveFrontierTuples_cell_filter D hab hold hcheck N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, hcell⟩, hcube⟩
    have hpos : ∀ i, 0 < p i :=
      fun i => ((mem_actualPrimeBoxTuples_iff.mp hp) i).1.pos
    exact ⟨hp, hcell, (actualPrimeTupleOwnCube_iff hN p hpos lambda).mp hcube⟩
  · rintro ⟨hp, hcell, hcube⟩
    have hpos : ∀ i, 0 < p i :=
      fun i => ((mem_actualPrimeBoxTuples_iff.mp hp) i).1.pos
    exact ⟨⟨hp, hcell⟩, (actualPrimeTupleOwnCube_iff hN p hpos lambda).mpr hcube⟩

end P1HistoricalFifthPhysicalGates

end

end ImbalancedChen
