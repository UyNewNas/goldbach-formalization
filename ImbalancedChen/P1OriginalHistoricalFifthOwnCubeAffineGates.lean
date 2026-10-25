import ImbalancedChen.P1OriginalCoarseFifthJointGeometry
import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.P1OriginalCoarseFifthResidualDictionary

/-!
# Original historical fifth residual affine gates

The candidate parent is the actual first-stop coarse T3 policy. On an
actually selected fifth owner its current third cap is Gamma-2e; old5
is the complete projected-fourth lookup, either cap4 or its true Gamma
fallback. New and old residuals attach distinct strict own-cube rows.
Neither row changes candidate enumeration. No first-cube or firstStop
condition is removed, and no initial-to-third comparison is assumed.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators

namespace HistoricalThirdCoarse.P1OriginalCoarseFifth

theorem measurableSet_firstLabelRegion (e : ℝ) (m : ℕ) :
    MeasurableSet (firstLabelRegion e m) := by
  have heq : firstLabelRegion e m =
      ⋃ i : Fin (m + 1), {t : Fin 5 → ℝ |
        logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0 ∧
        t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
        logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ VariableEnvelope.extendedFirstStop - 4 * e} := by
    ext t
    simp only [firstLabelRegion, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  by_cases hs : logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤
      VariableEnvelope.extendedFirstStop - 4 * e
  · have hlo : MeasurableSet {t : Fin 5 → ℝ |
        logPrimeMeshPoint 0 (19 / 96) m i.val ≤ t 0} :=
      measurableSet_le measurable_const (measurable_pi_apply 0)
    have hhi : MeasurableSet {t : Fin 5 → ℝ |
        t 0 < logPrimeMeshPoint 0 (19 / 96) m (i.val + 1)} :=
      measurableSet_lt (measurable_pi_apply 0) measurable_const
    simpa only [hs, and_true] using hlo.inter hhi
  · simp only [hs, and_false, Set.setOf_false, measurableSet_empty]

theorem measurableSet_activeRegion (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : MeasurableSet (activeRegion e chi m omega j) := by
  exact (measurableSet_firstLabelRegion e m).inter
    ((measurableSet_primeAffineGateRegion _ _).inter
      (measurableSet_le measurable_const (measurable_pi_apply 2)))

theorem measurableSet_inactiveRegion (e : ℝ) (m : ℕ) (omega : ℝ) :
    MeasurableSet (inactiveRegion e m omega) := by
  exact (measurableSet_firstLabelRegion e m).inter
    ((measurableSet_primeAffineGateRegion _ _).inter
      (measurableSet_lt (measurable_pi_apply 2) measurable_const))

theorem jointRegion_eq_active_union_inactive (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) :
    jointRegion e chi m omega j = activeRegion e chi m omega j ∪ inactiveRegion e m omega := by
  ext t
  constructor
  · intro ht
    by_cases hr : omega ≤ t 2
    · exact Or.inl ((jointRegion_active_iff e chi m omega j t).mp ⟨ht, hr⟩)
    · exact Or.inr ((jointRegion_inactive_iff e chi m omega j t).mp ⟨ht, hr⟩)
  · rintro (ht | ht)
    · exact ((jointRegion_active_iff e chi m omega j t).mpr ht).1
    · exact ((jointRegion_inactive_iff e chi m omega j t).mpr ht).1

/-- The real piecewise raw-third region is measurable without replacing
it prematurely by one constant selected cap. -/
theorem measurableSet_jointRegion (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) : MeasurableSet (jointRegion e chi m omega j) := by
  rw [jointRegion_eq_active_union_inactive]
  exact (measurableSet_activeRegion e chi m omega j).union
    (measurableSet_inactiveRegion e m omega)

end HistoricalThirdCoarse.P1OriginalCoarseFifth

namespace P1OriginalHistoricalFifthOwnCubeAffineGates

open HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalCoarseFifthContinuation

/-- Actual whole-cell activation, proved from the selected fifth label. -/
theorem selected_cell_rough (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) : omega ≤ t 2 := by
  have hc := (mem_selectedFifthCells e chi m omega J5 j).mp hj
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht
  have hlo := (mem_logPrimeMeshCell.mp ht3 (2 : Fin 3)).1
  have hreal : (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 5) j) 2 : ℝ) ≤ t 2 := by
    rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 5) j)) 2]
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat, historicalPrefixProject] using hlo
  exact hc.2.2.trans hreal

/-- Current third cap is the original selected Gamma-2e on this SAME
owner. The firstStop and initial first cube are not discarded. -/
theorem selected_currentExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    currentExponent (e : ℝ) chi m omega j t = levelExponent (e : ℝ) (box m (thirdOwner j)) := by
  have hr := selected_cell_rough e chi m omega J5 j hj ht
  have hc : thirdOwner j ∈ cells (e : ℝ) chi m :=
    ((mem_selectedFifthCells e chi m omega J5 j).mp hj).2.1
  simp only [currentExponent, if_pos hr, thirdCellExponent, if_pos hc]

theorem jointRegion_on_selected_cell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    t ∈ jointRegion (e : ℝ) chi m omega j ↔ t ∈ selectedRegion (e : ℝ) m omega j := by
  have hr := selected_cell_rough e chi m omega J5 j hj ht
  have hc : thirdOwner j ∈ cells (e : ℝ) chi m :=
    ((mem_selectedFifthCells e chi m omega J5 j).mp hj).2.1
  have hh := jointRegion_active_iff (e : ℝ) chi m omega j t
  rw [activeRegion_eq_selected (e : ℝ) chi m omega j hc] at hh
  simpa only [hr, and_true] using hh

def parentBounds (e : ℚ) (m : ℕ) (j : Label5 m) : Fin 7 → ℝ :=
  historicalUnorderedThirdGateBounds (initial (e : ℝ))
    (levelExponent (e : ℝ) (box m (thirdOwner j)))

def ownCubeForms : Fin 8 → (Fin 5 → ℝ) →L[ℝ] ℝ :=
  primeOwnCubeGateForms historicalUnorderedThirdGateForms

def ownCubeBounds (e : ℚ) (m : ℕ) (j : Label5 m) (lambda : ℝ) : Fin 8 → ℝ :=
  primeOwnCubeGateBounds lambda (parentBounds e m j)

theorem ownCubeForms_ne_zero : ∀ r, ownCubeForms r ≠ 0 := by
  exact primeOwnCubeGateForms_ne_zero _ historicalUnorderedThirdGateForms_ne_zero

def candidateCell (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m) : Set (Fin 5 → ℝ) :=
  logPrimeMeshCell 0 (19 / 96) m j ∩ selectedRegion (e : ℝ) m omega j

def physicalCell (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m) (lambda : ℝ) :
    Set (Fin 5 → ℝ) := candidateCell e m omega j ∩ {t | primeTupleOwnCubeForm t < lambda}

/-- The complete literal firstStop, rough activation and both parent
first cubes survive when one independently frozen own cube is attached. -/
theorem physicalCell_eq_affine (e : ℚ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) (lambda : ℝ) :
    physicalCell e m omega j lambda =
      logPrimeMeshCell 0 (19 / 96) m j ∩
        (firstLabelRegion (e : ℝ) m ∩ ({t | omega ≤ t 2} ∩
          primeAffineGateRegion ownCubeForms (ownCubeBounds e m j lambda))) := by
  ext t
  simp only [physicalCell, candidateCell, selectedRegion, parentBounds, ownCubeForms,
    ownCubeBounds, Set.mem_inter_iff, Set.mem_setOf_eq, mem_primeOwnCubeGateRegion]
  tauto

theorem mem_physicalCell (e : ℚ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) (lambda : ℝ) (t : Fin 5 → ℝ) :
    t ∈ physicalCell e m omega j lambda ↔
      t ∈ logPrimeMeshCell 0 (19 / 96) m j ∧ t ∈ firstLabelRegion (e : ℝ) m ∧
        StrictAnti t ∧ 3 * t 0 < initial (e : ℝ) ∧
        3 * t 0 < levelExponent (e : ℝ) (box m (thirdOwner j)) ∧
        t 0 + t 1 + 3 * t 2 < levelExponent (e : ℝ) (box m (thirdOwner j)) ∧
        omega ≤ t 2 ∧ primeTupleOwnCubeForm t < lambda := by
  simp only [physicalCell, candidateCell, selectedRegion, Set.mem_inter_iff,
    Set.mem_setOf_eq, mem_historicalUnorderedThirdGateRegion]
  tauto

/-- The stored old5 is exactly projected cap4 or the original Gamma-2e,
never the unrelated initial Theta cap or an ordinary constant D.old. -/
theorem old5_eq_projected_cap4_or_gamma (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ) (j : Label5 m) :
    (old5 e chi m omega J4 cap4 j : ℝ) =
      if historicalPrefixProject (by omega : 4 ≤ 5) j ∈
          P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4 then
        (cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) : ℝ)
      else levelExponent (e : ℝ) (box m (thirdOwner j)) := by
  unfold old5
  split_ifs
  · rfl
  · rw [P1OriginalCoarseContinuation.cast_thirdCellExponent]
    simp only [historicalPrefixProject_comp, thirdOwner]

theorem old4_level_on_selected_fifth_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (N : ℝ) (pre : List ℕ) (hN : 1 < N)
    (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 N (rosserAncestor 4 pre) =
      N ^ (old5 e chi m omega J4 cap4 j : ℝ) := by
  change N ^ (P1OriginalCoarseContinuation.effectiveExponent4Q e chi m omega J4 cap4 N
      (rosserAncestor 4 pre) : ℝ) = _
  rw [inherited_fourth_on_selected_fifth_cell e chi m omega J4 cap4 J5 N pre
    hN hlen hpos j hj ht]

/-- The NEW actual historical level retains its own strict physical cube. -/
theorem new5_ownCube_iff_log (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 <
        level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ) (P1OriginalCoarseFifthResidual.tupleHistory p) ↔
      primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (cap5 j : ℝ) := by
  rw [level5_on_selected_cell e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    (P1OriginalCoarseFifthResidual.tupleHistory p)
    (by simp [P1OriginalCoarseFifthResidual.tupleHistory]) j hj
    (by simpa only [P1OriginalCoarseFifthResidual.tupleHistory_log] using ht)]
  exact actualPrimeTupleOwnCube_iff hN p hpos _

/-- The OLD actual fourth ancestor has a different threshold and its own
strict physical cube. Passing the new gate does not supply this one. -/
theorem old4_ownCube_iff_log (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 <
        P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)
          (rosserAncestor 4 (P1OriginalCoarseFifthResidual.tupleHistory p)) ↔
      primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (old5 e chi m omega J4 cap4 j : ℝ) := by
  rw [old4_level_on_selected_fifth_cell e chi m omega J4 cap4 J5 (N : ℝ)
    (P1OriginalCoarseFifthResidual.tupleHistory p) (by exact_mod_cast hN)
    (by simp [P1OriginalCoarseFifthResidual.tupleHistory])
    (P1OriginalCoarseFifthResidual.tupleHistory_pos p hpos) j hj
    (by simpa only [P1OriginalCoarseFifthResidual.tupleHistory_log] using ht)]
  exact actualPrimeTupleOwnCube_iff hN p hpos _

def ungatedMinus (N cap : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ) : ℝ :=
  actualSmallRosserMinusDensity N cap (p (Fin.last 4) : ℝ)
    ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) * Real.log (N : ℝ) / singularSeries N

/-- Literal actual old/new minus residuals, with independent strict
affine admissions and independent physical quotient levels. -/
theorem actual_minus_difference_on_selected_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference
        e chi m omega J4 cap4 J5 cap5 N cap p =
      (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (cap5 j : ℝ)
        then ungatedMinus N cap (cap5 j : ℝ) p else 0) -
      (if primeTupleOwnCubeForm (actualPrimeTupleLog N p) < (old5 e chi m omega J4 cap4 j : ℝ)
        then ungatedMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0) := by
  rw [P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference_on_cell
    e chi m omega J4 cap4 J5 cap5 N cap hN p hpos j hj ht]
  have hn := actualPrimeTupleOwnCube_iff hN p hpos (cap5 j : ℝ)
  have ho := actualPrimeTupleOwnCube_iff hN p hpos (old5 e chi m omega J4 cap4 j : ℝ)
  simp only [actualPrimeTupleOwnCubeMinus, ungatedMinus, hn, ho]

theorem physicalCell_mono (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    {old new : ℝ} (h : old ≤ new) : physicalCell e m omega j old ⊆ physicalCell e m omega j new := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_le h⟩

theorem physicalCell_inter (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m) (old new : ℝ) :
    physicalCell e m omega j old ∩ physicalCell e m omega j new =
      physicalCell e m omega j (min old new) := by
  ext t
  simp only [physicalCell, Set.mem_inter_iff, Set.mem_setOf_eq, lt_min_iff]
  tauto

theorem physicalCell_diff (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m) (old new : ℝ) :
    physicalCell e m omega j new \ physicalCell e m omega j old =
      candidateCell e m omega j ∩
        {t | old ≤ primeTupleOwnCubeForm t ∧ primeTupleOwnCubeForm t < new} := by
  ext t
  simp only [physicalCell, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_lt]
  tauto

theorem old_region_subset_new_of_check (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ) ⊆
      physicalCell e m omega j (cap5 j : ℝ) := by
  apply physicalCell_mono
  exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 hcheck j hj

/-- The old equality wall is INCLUDED in the new-only interval, while
the new equality wall remains excluded. No boundary point is erased. -/
theorem historical_new_only (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) :
    physicalCell e m omega j (cap5 j : ℝ) \
        physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ) =
      candidateCell e m omega j ∩
        {t | (old5 e chi m omega J4 cap4 j : ℝ) ≤ primeTupleOwnCubeForm t ∧
          primeTupleOwnCubeForm t < (cap5 j : ℝ)} := by
  exact physicalCell_diff e m omega j _ _

def weakOwnCell (e : ℚ) (m : ℕ) (omega : ℝ) (j : Label5 m) (lambda : ℝ) :
    Set (Fin 5 → ℝ) := candidateCell e m omega j ∩ {t | primeTupleOwnCubeForm t ≤ lambda}

theorem weakOwnCell_diff_strict_eq_wall (e : ℚ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) (lambda : ℝ) :
    weakOwnCell e m omega j lambda \ physicalCell e m omega j lambda =
      candidateCell e m omega j ∩ {t | primeTupleOwnCubeForm t = lambda} := by
  ext t
  constructor
  · rintro ⟨⟨hc, hle⟩, hn⟩
    have hge : lambda ≤ primeTupleOwnCubeForm t := by
      apply le_of_not_gt
      intro hlt
      exact hn ⟨hc, hlt⟩
    exact ⟨hc, le_antisymm hle hge⟩
  · rintro ⟨hc, heq⟩
    exact ⟨⟨hc, heq.le⟩, fun ht => (lt_irrefl lambda) (heq ▸ ht.2)⟩

/-- Candidate enumeration remains the original complete T3 frontier;
whole-cell activation has been proved, not assumed for each prime. -/
theorem candidates_on_selected_fifth_cell_filter
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    (candidates (e : ℝ) chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈ candidateCell e m omega j) := by
  rw [candidates_cell_filter (e : ℝ) chi m omega N cap hN hcap j]
  ext p
  simp only [Finset.mem_filter, candidateCell, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, ht, hg⟩
    exact ⟨hp, ht, (jointRegion_on_selected_cell e chi m omega J5 j hj ht).mp hg⟩
  · rintro ⟨hp, ht, hg⟩
    exact ⟨hp, ht, (jointRegion_on_selected_cell e chi m omega J5 j hj ht).mpr hg⟩

/-- Ico ownership fixes the first coarse label uniquely. This is an exact
conditional dictionary, not an assertion that firstStop can be ignored. -/
theorem firstLabelRegion_on_cell (e : ℝ) (m : ℕ) (j : Label5 m) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    t ∈ firstLabelRegion e m ↔
      logPrimeMeshHi 0 (19 / 96) m j 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e := by
  constructor
  · rintro ⟨i, hlo, hhi, hstop⟩
    have hown : (fun _ : Fin 1 => i) = (fun _ : Fin 1 => j 0) := by
      apply logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
        (x := fun _ : Fin 1 => t 0)
      · apply mem_logPrimeMeshCell.mpr
        intro q
        fin_cases q
        exact ⟨hlo, hhi⟩
      · apply mem_logPrimeMeshCell.mpr
        intro q
        fin_cases q
        exact mem_logPrimeMeshCell.mp ht 0
    have hi : i = j 0 := congrFun hown 0
    rw [hi] at hstop
    simpa only [logPrimeMeshHi] using hstop
  · intro hs
    have ht0 := mem_logPrimeMeshCell.mp ht 0
    exact ⟨j 0, ht0.1, ht0.2, hs⟩

def firstStopCellCheck (e : ℝ) (m : ℕ) (j : Label5 m) : Bool :=
  decide (logPrimeMeshHi 0 (19 / 96) m j 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e)

theorem firstStopCellCheck_iff (e : ℝ) (m : ℕ) (j : Label5 m) :
    firstStopCellCheck e m j = true ↔
      logPrimeMeshHi 0 (19 / 96) m j 0 ≤ VariableEnvelope.extendedFirstStop - 4 * e := by
  simp only [firstStopCellCheck, decide_eq_true_eq]

/-- A genuine selected fifth cell supplies whole-cell rough activation.
The firstStop check remains as a true/false guard; all three parent cubes
remain in the constant affine family. No e/chi smallness is assumed. -/
theorem candidateCell_eq_if (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) :
    candidateCell e m omega j =
      if firstStopCellCheck (e : ℝ) m j = true then
        logPrimeMeshCell 0 (19 / 96) m j ∩
          primeAffineGateRegion historicalUnorderedThirdGateForms (parentBounds e m j)
      else ∅ := by
  by_cases hs : firstStopCellCheck (e : ℝ) m j = true
  · rw [if_pos hs]
    ext t
    constructor
    · rintro ⟨ht, hfirst, hgate, _hrough⟩
      exact ⟨ht, hgate⟩
    · rintro ⟨ht, hgate⟩
      have hfirst := (firstLabelRegion_on_cell (e : ℝ) m j t ht).mpr
        ((firstStopCellCheck_iff (e : ℝ) m j).mp hs)
      exact ⟨ht, hfirst, hgate, selected_cell_rough e chi m omega J5 j hj ht⟩
  · rw [if_neg hs]
    ext t
    constructor
    · rintro ⟨ht, hfirst, _hgate, _hrough⟩
      have hh := (firstStopCellCheck_iff (e : ℝ) m j).mpr
        ((firstLabelRegion_on_cell (e : ℝ) m j t ht).mp hfirst)
      exact (hs hh).elim
    · intro ht
      exact ht.elim

/-- Ready for the genuine eight-row own-cube Ico supplier. The original
firstStop false branch is explicitly empty, rather than assumed away. -/
theorem physicalCell_eq_if_affine (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ selectedFifthCells e chi m omega J5) (lambda : ℝ) :
    physicalCell e m omega j lambda =
      if firstStopCellCheck (e : ℝ) m j = true then
        logPrimeMeshCell 0 (19 / 96) m j ∩
          primeAffineGateRegion ownCubeForms (ownCubeBounds e m j lambda)
      else ∅ := by
  rw [physicalCell, candidateCell_eq_if e chi m omega J5 j hj]
  by_cases hs : firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ownCubeForms, ownCubeBounds,
      mem_primeOwnCubeGateRegion]
    tauto
  · simp only [if_neg hs, Set.empty_inter]

/-- Lower truncation is explicit and does not alter the original coarse
carrier, firstStop, raw-Q3 or any of the three parent cubes. -/
theorem truncated_candidates_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) (a : ℝ) :
    (candidates e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
          actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ))) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∩
          jointRegion e chi m omega j) := by
  ext p
  simp only [Finset.mem_filter, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, ht, hbox⟩
    have hg := (mem_candidates_iff_log_on_cell e chi m omega N cap hN hcap p j ht).mp hp
    exact ⟨(mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨fun i => ⟨(hg.1 i).1, (hg.1 i).2.1⟩, hbox⟩, ht, hg.2⟩
  · rintro ⟨hp, ht, hg⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hbox := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
    exact ⟨(mem_candidates_iff_log_on_cell e chi m omega N cap hN hcap p j ht).mpr
      ⟨fun i => ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩, hg⟩, ht, hbox⟩

/-- Positive-box candidate identity with the original stop guard and the
actual constant selected-third bounds, ready for a prime Ico limit. -/
theorem truncated_selected_candidates_filter_eq_if
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) (a : ℝ) :
    (candidates (e : ℝ) chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
          actualPrimeTupleLog N p ∈ logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ))) =
      if firstStopCellCheck (e : ℝ) m j = true then
        (actualPrimeBoxTuples N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))).filter
          (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j ∩
            primeAffineGateRegion historicalUnorderedThirdGateForms (parentBounds e m j))
      else ∅ := by
  rw [truncated_candidates_filter (e : ℝ) chi m omega N cap hN hcap j a]
  have hregion : logPrimeMeshCell 0 (19 / 96) m j ∩ jointRegion (e : ℝ) chi m omega j =
      candidateCell e m omega j := by
    ext t
    constructor
    · rintro ⟨ht, hg⟩
      exact ⟨ht, (jointRegion_on_selected_cell e chi m omega J5 j hj ht).mp hg⟩
    · rintro ⟨ht, hg⟩
      exact ⟨ht, (jointRegion_on_selected_cell e chi m omega J5 j hj ht).mpr hg⟩
  rw [hregion, candidateCell_eq_if e chi m omega J5 j hj]
  by_cases hs : firstStopCellCheck (e : ℝ) m j = true
  · simp only [if_pos hs]
  · simp only [if_neg hs, Set.mem_empty_iff_false, Finset.filter_false]

theorem historical_overlap_of_check
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (hcheck : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ) ∩
        physicalCell e m omega j (cap5 j : ℝ) =
      physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ) := by
  ext t
  constructor
  · exact fun ht => ht.1
  · exact fun ht => ⟨ht, old_region_subset_new_of_check e chi m omega J4 cap4 J5 cap5 hcheck j hj ht⟩

theorem old_wall_mem_new_only
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m)
    (hcap : old5 e chi m omega J4 cap4 j < cap5 j) {t : Fin 5 → ℝ}
    (ht : t ∈ candidateCell e m omega j)
    (hw : primeTupleOwnCubeForm t = (old5 e chi m omega J4 cap4 j : ℝ)) :
    t ∈ physicalCell e m omega j (cap5 j : ℝ) \
      physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ) := by
  rw [historical_new_only]
  refine ⟨ht, hw.ge, ?_⟩
  rw [hw]
  exact_mod_cast hcap

/-- Only an EXPLICIT residual own-cube filter attaches this eighth row;
the unfiltered candidate theorem above still enumerates all candidates. -/
theorem actual_ownCube_filter
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) (lambda : ℝ) :
    ((candidates (e : ℝ) chi m omega N cap).filter
      (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)).filter
        (fun p => (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 < (N : ℝ) ^ lambda) =
      (primeBox N).filter (fun p => actualPrimeTupleLog N p ∈ physicalCell e m omega j lambda) := by
  rw [candidates_on_selected_fifth_cell_filter e chi m omega J5 N cap hN hcap j hj]
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, ht⟩, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    exact ⟨hp, ht, (actualPrimeTupleOwnCube_iff hN p hpos lambda).mp hg⟩
  · rintro ⟨hp, ht, hg⟩
    have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    exact ⟨⟨hp, ht⟩, (actualPrimeTupleOwnCube_iff hN p hpos lambda).mpr hg⟩

/-- Literal new5/old4 actual minus difference on an ORIGINAL next
candidate, expressed by the two complete separately gated affine cells. -/
theorem actual_minus_difference_affine_on_candidate
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (hp : p ∈ candidates (e : ℝ) chi m omega N cap)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference
        e chi m omega J4 cap4 J5 cap5 N cap p =
      (if actualPrimeTupleLog N p ∈ physicalCell e m omega j (cap5 j : ℝ)
        then ungatedMinus N cap (cap5 j : ℝ) p else 0) -
      (if actualPrimeTupleLog N p ∈ physicalCell e m omega j (old5 e chi m omega J4 cap4 j : ℝ)
        then ungatedMinus N cap (old5 e chi m omega J4 cap4 j : ℝ) p else 0) := by
  have hg := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hg.1 i).1.pos
  have hc : actualPrimeTupleLog N p ∈ candidateCell e m omega j :=
    ⟨ht, (jointRegion_on_selected_cell e chi m omega J5 j hj ht).mp hg.2⟩
  rw [actual_minus_difference_on_selected_cell e chi m omega J4 cap4 J5 cap5 N cap hN p hpos j hj ht]
  simp only [physicalCell, Set.mem_inter_iff, Set.mem_setOf_eq, hc, true_and]

end P1OriginalHistoricalFifthOwnCubeAffineGates

end

end ImbalancedChen
