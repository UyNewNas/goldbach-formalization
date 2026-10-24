import ImbalancedChen.ActualHistoricalFifthCellIntegral

/-!
Support and cancellation for the actual historical fifth correction.
The parent reads the original first level and the effective third history.
The old residual reads the effective fourth history.  Neither own-cube
admission is absorbed into the parent.  Raw `cap5` has no fallback off the
selected finset; the effective-cell integral below deliberately uses `cell5`.

Source-only candidate, 2026-10-24.  No compiler was run.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

def p1FifthJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set (Fin 5 → ℝ) :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

def p1FifthJointUnion (D : HistoricalPrefixCapData) : Set (Fin 5 → ℝ) :=
  ⋃ j ∈ D.cells5, D.p1FifthJointCell j

def p1FifthHistoricalParent (D : HistoricalPrefixCapData) : Set (Fin 5 → ℝ) :=
  {t | StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
    t 0 + t 1 + 3 * t 2 <
      (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 5) t) : ℝ)}

def p1FifthCellProfile (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ) : ℝ :=
  (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
    primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i

def p1FifthHistoricalProfile (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ) : ℝ :=
  (primeOwnCubeGatedProfile (D.exponent5 t : ℝ) t -
    primeOwnCubeGatedProfile
      (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) : ℝ) t) *
    ∏ i, 1 / t i

def p1FifthCorrectionKernel (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ) : ℝ :=
  if t ∈ D.p1FifthHistoricalParent then D.p1FifthHistoricalProfile t else 0

theorem measurableSet_p1FifthJointCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : MeasurableSet (D.p1FifthJointCell j) := by
  exact (measurableSet_logPrimeMeshCell _ _ _ _).inter
    (measurableSet_primeAffineGateRegion _ _)

theorem measurableSet_p1FifthJointUnion (D : HistoricalPrefixCapData) :
    MeasurableSet D.p1FifthJointUnion := by
  exact Finset.measurableSet_biUnion D.cells5
    (fun j _ => D.measurableSet_p1FifthJointCell j)

theorem p1FifthHistoricalParent_on_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    t ∈ D.p1FifthHistoricalParent ↔
      t ∈ primeAffineGateRegion ordinaryUpperFiveGateForms
        (D.fifthParentGateBounds j) := by
  rw [D.mem_fifthParentGateRegion]
  change (StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
    t 0 + t 1 + 3 * t 2 <
      (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 5) t) : ℝ)) ↔ _
  rw [D.exponent3_on_cell hab _ _
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht)]

theorem p1FifthHistoricalProfile_on_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.p1FifthHistoricalProfile t = D.p1FifthCellProfile j t := by
  unfold p1FifthHistoricalProfile p1FifthCellProfile
  rw [D.exponent5_on_cell hab _ _ ht,
    D.exponent4_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]
  simp only [cell5, if_pos hj, old5]

theorem p1FifthHistoricalProfile_on_unselected_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.p1FifthHistoricalProfile t = 0 := by
  unfold p1FifthHistoricalProfile
  rw [D.exponent5_on_cell hab _ _ ht,
    D.exponent4_on_cell hab _ _
      (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 4 ≤ 5) ht)]
  simp only [cell5, if_neg hj, old5, sub_self, zero_mul]

theorem p1FifthHistoricalProfile_outside (D : HistoricalPrefixCapData)
    (t : Fin 5 → ℝ)
    (hout : ∀ j ∈ D.cells5,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.p1FifthHistoricalProfile t = 0 := by
  unfold p1FifthHistoricalProfile
  rw [D.exponent5_outside t hout, sub_self, zero_mul]

theorem p1FifthCellProfile_eq_zero_of_caps_eq (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (hcap : D.cap5 j = D.old5 j)
    (t : Fin 5 → ℝ) : D.p1FifthCellProfile j t = 0 := by
  simp only [p1FifthCellProfile, hcap, sub_self, zero_mul]

theorem p1FifthCellProfile_eq_zero_of_ownCubes_fail (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ)
    (hnew : (D.cap5 j : ℝ) ≤ primeTupleOwnCubeForm t)
    (hold : (D.old5 j : ℝ) ≤ primeTupleOwnCubeForm t) :
    D.p1FifthCellProfile j t = 0 := by
  simp [p1FifthCellProfile, primeOwnCubeGatedProfile,
    not_lt.mpr hnew, not_lt.mpr hold]

theorem p1FifthCellIntegral_eq_zero_of_caps_eq (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (hcap : D.cap5 j = D.old5 j) :
    D.fifthCellIntegral j = 0 := by
  simp only [fifthCellIntegral, hcap, sub_self]

/-- This is the integral of the effective fifth cell, including its fallback. -/
def p1FifthEffectiveCellIntegral (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.cell5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j) -
    primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

theorem p1FifthEffectiveCellIntegral_of_mem (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    D.p1FifthEffectiveCellIntegral j = D.fifthCellIntegral j := by
  simp only [p1FifthEffectiveCellIntegral, fifthCellIntegral, cell5, if_pos hj]

theorem p1FifthEffectiveCellIntegral_of_not_mem (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5) :
    D.p1FifthEffectiveCellIntegral j = 0 := by
  simp only [p1FifthEffectiveCellIntegral, cell5, if_neg hj, sub_self]

theorem p1FifthCorrectionKernel_on_jointCell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (t : Fin 5 → ℝ) (ht : t ∈ D.p1FifthJointCell j) :
    D.p1FifthCorrectionKernel t = D.p1FifthCellProfile j t := by
  have hp := (D.p1FifthHistoricalParent_on_cell hab j t ht.1).mpr ht.2
  rw [p1FifthCorrectionKernel, if_pos hp]
  exact D.p1FifthHistoricalProfile_on_cell hab j hj t ht.1

theorem p1FifthCorrectionKernel_outside_union (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (t : Fin 5 → ℝ) (hout : t ∉ D.p1FifthJointUnion) :
    D.p1FifthCorrectionKernel t = 0 := by
  by_cases hp : t ∈ D.p1FifthHistoricalParent
  · rw [p1FifthCorrectionKernel, if_pos hp]
    apply D.p1FifthHistoricalProfile_outside t
    intro j hj ht
    apply hout
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj,
      ⟨ht, (D.p1FifthHistoricalParent_on_cell hab j t ht).mp hp⟩⟩⟩
  · exact if_neg hp

theorem p1FifthCorrectionKernel_on_unselected_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.p1FifthCorrectionKernel t = 0 := by
  unfold p1FifthCorrectionKernel
  rw [D.p1FifthHistoricalProfile_on_unselected_cell hab j hj t ht]
  simp

theorem p1FifthCorrectionKernel_eq_cell_indicators (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (t : Fin 5 → ℝ) :
    D.p1FifthCorrectionKernel t =
      ∑ j ∈ D.cells5, (D.p1FifthJointCell j).indicator (D.p1FifthCellProfile j) t := by
  by_cases ht : t ∈ D.p1FifthJointUnion
  · obtain ⟨j, hj, htj⟩ : ∃ j ∈ D.cells5, t ∈ D.p1FifthJointCell j := by
      simpa only [p1FifthJointUnion, Set.mem_iUnion] using ht
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [Set.indicator_of_mem htj]
      exact D.p1FifthCorrectionKernel_on_jointCell hab j hj t htj
    · intro q _hq hqj
      apply Set.indicator_of_notMem
      intro htq
      exact hqj (logPrimeMeshCell_unique (by exact_mod_cast hab) htq.1 htj.1)
  · rw [D.p1FifthCorrectionKernel_outside_union hab t ht]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply Set.indicator_of_notMem
    intro htj
    exact ht (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, htj⟩⟩)

theorem integrableOn_p1FifthCellProfile (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    IntegrableOn (D.p1FifthCellProfile j) (D.p1FifthJointCell j) := by
  have hnew := integrableOn_primeOwnCubeGatedProfile_IcoCell
    (by exact_mod_cast ha : (0 : ℝ) < D.a)
    (by exact_mod_cast hab : (D.a : ℝ) < D.b) (D.cap5 j : ℝ) D.m j
    ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
  have hold := integrableOn_primeOwnCubeGatedProfile_IcoCell
    (by exact_mod_cast ha : (0 : ℝ) < D.a)
    (by exact_mod_cast hab : (D.a : ℝ) < D.b) (D.old5 j : ℝ) D.m j
    ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
  apply (hnew.sub hold).congr
  exact Filter.Eventually.of_forall (fun t => by dsimp [p1FifthCellProfile]; ring)

theorem integrable_p1FifthCorrectionKernel (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    Integrable D.p1FifthCorrectionKernel := by
  have hfun : D.p1FifthCorrectionKernel = fun t =>
      ∑ j ∈ D.cells5, (D.p1FifthJointCell j).indicator (D.p1FifthCellProfile j) t := by
    funext t
    exact D.p1FifthCorrectionKernel_eq_cell_indicators hab.le t
  rw [hfun]
  exact integrable_finsetSum _ (fun j _hj =>
    (integrable_indicator_iff (D.measurableSet_p1FifthJointCell j)).2
      (D.integrableOn_p1FifthCellProfile ha hab j))

theorem p1FifthCorrectionKernel_support_subset (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) :
    Function.support D.p1FifthCorrectionKernel ⊆ D.p1FifthJointUnion := by
  intro t ht
  by_contra hout
  exact ht (D.p1FifthCorrectionKernel_outside_union hab t hout)

theorem p1FifthCorrectionKernel_integral_on_unselected_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5) :
    (∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j,
      D.p1FifthCorrectionKernel t) = 0 := by
  calc
    _ = ∫ _t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeMeshCell _ _ _ j)] with t ht
      exact D.p1FifthCorrectionKernel_on_unselected_cell hab j hj t ht
    _ = 0 := by simp

theorem p1FifthCorrectionIntegral_eq_integral_kernel (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral = ∫ t, D.p1FifthCorrectionKernel t := by
  have hfun : D.p1FifthCorrectionKernel = fun t =>
      ∑ j ∈ D.cells5, (D.p1FifthJointCell j).indicator (D.p1FifthCellProfile j) t := by
    funext t
    exact D.p1FifthCorrectionKernel_eq_cell_indicators hab.le t
  rw [hfun, integral_finsetSum _ (fun j _hj =>
    (integrable_indicator_iff (D.measurableSet_p1FifthJointCell j)).2
      (D.integrableOn_p1FifthCellProfile ha hab j))]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [integral_indicator (D.measurableSet_p1FifthJointCell j)]
  exact D.fifthCellIntegral_eq_integral ha hab j

/-- A single genuine integral over the common historical selected union. -/
theorem p1FifthCorrectionIntegral_eq_integral_jointUnion (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∫ t in D.p1FifthJointUnion, D.p1FifthCorrectionKernel t := by
  rw [D.p1FifthCorrectionIntegral_eq_integral_kernel ha hab,
    ← integral_indicator D.measurableSet_p1FifthJointUnion]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : t ∈ D.p1FifthJointUnion
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht,
        D.p1FifthCorrectionKernel_outside_union hab.le t ht])

/-- The same integral without the redundant parent indicator: membership
in the common union already pays the actual historical parent gates. -/
theorem p1FifthCorrectionIntegral_eq_integral_historicalProfile
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∫ t in D.p1FifthJointUnion, D.p1FifthHistoricalProfile t := by
  rw [D.p1FifthCorrectionIntegral_eq_integral_jointUnion ha hab]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem D.measurableSet_p1FifthJointUnion] with t ht
  obtain ⟨j, _hj, htj⟩ : ∃ j ∈ D.cells5, t ∈ D.p1FifthJointCell j := by
    simpa only [p1FifthJointUnion, Set.mem_iUnion] using ht
  exact if_pos ((D.p1FifthHistoricalParent_on_cell hab.le j t htj.1).mpr htj.2)

end HistoricalPrefixCapData

end

end ImbalancedChen
