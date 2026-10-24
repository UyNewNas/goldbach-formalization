import ImbalancedChen.P1FourthNearOneKernel
import ImbalancedChen.P1HistoricalFourthResidualIntegral

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The full fourth historical integral on the actual common T3 joint cell.
There is no whole-box residual margin.  The continuous max-one extension
is used off the admitted region only.  The historical gates themselves
prove strict legality of both literal profiles on the integration region.
-/

namespace ImbalancedChen.P1FourthFullCellIntegral

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical BigOperators
open HistoricalPrefixCapData
open P1FourthNearOneKernel

def jointCell (D : HistoricalPrefixCapData) (j : Fin 4 → Fin (D.m + 1)) :
    Set (Fin 4 → ℝ) :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion p1_fourthParentGateForms (D.p1_fourthParentGateBounds j)

theorem measurableSet_jointCell (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) : MeasurableSet (jointCell D j) :=
  (measurableSet_logPrimeMeshCell _ _ _ _).inter
    (measurableSet_primeAffineGateRegion _ _)

theorem jointCell_coordinate_bounds (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (j : Fin 4 → Fin (D.m + 1)) {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j)
    (i : Fin 4) : (D.a : ℝ) ≤ t i ∧ t i < (D.b : ℝ) := by
  exact mem_logPrimeBox.mp
    (logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht.1) i

theorem jointCell_subset_closedBox (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (j : Fin 4 → Fin (D.m + 1)) :
    jointCell D j ⊆ univ.pi (fun _ : Fin 4 => Icc (D.a : ℝ) (D.b : ℝ)) := by
  intro t ht i _
  exact ⟨(jointCell_coordinate_bounds D hab j ht i).1,
    (jointCell_coordinate_bounds D hab j ht i).2.le⟩

/-- Strict legality follows from the T3 parent row and t4 < t3. -/
theorem residual_gt_one_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {lambda : ℝ} (hlevel : (D.old4 j : ℝ) ≤ lambda)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) : 1 < residual lambda t := by
  have hg := (D.p1_mem_fourthParentGateRegion j t).mp ht.2
  have h43 : t 3 < t 2 := hg.1 (by decide : (2 : Fin 4) < 3)
  have hp : 0 < t (Fin.last 3) :=
    (show (0 : ℝ) < (D.a : ℝ) by exact_mod_cast ha).trans_le
      (jointCell_coordinate_bounds D hab j ht _).1
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ] <;> ring
  change 1 < (lambda - ∑ i, t i) / t (Fin.last 3)
  apply (lt_div_iff₀ hp).mpr
  change 1 * t 3 < lambda - ∑ i, t i
  rw [hsum]
  linarith [hg.2.2]

theorem old_residual_gt_one (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    1 < residual (D.old4 j : ℝ) t :=
  residual_gt_one_on_joint D ha hab j le_rfl ht

theorem new_residual_gt_one (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    1 < residual (D.cap4 j : ℝ) t := by
  apply residual_gt_one_on_joint D ha hab j ?_ ht
  exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj

theorem jointCell_subset_legal (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {lambda : ℝ} (hlevel : (D.old4 j : ℝ) ≤ lambda) :
    jointCell D j ⊆ legal (D.a : ℝ) lambda := by
  intro t ht
  have hp : 0 < t (Fin.last 3) :=
    (show (0 : ℝ) < (D.a : ℝ) by exact_mod_cast ha).trans_le
      (jointCell_coordinate_bounds D hab j ht _).1
  have hs := residual_gt_one_on_joint D ha hab j hlevel ht
  change 1 < (lambda - ∑ i, t i) / t (Fin.last 3) at hs
  have hh := (lt_div_iff₀ hp).mp hs
  exact ⟨(jointCell_coordinate_bounds D hab j ht _).1, by linarith⟩

/-- Defined on the whole positive box for use as a continuous prime test. -/
def extendedProfile (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant)) * maxOneNormalized lambda t

theorem continuousOn_extendedProfile {a b lambda : ℝ} (ha : 0 < a) :
    ContinuousOn (extendedProfile lambda) (univ.pi (fun _ : Fin 4 => Icc a b)) :=
  continuousOn_const.mul (continuousOn_maxOneNormalized ha)

theorem extendedProfile_eq_raw_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {lambda : ℝ} (hlevel : (D.old4 j : ℝ) ≤ lambda)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    extendedProfile lambda t = fourthPlusProfileP1 lambda t := by
  have haR : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast ha
  have hlegal := jointCell_subset_legal D ha hab j hlevel ht
  calc
    extendedProfile lambda t = density lambda t := by
      rw [extendedProfile, maxOneNormalized_eq haR hlegal]
      rfl
    _ = fourthPlusProfileP1 lambda t :=
      density_eq_actual lambda t (residual_gt_one_on_joint D ha hab j hlevel ht)

theorem abs_rawProfile_le_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {lambda : ℝ} (hlevel : (D.old4 j : ℝ) ≤ lambda)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    |fourthPlusProfileP1 lambda t| ≤ 4 / (D.a : ℝ) := by
  have heq : density lambda t = fourthPlusProfileP1 lambda t :=
    density_eq_actual lambda t (residual_gt_one_on_joint D ha hab j hlevel ht)
  rw [← heq]
  exact abs_density_le (by exact_mod_cast ha)
    (jointCell_subset_legal D ha hab j hlevel ht)

def reciprocalWeight (t : Fin 4 → ℝ) : ℝ := ∏ i, 1 / t i

theorem continuousOn_reciprocalWeight {a b : ℝ} (ha : 0 < a) :
    ContinuousOn reciprocalWeight (univ.pi (fun _ : Fin 4 => Icc a b)) := by
  unfold reciprocalWeight
  apply continuousOn_finsetProd Finset.univ
  intro i _
  exact continuousOn_const.div (continuous_apply i).continuousOn
    (fun t ht => (ha.trans_le (ht i (mem_univ _)).1).ne')

def extendedWeightedProfile (lambda : ℝ) (t : Fin 4 → ℝ) : ℝ :=
  extendedProfile lambda t * reciprocalWeight t

/-- Integrability of the extension requires no geometric legality at all. -/
theorem integrableOn_extendedWeightedProfile_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1)) (lambda : ℝ) :
    IntegrableOn (extendedWeightedProfile lambda) (jointCell D j) := by
  have haR : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast ha
  have hc : ContinuousOn (extendedWeightedProfile lambda)
      (univ.pi (fun _ : Fin 4 => Icc (D.a : ℝ) (D.b : ℝ))) :=
    (continuousOn_extendedProfile haR).mul (continuousOn_reciprocalWeight haR)
  exact (hc.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
    (jointCell_subset_closedBox D hab j)

theorem integrableOn_rawWeightedProfile_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {lambda : ℝ} (hlevel : (D.old4 j : ℝ) ≤ lambda) :
    IntegrableOn (fun t => fourthPlusProfileP1 lambda t * ∏ i, 1 / t i)
      (jointCell D j) := by
  apply (integrableOn_extendedWeightedProfile_joint D ha hab j lambda).congr_fun
    (fun t ht => ?_) (measurableSet_jointCell D j)
  unfold extendedWeightedProfile reciprocalWeight
  rw [extendedProfile_eq_raw_on_joint D ha hab j hlevel ht]

/-- Independent full I4 cell, retaining the actual common historical T3 domain. -/
def fullCellIntegral (D : HistoricalPrefixCapData) (j : Fin 4 → Fin (D.m + 1)) : ℝ :=
  ∫ t in jointCell D j,
    (extendedProfile (D.old4 j : ℝ) t - extendedProfile (D.cap4 j : ℝ) t) *
      reciprocalWeight t

def fullIntegral (D : HistoricalPrefixCapData) : ℝ :=
  ∑ j ∈ D.cells4, fullCellIntegral D j

theorem integrableOn_fullCellIntegrand (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1)) :
    IntegrableOn (fun t =>
      (extendedProfile (D.old4 j : ℝ) t - extendedProfile (D.cap4 j : ℝ) t) *
        reciprocalWeight t) (jointCell D j) := by
  simpa only [extendedWeightedProfile, sub_mul] using
    (integrableOn_extendedWeightedProfile_joint D ha hab j (D.old4 j : ℝ)).sub
      (integrableOn_extendedWeightedProfile_joint D ha hab j (D.cap4 j : ℝ))

theorem fullCellIntegral_eq_raw_single (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    fullCellIntegral D j = ∫ t in jointCell D j,
      (fourthPlusProfileP1 (D.old4 j : ℝ) t - fourthPlusProfileP1 (D.cap4 j : ℝ) t) *
        ∏ i, 1 / t i := by
  have hlevel : (D.old4 j : ℝ) ≤ (D.cap4 j : ℝ) := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  apply setIntegral_congr_fun (measurableSet_jointCell D j)
  intro t ht
  rw [extendedProfile_eq_raw_on_joint D ha hab j le_rfl ht,
    extendedProfile_eq_raw_on_joint D ha hab j hlevel ht]
  rfl

/-- Exact dictionary to the earlier raw integral, with no margin premise. -/
theorem fullCellIntegral_eq_dictionary (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    fullCellIntegral D j = D.fourthCellIntegralP1 j := by
  have hlevel : (D.old4 j : ℝ) ≤ (D.cap4 j : ℝ) := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  rw [fullCellIntegral_eq_raw_single D ha hab hcheck j hj]
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_rawWeightedProfile_joint D ha hab j le_rfl)
    (integrableOn_rawWeightedProfile_joint D ha hab j hlevel)]
  rfl

theorem fullIntegral_eq_dictionary (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true) :
    fullIntegral D = D.fourthCorrectionIntegralP1 := by
  apply Finset.sum_congr rfl
  intro j hj
  exact fullCellIntegral_eq_dictionary D ha hab hcheck j hj

/-- Only the strict/weak parent walls change here; the Ico mesh is retained. -/
def weakJointCell (D : HistoricalPrefixCapData) (j : Fin 4 → Fin (D.m + 1)) :
    Set (Fin 4 → ℝ) :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    {t | ∀ i, p1_fourthParentGateForms i t ≤ D.p1_fourthParentGateBounds j i}

theorem jointCell_ae_eq_weakJointCell (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) : jointCell D j =ᵐ[volume] weakJointCell D j := by
  filter_upwards [ae_primeAffineGate_no_wall p1_fourthParentGateForms
    (D.p1_fourthParentGateBounds j) p1_fourthParentGateForms_ne_zero] with t ht
  apply propext
  change (t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
      ∀ i, p1_fourthParentGateForms i t < D.p1_fourthParentGateBounds j i) ↔
    (t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
      ∀ i, p1_fourthParentGateForms i t ≤ D.p1_fourthParentGateBounds j i)
  exact and_congr_right (fun _ => ⟨fun h i => (h i).le,
    fun h i => lt_of_le_of_ne (h i) (ht i)⟩)

theorem integral_jointCell_eq_weakJointCell (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) (f : (Fin 4 → ℝ) → ℝ) :
    (∫ t in jointCell D j, f t) = ∫ t in weakJointCell D j, f t :=
  setIntegral_congr_set (jointCell_ae_eq_weakJointCell D j)

end
end ImbalancedChen.P1FourthFullCellIntegral
