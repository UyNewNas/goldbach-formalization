import ImbalancedChen.ActualHistoricalFifthCellIntegral
import ImbalancedChen.ActualHistoricalFifthSavingIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED.

Last-candidate disintegration of the actual historical fifth correction.
The outer four coordinates retain the original first and effective third
ancestor gates. The inner candidate retains its half-open mesh interval,
strict descending-order gate, and BOTH distinct new/old own-cube profiles.
The old residual is the effective historical fourth level `old5`.

No equality with the unrelated paired four-dimensional Buchstab gain is
claimed. The analytic dictionary below is about the actual existing
`HistoricalPrefixCapData.fifthCellIntegral` and `fifthCorrectionIntegral`.
-/

namespace ImbalancedChen.P2HistoricalFifthDisintegration

open MeasureTheory Set
open MathlibNt.SieveTheory
open scoped Classical BigOperators

noncomputable section

abbrev Parent := Fin 4 → ℝ
abbrev Fifth := Fin 5 → ℝ

def join (p : Parent) (q : ℝ) : Fifth := Fin.snoc p q

/-- Extract the actual last candidate after its four-coordinate parent. -/
def split5 : Fifth ≃ᵐ Parent × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (Fin.last 4)).trans
    (MeasurableEquiv.prodComm ℝ Parent)

theorem split5_preserving : MeasurePreserving split5 := by
  have hs : MeasurePreserving (Prod.swap : ℝ × Parent → Parent × ℝ)
      volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap : MeasurePreserving
        (Prod.swap : ℝ × Parent → Parent × ℝ)
        (volume.prod volume) (volume.prod volume))
  exact hs.comp (volume_preserving_piFinSuccAbove _ (Fin.last 4))

theorem split5_symm (p : Parent) (q : ℝ) : split5.symm (p, q) = join p q := by
  ext i
  fin_cases i <;>
    simp [split5, join, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.insertNth, Fin.succAboveCases, MeasurableEquiv.prodComm]

theorem project_join (p : Parent) (q : ℝ) :
    historicalPrefixProject (by omega : 4 ≤ 5) (join p q) = p := by
  ext i
  fin_cases i <;> rfl

theorem sum_join (p : Parent) (q : ℝ) : (∑ i, join p q i) = (∑ i, p i) + q := by
  simp [join, Fin.sum_univ_castSucc]

theorem reciprocal_product_join (p : Parent) (q : ℝ) :
    (∏ i, 1 / join p q i) = (∏ i, 1 / p i) * (1 / q) := by
  simp [join, Fin.prod_univ_castSucc]

theorem ownCubeForm_join (p : Parent) (q : ℝ) :
    primeTupleOwnCubeForm (join p q) = (∑ i, p i) + 3 * q := by
  rw [primeTupleOwnCubeForm, sum_join]
  simp only [join, Fin.snoc_last]
  ring

/-- Literal one-dimensional residual with its own strict own-cube gate. -/
def lastProfile (lambda : ℝ) (p : Parent) (q : ℝ) : ℝ :=
  if (∑ i, p i) + 3 * q < lambda then
    (2 * Real.exp (-Real.eulerMascheroniConstant) / q) *
      suzukiContinuousLowerFactor (max 2 ((lambda - (∑ i, p i) - q) / q))
  else 0

theorem gatedProfile_join (lambda : ℝ) (p : Parent) (q : ℝ) :
    primeOwnCubeGatedProfile lambda (join p q) = lastProfile lambda p q := by
  simp only [primeOwnCubeGatedProfile, ownCubeForm_join, lastProfile,
    primeTupleMinusProfile, sum_join, join, Fin.snoc_last, sub_add_eq_sub_sub]

/-- Full Fubini for the actual 5->4+1 coordinate split. -/
theorem integral_last_candidate (F : Fifth → ℝ) (hF : Integrable F) :
    (∫ t : Fifth, F t) = ∫ p : Parent, ∫ q : ℝ, F (join p q) := by
  have hi : Integrable (fun v : Parent × ℝ => F (split5.symm v)) :=
    split5_preserving.symm.integrable_comp_of_integrable hF
  calc
    _ = ∫ v : Parent × ℝ, F (split5.symm v) :=
      (split5_preserving.symm.integral_comp' F).symm
    _ = _ := by
      simpa only [split5_symm] using
        integral_prod (fun v : Parent × ℝ => F (split5.symm v)) hi

def cellRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set Fifth :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
    primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)

def cellProfile (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fifth) : ℝ :=
  (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
    primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i

def supportedCell (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Fifth → ℝ :=
  (cellRegion D j).indicator (cellProfile D j)

theorem cellRegion_measurable (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : MeasurableSet (cellRegion D j) := by
  exact (measurableSet_logPrimeMeshCell _ _ _ _).inter
    (measurableSet_primeAffineGateRegion _ _)

theorem supportedCell_integrable (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b)
    (j : Fin 5 → Fin (D.m + 1)) : Integrable (supportedCell D j) := by
  have haR : (0 : ℝ) < (D.a : ℝ) := by exact_mod_cast ha
  have habR : (D.a : ℝ) < (D.b : ℝ) := by exact_mod_cast hab
  have hn := integrableOn_primeOwnCubeGatedProfile_IcoCell haR habR
    (D.cap5 j : ℝ) D.m j ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
  have ho := integrableOn_primeOwnCubeGatedProfile_IcoCell haR habR
    (D.old5 j : ℝ) D.m j ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
  have hd : IntegrableOn (cellProfile D j) (cellRegion D j) := by
    simpa only [cellProfile, cellRegion, sub_mul] using hn.sub ho
  exact hd.integrable_indicator (cellRegion_measurable D j)

def parentLabel (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Fin 4 → Fin (D.m + 1) :=
  historicalPrefixProject (by omega : 4 ≤ 5) j

/-- Parent gate has no old/new fifth own-cube admission condition. -/
def parentRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Set Parent :=
  logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m (parentLabel D j) ∩
    {p | StrictAnti p ∧ 3 * p 0 < (D.old : ℝ) ∧
      p 0 + p 1 + 3 * p 2 <
        (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)}

def candidateSlice (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) : Set ℝ :=
  Ico (logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 4))
      (logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 4)) ∩ Iio (p 3)

theorem strictAnti_parent_iff (p : Parent) :
    StrictAnti p ↔ p 1 < p 0 ∧ p 2 < p 1 ∧ p 3 < p 2 := by
  constructor
  · intro h
    exact ⟨h (by decide), h (by decide), h (by decide)⟩
  · rintro ⟨h1, h2, h3⟩
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3

theorem strictAnti_join (p : Parent) (q : ℝ) :
    StrictAnti (join p q) ↔ StrictAnti p ∧ q < p 3 := by
  constructor
  · intro h
    constructor
    · rw [strictAnti_parent_iff]
      exact ⟨h (by decide : (0 : Fin 5) < 1),
        h (by decide : (1 : Fin 5) < 2), h (by decide : (2 : Fin 5) < 3)⟩
    · exact h (by decide : (3 : Fin 5) < 4)
  · rintro ⟨hp, hq⟩
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · exact hp (by decide : (0 : Fin 4) < 1)
    · exact hp (by decide : (1 : Fin 4) < 2)
    · exact hp (by decide : (2 : Fin 4) < 3)
    · exact hq

theorem meshCell_join (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) (q : ℝ) :
    join p q ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ↔
      p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m (parentLabel D j) ∧
      q ∈ Ico (logPrimeMeshLo (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 4))
        (logPrimeMeshHi (D.a : ℝ) (D.b : ℝ) D.m j (Fin.last 4)) := by
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · have hp := mem_logPrimeMeshCell_historicalPrefixProject
        (by omega : 4 ≤ 5) ht
      simpa only [project_join, parentLabel] using hp
    · exact (mem_logPrimeMeshCell.mp ht) (Fin.last 4)
  · rintro ⟨hp, hq⟩
    rw [mem_logPrimeMeshCell]
    intro i
    fin_cases i
    · exact (mem_logPrimeMeshCell.mp hp) 0
    · exact (mem_logPrimeMeshCell.mp hp) 1
    · exact (mem_logPrimeMeshCell.mp hp) 2
    · exact (mem_logPrimeMeshCell.mp hp) 3
    · exact hq

/-- Exact joint-cell geometry after extracting the last candidate. -/
theorem cellRegion_join (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) (q : ℝ) :
    join p q ∈ cellRegion D j ↔
      p ∈ parentRegion D j ∧ q ∈ candidateSlice D j p := by
  simp only [cellRegion, mem_inter_iff, meshCell_join, D.mem_fifthParentGateRegion,
    strictAnti_join, parentRegion, candidateSlice, mem_setOf_eq, mem_Iio]
  simp only [join, Fin.snoc_castSucc]
  tauto

theorem candidateSlice_measurable (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) :
    MeasurableSet (candidateSlice D j p) := by
  exact measurableSet_Ico.inter measurableSet_Iio

theorem parentRegion_measurable (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : MeasurableSet (parentRegion D j) := by
  have hanti : MeasurableSet {p : Parent | StrictAnti p} := by
    have heq : {p : Parent | StrictAnti p} =
        {p : Parent | p 1 < p 0 ∧ p 2 < p 1 ∧ p 3 < p 2} := by
      ext p
      exact strictAnti_parent_iff p
    rw [heq]
    exact ((isOpen_lt (continuous_apply 1) (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 2) (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 3) (continuous_apply 2)))).measurableSet
  have hfirst : Continuous (fun p : Parent => 3 * p 0) := by fun_prop
  have hthird : Continuous (fun p : Parent => p 0 + p 1 + 3 * p 2) := by fun_prop
  exact (measurableSet_logPrimeMeshCell _ _ _ _).inter
    (hanti.inter ((isOpen_lt hfirst continuous_const).measurableSet.inter
      (isOpen_lt hthird continuous_const).measurableSet))

theorem cellProfile_join (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) (q : ℝ) :
    cellProfile D j (join p q) =
      (lastProfile (D.cap5 j : ℝ) p q - lastProfile (D.old5 j : ℝ) p q) *
        ((∏ i, 1 / p i) * (1 / q)) := by
  rw [cellProfile, gatedProfile_join, gatedProfile_join, reciprocal_product_join]

theorem supportedCell_join (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) (q : ℝ) :
    supportedCell D j (join p q) =
      (parentRegion D j).indicator (fun p =>
        (candidateSlice D j p).indicator (fun q =>
          (lastProfile (D.cap5 j : ℝ) p q - lastProfile (D.old5 j : ℝ) p q) *
            ((∏ i, 1 / p i) * (1 / q))) q) p := by
  by_cases hp : p ∈ parentRegion D j <;>
    by_cases hq : q ∈ candidateSlice D j p <;>
      simp [supportedCell, Set.indicator_apply, cellRegion_join, cellProfile_join, hp, hq]

theorem integral_fixed_parent_indicator (s : Set Parent) (p : Parent)
    (F : Parent → ℝ → ℝ) :
    (∫ q : ℝ, s.indicator (fun p => F p q) p) =
      s.indicator (fun p => ∫ q : ℝ, F p q) p := by
  by_cases hp : p ∈ s <;> simp [hp]

theorem integral_candidate_indicator (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (p : Parent) (F : ℝ → ℝ) :
    (∫ q : ℝ, (candidateSlice D j p).indicator F q) =
      ∫ q in candidateSlice D j p, F q := by
  exact integral_indicator (candidateSlice_measurable D j p)

/-- The genuine historical fifth cell is an outer four-dimensional parent
integral of its actual one-dimensional new-minus-old residual difference. -/
theorem fifthCellIntegral_disintegrated (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ p : Parent in parentRegion D j, ∫ q in candidateSlice D j p,
        (lastProfile (D.cap5 j : ℝ) p q - lastProfile (D.old5 j : ℝ) p q) *
          ((∏ i, 1 / p i) * (1 / q)) := by
  calc
    _ = ∫ t : Fifth in cellRegion D j, cellProfile D j t :=
      D.fifthCellIntegral_eq_integral ha hab j
    _ = ∫ t : Fifth, supportedCell D j t :=
      (integral_indicator (cellRegion_measurable D j)).symm
    _ = ∫ p : Parent, ∫ q : ℝ, supportedCell D j (join p q) :=
      integral_last_candidate _ (supportedCell_integrable D ha hab j)
    _ = _ := by
      simp_rw [supportedCell_join, integral_fixed_parent_indicator,
        integral_candidate_indicator,
        integral_indicator (parentRegion_measurable D j)]

/-- Every selected fifth cell, with its actual inherited fourth cap. -/
theorem fifthCorrectionIntegral_disintegrated (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral = ∑ j ∈ D.cells5,
      ∫ p : Parent in parentRegion D j, ∫ q in candidateSlice D j p,
        (lastProfile (D.cap5 j : ℝ) p q - lastProfile (D.old5 j : ℝ) p q) *
          ((∏ i, 1 / p i) * (1 / q)) := by
  unfold HistoricalPrefixCapData.fifthCorrectionIntegral
  apply Finset.sum_congr rfl
  intro j _
  exact fifthCellIntegral_disintegrated D ha hab j

/-- The old level on a last-candidate slice is the complete effective
fourth ancestor exponent, including its inherited third fallback. -/
theorem old5_eq_exponent4_on_slice (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1))
    (p : Parent) (q : ℝ)
    (hc : join p q ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.old5 j = D.exponent4 p := by
  have hp := (meshCell_join D j p q).mp hc
  rw [D.exponent4_on_cell hab p (parentLabel D j) hp.1]
  rfl

theorem cap5_eq_exponent5_on_selected_slice (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (p : Parent) (q : ℝ)
    (hc : join p q ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.cap5 j = D.exponent5 (join p q) := by
  rw [D.exponent5_on_cell hab _ j hc]
  simp only [HistoricalPrefixCapData.cell5, if_pos hj]

end

end ImbalancedChen.P2HistoricalFifthDisintegration
