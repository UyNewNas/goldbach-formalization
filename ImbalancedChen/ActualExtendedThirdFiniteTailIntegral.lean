import ImbalancedChen.ActualExtendedThirdFinitePhysicalKernel
import ImbalancedChen.ActualExtendedThirdClosedIntegral

/-!
# Actual tuple-space tail of the finite robust-cap lookup

The measurable finite lookup is used in the tuple integrand itself. Tonelli
identifies its actual ordered Lebesgue mass with the canonical nested tail;
the actual residual certificate pays the uniform small-cutoff estimate.
The closed manuscript ordering is connected by the previously proved null
ordering wall, rather than by assuming an integral identity or measurability.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open VariableEnvelope
open scoped Classical ENNReal

def actualExtendedThirdFiniteOrderedTailMass (e : ℝ) (m : ℕ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdOrderedTailRegion h,
    ENNReal.ofReal (actualExtendedThirdFiniteKernel e m t)

private theorem finite_insert_last_fin3 (q x y : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      (q, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x, y)) = ![x, y, q] := by
  ext i
  fin_cases i <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth, Fin.succAboveCases, MeasurableEquiv.piFinTwo]

/-- Actual Tonelli bridge; measurability is paid by the explicit capped kernel,
not supplied as a premise on the original functional. -/
theorem actualExtendedThirdFiniteOrderedTailMass_eq_nested (e h : ℝ) (m : ℕ) :
    actualExtendedThirdFiniteOrderedTailMass e m h =
      ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z thirdPrefixRho, ∫⁻ y in Ioc z x,
        ENNReal.ofReal (actualExtendedThirdFiniteKernel e m ![x, y, z]) := by
  let F : (Fin 3 → ℝ) → ℝ≥0∞ := (actualExtendedThirdOrderedTailRegion h).indicator
    (fun t => ENNReal.ofReal (actualExtendedThirdFiniteKernel e m t))
  have hF : Measurable F := (measurable_actualExtendedThirdFiniteKernel e m).ennreal_ofReal.indicator
    (measurableSet_actualExtendedThirdOrderedTailRegion h)
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  let E₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinSuccAbove _ 2
  have hE₂ : MeasurePreserving E₂ := volume_preserving_piFinTwo _
  have hvec (x y z : ℝ) : F ![x, y, z] =
      (Ioc 0 h).indicator (fun z => (Ioc z thirdPrefixRho).indicator
        (fun x => (Ioc z x).indicator
          (fun y => ENNReal.ofReal (actualExtendedThirdFiniteKernel e m ![x, y, z])) y) x) z := by
    have hmem : ![x, y, z] ∈ actualExtendedThirdOrderedTailRegion h ↔
        z ∈ Ioc 0 h ∧ x ∈ Ioc z thirdPrefixRho ∧ y ∈ Ioc z x := by
      change (0 < z ∧ z ≤ h ∧ z < x ∧ x ≤ thirdPrefixRho ∧ z < y ∧ y ≤ x) ↔
        (0 < z ∧ z ≤ h) ∧ (z < x ∧ x ≤ thirdPrefixRho) ∧ (z < y ∧ y ≤ x)
      constructor
      · rintro ⟨hz, hzh, hzx, hx, hzy, hy⟩
        exact ⟨⟨hz, hzh⟩, ⟨hzx, hx⟩, ⟨hzy, hy⟩⟩
      · rintro ⟨⟨hz, hzh⟩, ⟨hzx, hx⟩, ⟨hzy, hy⟩⟩
        exact ⟨hz, hzh, hzx, hx, hzy, hy⟩
    by_cases hz : z ∈ Ioc 0 h <;>
      by_cases hx : x ∈ Ioc z thirdPrefixRho <;>
      by_cases hy : y ∈ Ioc z x <;>
      simp_all [F, Set.indicator_apply]
  calc
    actualExtendedThirdFiniteOrderedTailMass e m h = ∫⁻ t, F t :=
      (lintegral_indicator (measurableSet_actualExtendedThirdOrderedTailRegion h) _).symm
    _ = ∫⁻ p : ℝ × (Fin 2 → ℝ), F (E.symm p) := (hE.symm.lintegral_comp hF).symm
    _ = ∫⁻ z : ℝ, ∫⁻ v : Fin 2 → ℝ, F (E.symm (z, v)) :=
      lintegral_prod _ (hF.comp E.symm.measurable).aemeasurable
    _ = ∫⁻ z : ℝ, ∫⁻ x : ℝ, ∫⁻ y : ℝ, F ![x, y, z] := by
      apply lintegral_congr
      intro z
      have hs : Measurable (fun v : Fin 2 → ℝ => F (E.symm (z, v))) :=
        hF.comp (E.symm.measurable.comp (measurable_const.prodMk measurable_id))
      calc
        _ = ∫⁻ p : ℝ × ℝ, F (E.symm (z, E₂.symm p)) :=
          (hE₂.symm.lintegral_comp hs).symm
        _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, F (E.symm (z, E₂.symm (x, y))) :=
          lintegral_prod _ (hs.comp E₂.symm.measurable).aemeasurable
        _ = _ := by simp only [E, E₂, finite_insert_last_fin3]
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Ioc 0 h
      · rw [indicator_of_mem hz]
        calc
          _ = ∫⁻ x : ℝ, (Ioc z thirdPrefixRho).indicator
              (fun x => ∫⁻ y in Ioc z x,
                ENNReal.ofReal (actualExtendedThirdFiniteKernel e m ![x, y, z])) x := by
            apply lintegral_congr
            intro x
            by_cases hx : x ∈ Ioc z thirdPrefixRho
            · rw [indicator_of_mem hx]
              simp_rw [hvec, indicator_of_mem hz, indicator_of_mem hx]
              exact lintegral_indicator measurableSet_Ioc _
            · rw [indicator_of_notMem hx]
              simp_rw [hvec, indicator_of_mem hz, indicator_of_notMem hx]
              exact lintegral_zero
          _ = _ := lintegral_indicator measurableSet_Ioc _
      · rw [indicator_of_notMem hz]
        simp_rw [hvec, indicator_of_notMem hz]
        simp only [lintegral_zero]

theorem actualExtendedThirdFiniteKernel_eq_core {e h x y z : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hz : 0 < z) (hzh : z ≤ h) (hzy : z ≤ y) (hyx : y ≤ x)
    (hx : x ≤ thirdPrefixRho) :
    actualExtendedThirdFiniteKernel e m ![x, y, z] =
      thirdPrefixCorrectionKernel (thirdPrefixTheta - 2 * e)
        (actualExtendedThirdFiniteLevel e m ![x, y, z]) x y z := by
  have ht : ![x, y, z] ∈ actualExtendedThirdClosedOrder := by
    simp only [actualExtendedThirdClosedOrder]
    exact ⟨hz.le, hzy, hyx⟩
  have hg := actualExtendedThirdFiniteLevel_tail_geometry (m := m) he0 he ht
    (by simpa only [Matrix.cons_val_zero] using hx)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hr := actualExtendedThirdFiniteLevel_le_root e m ![x, y, z]
  have hs := thirdPrefixTail_argument_ge_three (by norm_num [thirdPrefixTailMargin])
    hsmall hz hzh hg
  have hargs : (actualExtendedThirdFiniteLevel e m ![x, y, z] - x - y - z) / z ≤
      (thirdPrefixTheta - 2 * e - x - y - z) / z :=
    (div_le_div_iff_of_pos_right hz).mpr (by linarith)
  change actualExtendedThirdCapKernel e (actualExtendedThirdFiniteLevel e m ![x, y, z])
    x y z = _
  unfold actualExtendedThirdCapKernel thirdPrefixCorrectionKernel
  rw [actualExtendedThirdLowerFactor_of_two_le
      ((by norm_num : (2 : ℝ) ≤ 3).trans (hs.trans hargs)),
    actualExtendedThirdLowerFactor_of_two_le ((by norm_num : (2 : ℝ) ≤ 3).trans hs)]

theorem actualExtendedThirdFiniteOrderedTailMass_eq_core {e h : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdFiniteOrderedTailMass e m h =
      actualExtendedThirdFiniteNestedTailMass e m h := by
  rw [actualExtendedThirdFiniteOrderedTailMass_eq_nested]
  unfold actualExtendedThirdFiniteNestedTailMass thirdPrefixTailMass
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro z hz
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change ENNReal.ofReal (actualExtendedThirdFiniteKernel e m ![x, y, z]) =
    ENNReal.ofReal (if x + y + 3 * z < thirdPrefixTheta - 2 * e then
      thirdPrefixCorrectionKernel (thirdPrefixTheta - 2 * e)
        (actualExtendedThirdFiniteLevel e m ![x, y, z]) x y z else 0)
  have ht : ![x, y, z] ∈ actualExtendedThirdClosedOrder := by
    simp only [actualExtendedThirdClosedOrder]
    exact ⟨hz.1.le, hy.1.le, hy.2⟩
  have hg := actualExtendedThirdFiniteLevel_tail_geometry (m := m) he0 he ht
    (by simpa only [Matrix.cons_val_zero] using hx.2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
  have hcube := thirdPrefixTail_ownCube_lt hsmall hz.1 hz.2 hg
  have hroot := actualExtendedThirdFiniteLevel_le_root e m ![x, y, z]
  have hold : x + y + 3 * z < thirdPrefixTheta - 2 * e := hcube.trans_le hroot
  rw [if_pos hold, actualExtendedThirdFiniteKernel_eq_core he0 he hsmall
    hz.1 hz.2 hy.1.le hy.2 hx.2]

theorem actualExtendedThirdFiniteKernel_nonneg {e : ℝ} {m : ℕ} {t : Fin 3 → ℝ}
    (hz : 0 < t 2) (hzy : t 2 ≤ t 1) (hyx : t 1 ≤ t 0) :
    0 ≤ actualExtendedThirdFiniteKernel e m t := by
  have hroot := actualExtendedThirdFiniteLevel_le_root e m t
  have hargs : (actualExtendedThirdFiniteLevel e m t - t 0 - t 1 - t 2) / t 2 ≤
      (thirdPrefixTheta - 2 * e - t 0 - t 1 - t 2) / t 2 :=
    (div_le_div_iff_of_pos_right hz).mpr (by linarith)
  have hd := monotone_actualExtendedThirdLowerFactor hargs
  unfold actualExtendedThirdFiniteKernel actualExtendedThirdCapKernel
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hd))
    (le_of_lt (mul_pos (mul_pos (hz.trans_le (hzy.trans hyx)) (hz.trans_le hzy))
      (sq_pos_of_pos hz)))

/-- The actual physical tail in the manuscript's closed ordered coordinates,
measured by absolute mass before any real-valued integral is taken. -/
def actualExtendedThirdFiniteClosedTailMass (e : ℝ) (m : ℕ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdClosedOrderRegion h,
    ENNReal.ofReal |actualExtendedThirdFiniteKernel e m t|

theorem actualExtendedThirdFiniteClosedTailMass_eq_ordered (e h : ℝ) (m : ℕ) :
    actualExtendedThirdFiniteClosedTailMass e m h = actualExtendedThirdFiniteOrderedTailMass e m h := by
  unfold actualExtendedThirdFiniteClosedTailMass actualExtendedThirdFiniteOrderedTailMass
  rw [setLIntegral_congr (actualExtendedThirdClosedOrderRegion_ae_eq h)]
  apply setLIntegral_congr_fun (measurableSet_actualExtendedThirdOrderedTailRegion h)
  intro t ht
  dsimp only
  rw [abs_of_nonneg (actualExtendedThirdFiniteKernel_nonneg ht.1 ht.2.2.2.2.1.le ht.2.2.2.2.2)]

/-- A single cutoff is fixed before the buffer and grid, for the actual
tuple-space kernel. Both its measurable lookup and residual floor are paid. -/
theorem actualExtendedThirdFiniteClosedTailMass_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ thirdPrefixTailMargin / 4 ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 384 → ∀ m : ℕ,
        actualExtendedThirdFiniteClosedTailMass e m h ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hh, hs, hb⟩ := actualExtendedThirdFiniteNestedTailMass_uniform_small hε
  refine ⟨h, hh, hs, ?_⟩
  intro e he0 he m
  rw [actualExtendedThirdFiniteClosedTailMass_eq_ordered,
    actualExtendedThirdFiniteOrderedTailMass_eq_core he0 he hs]
  exact hb e he0 he m

end

end ImbalancedChen
