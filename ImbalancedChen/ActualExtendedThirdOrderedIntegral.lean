import ImbalancedChen.ActualExtendedThirdIdealCap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual extended third-prefix functional in ordered tuple coordinates

The manuscript extends the normalized lower sieve factor by zero below two.
We implement that extension by clamping the argument at two and prove its
measurability from the already verified monotonicity of the actual factor.
This avoids importing the unrelated compact arithmetic-density chain.

The ordered tail is a genuine integral on `Fin 3 -> Real` with its actual
half-open coordinate ownership and strict old own-cube gate. Tonelli, applied
to the explicit measurable kernel, identifies it with the nested tail from
the verified Core. The cap is the literal ideal extended envelope. No finite
robust-policy approximation or same-policy prime asymptotic is claimed here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open VariableEnvelope
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped ENNReal

theorem thirdTailLowerFactor_two : thirdTailLowerFactor 2 = 0 := by
  have hlower : suzukiContinuousLowerFactor 2 = 0 := by
    rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
      one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
        jr1965Section13HatSourceContract (by norm_num : (2 : ℝ) ≤ 2)
        (by norm_num : (2 : ℝ) ≤ 4),
      suzukiLowerSieveFactorFirstInterval_eq_log (by norm_num : (2 : ℝ) ≤ 2)
        (by norm_num : (2 : ℝ) ≤ 4)]
    norm_num
  simp only [thirdTailLowerFactor, hlower, zero_div]

/-- The manuscript's actual normalized lower factor, extended by zero below two. -/
def actualExtendedThirdLowerFactor (s : ℝ) : ℝ := thirdTailLowerFactor (max 2 s)

theorem actualExtendedThirdLowerFactor_of_le_two {s : ℝ} (hs : s ≤ 2) :
    actualExtendedThirdLowerFactor s = 0 := by
  rw [actualExtendedThirdLowerFactor, max_eq_left hs, thirdTailLowerFactor_two]

theorem actualExtendedThirdLowerFactor_of_two_le {s : ℝ} (hs : 2 ≤ s) :
    actualExtendedThirdLowerFactor s = thirdTailLowerFactor s := by
  rw [actualExtendedThirdLowerFactor, max_eq_right hs]

theorem monotone_actualExtendedThirdLowerFactor : Monotone actualExtendedThirdLowerFactor := by
  intro s t hst
  unfold actualExtendedThirdLowerFactor thirdTailLowerFactor
  have hs : max (2 : ℝ) s ∈ Ici 2 := le_max_left 2 s
  have ht : max (2 : ℝ) t ∈ Ici 2 := le_max_left 2 t
  exact div_le_div_of_nonneg_right
    (thirdTail_lowerFactor_monotone hs ht
      (max_le_max le_rfl hst)) (by positivity)

theorem measurable_actualExtendedThirdLowerFactor : Measurable actualExtendedThirdLowerFactor :=
  monotone_actualExtendedThirdLowerFactor.measurable

def actualExtendedThirdOrderedKernel (e x y z : ℝ) : ℝ :=
  4 * (actualExtendedThirdLowerFactor ((thirdPrefixTheta - 2 * e - x - y - z) / z) -
    actualExtendedThirdLowerFactor ((actualExtendedThirdBufferedCap e x y z - x - y - z) / z)) /
      (x * y * z ^ 2)

def actualExtendedThirdGatedKernel (e x y z : ℝ) : ℝ :=
  if x + y + 3 * z < thirdPrefixTheta - 2 * e then
    actualExtendedThirdOrderedKernel e x y z else 0

theorem measurable_actualExtendedThirdOrderedKernel (e : ℝ) :
    Measurable (fun t : Fin 3 → ℝ => actualExtendedThirdOrderedKernel e (t 0) (t 1) (t 2)) := by
  have hx : Measurable (fun t : Fin 3 → ℝ => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : Fin 3 → ℝ => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : Fin 3 → ℝ => t 2) := (continuous_apply 2).measurable
  have hold : Measurable (fun t : Fin 3 → ℝ =>
      (thirdPrefixTheta - 2 * e - t 0 - t 1 - t 2) / t 2) :=
    (((measurable_const.sub hx).sub hy).sub hz).div hz
  have hnew : Measurable (fun t : Fin 3 → ℝ =>
      (actualExtendedThirdBufferedCap e (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2) :=
    ((((measurable_actualExtendedThirdBufferedCap e).sub hx).sub hy).sub hz).div hz
  unfold actualExtendedThirdOrderedKernel
  exact (measurable_const.mul
    ((measurable_actualExtendedThirdLowerFactor.comp hold).sub
      (measurable_actualExtendedThirdLowerFactor.comp hnew))).div
      ((hx.mul hy).mul (hz.pow_const 2))

theorem measurable_actualExtendedThirdGatedKernel (e : ℝ) :
    Measurable (fun t : Fin 3 → ℝ => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  unfold actualExtendedThirdGatedKernel
  exact (measurable_actualExtendedThirdOrderedKernel e).piecewise
    (isOpen_lt ((hx.add hy).add (hz.const_mul 3)) continuous_const).measurableSet
    measurable_const

/-- Coordinate order `(x,y,z)`, with precisely the Core's half-open ownership. -/
def actualExtendedThirdOrderedTailRegion (h : ℝ) : Set (Fin 3 → ℝ) :=
  {t | 0 < t 2 ∧ t 2 ≤ h ∧ t 2 < t 0 ∧ t 0 ≤ thirdPrefixRho ∧
    t 2 < t 1 ∧ t 1 ≤ t 0}

theorem measurableSet_actualExtendedThirdOrderedTailRegion (h : ℝ) :
    MeasurableSet (actualExtendedThirdOrderedTailRegion h) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  exact (isOpen_lt continuous_const hz).measurableSet.inter
    ((isClosed_le hz continuous_const).measurableSet.inter
      ((isOpen_lt hz hx).measurableSet.inter
        ((isClosed_le hx continuous_const).measurableSet.inter
          ((isOpen_lt hz hy).measurableSet.inter (isClosed_le hy hx).measurableSet))))

def actualExtendedThirdOrderedTailMass (e h : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in actualExtendedThirdOrderedTailRegion h,
    ENNReal.ofReal (actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2))

private theorem extended_insert_last_fin3 (q x y : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      (q, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x, y)) = ![x, y, q] := by
  ext i
  fin_cases i <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth, Fin.succAboveCases, MeasurableEquiv.piFinTwo]

/-- Actual Tonelli bridge; measurability is paid by the explicit capped kernel,
not supplied as a premise on the original functional. -/
theorem actualExtendedThirdOrderedTailMass_eq_nested (e h : ℝ) :
    actualExtendedThirdOrderedTailMass e h =
      ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z thirdPrefixRho, ∫⁻ y in Ioc z x,
        ENNReal.ofReal (actualExtendedThirdGatedKernel e x y z) := by
  let F : (Fin 3 → ℝ) → ℝ≥0∞ := (actualExtendedThirdOrderedTailRegion h).indicator
    (fun t => ENNReal.ofReal (actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)))
  have hF : Measurable F := (measurable_actualExtendedThirdGatedKernel e).ennreal_ofReal.indicator
    (measurableSet_actualExtendedThirdOrderedTailRegion h)
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  let E₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinSuccAbove _ 2
  have hE₂ : MeasurePreserving E₂ := volume_preserving_piFinTwo _
  have hvec (x y z : ℝ) : F ![x, y, z] =
      (Ioc 0 h).indicator (fun z => (Ioc z thirdPrefixRho).indicator
        (fun x => (Ioc z x).indicator
          (fun y => ENNReal.ofReal (actualExtendedThirdGatedKernel e x y z)) y) x) z := by
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
      simp_all [F, Set.indicator_apply, Matrix.cons_val_two]
  calc
    actualExtendedThirdOrderedTailMass e h = ∫⁻ t, F t :=
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
        _ = _ := by simp only [E, E₂, extended_insert_last_fin3]
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Ioc 0 h
      · rw [indicator_of_mem hz]
        calc
          _ = ∫⁻ x : ℝ, (Ioc z thirdPrefixRho).indicator
              (fun x => ∫⁻ y in Ioc z x,
                ENNReal.ofReal (actualExtendedThirdGatedKernel e x y z)) x := by
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

theorem actualExtendedThirdOrderedKernel_eq_core {e h x y z : ℝ}
    (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4)
    (hz : 0 < z) (hzh : z ≤ h) (hzy : z ≤ y) (hyx : y ≤ x)
    (hx : x ≤ thirdPrefixRho) :
    actualExtendedThirdOrderedKernel e x y z =
      thirdPrefixCorrectionKernel (thirdPrefixTheta - 2 * e)
        (actualExtendedThirdBufferedCap e x y z) x y z := by
  have hg := actualExtendedThirdBufferedCap_tail_geometry (z := z) he
    (hz.le.trans (hzy.trans hyx)) hx (hyx.trans hx)
  have hs := thirdPrefixTail_argument_ge_three (by norm_num [thirdPrefixTailMargin])
    hsmall hz hzh hg.1
  have hargs : (actualExtendedThirdBufferedCap e x y z - x - y - z) / z ≤
      (thirdPrefixTheta - 2 * e - x - y - z) / z :=
    (div_le_div_iff_of_pos_right hz).mpr (by linarith [hg.2])
  unfold actualExtendedThirdOrderedKernel thirdPrefixCorrectionKernel
  rw [actualExtendedThirdLowerFactor_of_two_le ((by norm_num : (2 : ℝ) ≤ 3).trans (hs.trans hargs)),
    actualExtendedThirdLowerFactor_of_two_le ((by norm_num : (2 : ℝ) ≤ 3).trans hs)]

/-- The actual ordered tuple-space integral is exactly the verified Core mass
throughout the small tail, with the original old-cube gate retained. -/
theorem actualExtendedThirdOrderedTailMass_eq_core {e h : ℝ}
    (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdOrderedTailMass e h = actualExtendedThirdIdealTailMass e h := by
  rw [actualExtendedThirdOrderedTailMass_eq_nested]
  unfold actualExtendedThirdIdealTailMass thirdPrefixTailMass
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro z hz
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro y hy
  change ENNReal.ofReal (actualExtendedThirdGatedKernel e x y z) =
    ENNReal.ofReal (if x + y + 3 * z < thirdPrefixTheta - 2 * e then
      thirdPrefixCorrectionKernel (thirdPrefixTheta - 2 * e)
        (actualExtendedThirdBufferedCap e x y z) x y z else 0)
  unfold actualExtendedThirdGatedKernel
  rw [actualExtendedThirdOrderedKernel_eq_core he hsmall hz.1 hz.2 hy.1.le hy.2 hx.2]

theorem actualExtendedThirdOrderedTailMass_ne_top {e h : ℝ}
    (he : e ≤ 1 / 384) (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdOrderedTailMass e h ≠ ∞ := by
  rw [actualExtendedThirdOrderedTailMass_eq_core he hsmall]
  exact actualExtendedThirdIdealTailMass_ne_top he hh hsmall

theorem actualExtendedThirdGatedKernel_nonneg_on_region (e h : ℝ)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdOrderedTailRegion h) :
    0 ≤ actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2) := by
  rcases ht with ⟨hz, _hzh, hzx, _hx, hzy, _hyx⟩
  have hcap := thirdPrefixBufferedCap_le_root e
    (actualExtendedThirdEnvelope (t 0) (t 1) (t 2))
  have hargs : (actualExtendedThirdBufferedCap e (t 0) (t 1) (t 2) - t 0 - t 1 - t 2) / t 2 ≤
      (thirdPrefixTheta - 2 * e - t 0 - t 1 - t 2) / t 2 :=
    (div_le_div_iff_of_pos_right hz).mpr (by
      change actualExtendedThirdBufferedCap e (t 0) (t 1) (t 2) ≤ thirdPrefixTheta - 2 * e at hcap
      linarith)
  have hd := monotone_actualExtendedThirdLowerFactor hargs
  unfold actualExtendedThirdGatedKernel
  split_ifs
  · unfold actualExtendedThirdOrderedKernel
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hd))
      (le_of_lt (mul_pos (mul_pos (hz.trans hzx) (hz.trans hzy)) (sq_pos_of_pos hz)))
  · exact le_rfl

/-- Finiteness of the positive tuple-space mass pays Bochner integrability;
the real integral is not justified by its value being defined to be zero. -/
theorem integrableOn_actualExtendedThirdGatedKernel {e h : ℝ}
    (he : e ≤ 1 / 384) (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    IntegrableOn (fun t : Fin 3 → ℝ => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2))
      (actualExtendedThirdOrderedTailRegion h) := by
  refine ⟨(measurable_actualExtendedThirdGatedKernel e).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hnorm : (∫⁻ t in actualExtendedThirdOrderedTailRegion h,
      ENNReal.ofReal ‖actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)‖) =
      actualExtendedThirdOrderedTailMass e h := by
    apply setLIntegral_congr_fun (measurableSet_actualExtendedThirdOrderedTailRegion h)
    intro t ht
    change ENNReal.ofReal ‖actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)‖ =
      ENNReal.ofReal (actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2))
    rw [Real.norm_eq_abs, abs_of_nonneg (actualExtendedThirdGatedKernel_nonneg_on_region e h ht)]
  rw [hnorm]
  exact lt_top_iff_ne_top.mpr (actualExtendedThirdOrderedTailMass_ne_top he hh hsmall)

theorem integral_actualExtendedThirdGatedKernel_eq_core {e h : ℝ}
    (he : e ≤ 1 / 384) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    (∫ t in actualExtendedThirdOrderedTailRegion h,
      actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) =
      (actualExtendedThirdIdealTailMass e h).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (actualExtendedThirdOrderedTailRegion h)]
      (fun t : Fin 3 → ℝ => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)) := by
    apply (ae_restrict_iff' (measurableSet_actualExtendedThirdOrderedTailRegion h)).2
    exact ae_of_all _ (fun t ht => actualExtendedThirdGatedKernel_nonneg_on_region e h ht)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_actualExtendedThirdGatedKernel e).aestronglyMeasurable]
  exact congrArg ENNReal.toReal (actualExtendedThirdOrderedTailMass_eq_core he hsmall)

end

end ImbalancedChen
