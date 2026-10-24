import ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
import ImbalancedChen.P2SavedFloorSubdivisionEstimator
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE_WRITTEN_UNCOMPILED. No producer, Lean, runtime or replay was run.

The source defect is 4*h(R/a)/(R*t*u), R=57/64-(5/2)t-u on the
ordinary high-t branch. It is NOT h((1-t-u)/a)/(t*u).

The lower h licence is refused below s=2. Its literal semantic extension
below two is zero, with s=2 retained. No continuity at that wall is asserted.
Actual Wu-h antitonicity on [2,5], nonnegativity and boundedness give a
measurable bounded global extension. Fubini on the two finite restricted
Lebesgue measures proves inner and outer integrability of the literal
kernel. The preceding logmass comparison consequently needs no assumed
integrability. Table endpoint licences remain explicit local inputs.
-/

namespace ImbalancedChen.P2HistoricDefectIntegralMeasurability

noncomputable section

open Set MeasureTheory Wu2008DoubleSieve P2SavedFloorSemantics
open P2HistoricQ80OrdinaryEstimatorSoundness
open scoped Interval

def clampArgument (s : ℝ) : ℝ := max 2 (min 5 s)

theorem clampArgument_domain (s : ℝ) : clampArgument s ∈ Icc (2 : ℝ) 5 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

def clampedH (δ s : ℝ) : ℝ := P2TableActionSourceOnly.h δ (clampArgument s)

theorem clampedH_antitone {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    Antitone (clampedH δ) := by
  intro x y hxy
  have hx := clampArgument_domain x
  have hy := clampArgument_domain y
  have hclamp : clampArgument x ≤ clampArgument y :=
    max_le_max_left 2 (min_le_min_left 5 hxy)
  exact wuImprovementLimit_lower_antitone hδ hδhi
    ⟨hx.1, hx.2.trans (by norm_num : (5 : ℝ) ≤ 10)⟩
    ⟨hy.1, hy.2.trans (by norm_num : (5 : ℝ) ≤ 10)⟩ hclamp

theorem clampedH_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (s : ℝ) :
    0 ≤ clampedH δ s ∧ clampedH δ s ≤ P2TableActionSourceOnly.h δ 2 := by
  have hs := clampArgument_domain s
  constructor
  · exact wuImprovementLimit_nonneg false hδ (by linarith : δ < 1 / 2)
      (by linarith [hs.1] : 1 ≤ clampArgument s)
      (hs.2.trans (by norm_num : (5 : ℝ) ≤ 10))
  · exact wuImprovementLimit_lower_antitone hδ hδhi
      ⟨by norm_num, by norm_num⟩
      ⟨hs.1, hs.2.trans (by norm_num : (5 : ℝ) ≤ 10)⟩ hs.1

/-- Globally bounded measurable extension used only for integrability. -/
def boundedGuardedH (δ : ℝ) : ℝ → ℝ := (Ici (2 : ℝ)).indicator (clampedH δ)

/-- Literal zero extension of the actual source h; equality is retained. -/
def guardedH (δ : ℝ) : ℝ → ℝ := (Ici (2 : ℝ)).indicator (P2TableActionSourceOnly.h δ)

theorem guardedH_below_two (δ : ℝ) {s : ℝ} (hs : s < 2) : guardedH δ s = 0 := by
  simp [guardedH, Set.indicator_of_not_mem, not_le.mpr hs]

theorem guardedH_at_two (δ : ℝ) : guardedH δ 2 = P2TableActionSourceOnly.h δ 2 := by
  simp [guardedH]

theorem measurable_boundedGuardedH {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    Measurable (boundedGuardedH δ) := by
  exact (clampedH_antitone hδ hδhi).measurable.indicator measurableSet_Ici

theorem boundedGuardedH_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (s : ℝ) :
    0 ≤ boundedGuardedH δ s ∧
      boundedGuardedH δ s ≤ P2TableActionSourceOnly.h δ 2 := by
  by_cases hs : s ∈ Ici (2 : ℝ)
  · simpa only [boundedGuardedH, Set.indicator_of_mem hs] using clampedH_bounds hδ hδhi s
  · have hb := clampedH_bounds hδ hδhi s
    simp only [boundedGuardedH, Set.indicator_of_not_mem hs]
    exact ⟨le_rfl, hb.1.trans hb.2⟩

theorem boundedGuardedH_eq_guardedH (δ : ℝ) {s : ℝ} (hs : s ≤ 5) :
    boundedGuardedH δ s = guardedH δ s := by
  by_cases hs2 : 2 ≤ s
  · have hc : clampArgument s = s := by
      simp only [clampArgument, min_eq_right hs, max_eq_right hs2]
    simp only [boundedGuardedH, guardedH, Set.indicator_of_mem hs2, clampedH, hc]
  · simp only [boundedGuardedH, guardedH, Set.indicator_of_not_mem hs2]

/-- The literal rounded lower lookup really returns zero when the exact
residual input crosses below two; this is not a chosen analytic convention. -/
theorem literalLookup_real_crossing (table : ℤ → ℤ) {rl rh : ℚ}
    (hrl : rl < 2 * Certificates.P2HistoricQ80DefectLookup.a) :
    Certificates.P2HistoricQ80DefectLookup.defectLookup 50 table
      (Certificates.P2HistoricQ80DefectLookup.I80.ofEnclosure
        ⟨rl / Certificates.P2HistoricQ80DefectLookup.a,
          rh / Certificates.P2HistoricQ80DefectLookup.a⟩) true =
      Certificates.P2HistoricQ80DefectLookup.I80.raw 0 := by
  apply Certificates.P2HistoricQ80DefectLookup.defectLookup_lower_crossing
  change ⌊(rl / Certificates.P2HistoricQ80DefectLookup.a) *
      (Certificates.P2HistoricQ80DefectLookup.Q:ℚ)⌋ <
    2 * (Certificates.P2HistoricQ80DefectLookup.Q:ℤ)
  apply Int.floor_lt.mpr
  have ha : (0:ℚ) < Certificates.P2HistoricQ80DefectLookup.a := by
    norm_num [Certificates.P2HistoricQ80DefectLookup.a]
  have hs : rl / Certificates.P2HistoricQ80DefectLookup.a < 2 :=
    (div_lt_iff₀ ha).mpr hrl
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
    mul_lt_mul_of_pos_right hs Certificates.P2HistoricQ80DefectLookup.Q_pos

def guardedDefectKernel (δ t u : ℝ) : ℝ :=
  4 * guardedH δ (ordinaryResidual t u / ordinaryA) / (ordinaryResidual t u * t * u)

def guardedDefectIntegral (δ tl tr ul ur : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, guardedDefectKernel δ t u

/-- Denominators are clamped only in the proof's global extension.
The extension is proved equal to the literal kernel on the whole cell. -/
def defectExtension (δ tl ul rl : ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * boundedGuardedH δ (ordinaryResidual p.1 p.2 / ordinaryA) /
    (max rl (ordinaryResidual p.1 p.2) * max tl p.1 * max ul p.2)

theorem measurable_defectExtension {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (tl ul rl : ℝ) : Measurable (defectExtension δ tl ul rl) := by
  have hr : Continuous (fun p : ℝ × ℝ => ordinaryResidual p.1 p.2) := by
    unfold ordinaryResidual
    fun_prop
  have hn : Measurable (fun p : ℝ × ℝ =>
      4 * boundedGuardedH δ (ordinaryResidual p.1 p.2 / ordinaryA)) :=
    measurable_const.mul ((measurable_boundedGuardedH hδ hδhi).comp
      (hr.div_const ordinaryA).measurable)
  exact hn.div
    (((continuous_const.max hr).mul (continuous_const.max continuous_fst)).mul
      (continuous_const.max continuous_snd)).measurable

theorem defectExtension_norm_bound {δ tl ul rl : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl) (p : ℝ × ℝ) :
    ‖defectExtension δ tl ul rl p‖ ≤
      4 * P2TableActionSourceOnly.h δ 2 / (rl * tl * ul) := by
  have hr0 : 0 < max rl (ordinaryResidual p.1 p.2) := hrl.trans_le (le_max_left _ _)
  have ht0 : 0 < max tl p.1 := htl.trans_le (le_max_left _ _)
  have hu0 : 0 < max ul p.2 := hul.trans_le (le_max_left _ _)
  have hd0 : 0 < max rl (ordinaryResidual p.1 p.2) * max tl p.1 * max ul p.2 := by positivity
  have hbase0 : 0 < rl * tl * ul := by positivity
  have hd1 : rl * tl ≤ max rl (ordinaryResidual p.1 p.2) * max tl p.1 :=
    mul_le_mul (le_max_left _ _) (le_max_left _ _) htl.le hr0.le
  have hd : rl * tl * ul ≤ max rl (ordinaryResidual p.1 p.2) * max tl p.1 * max ul p.2 :=
    mul_le_mul hd1 (le_max_left _ _) hul.le (mul_nonneg hr0.le ht0.le)
  have hb := boundedGuardedH_bounds hδ hδhi (ordinaryResidual p.1 p.2 / ordinaryA)
  have hh2 : 0 ≤ P2TableActionSourceOnly.h δ 2 := hb.1.trans hb.2
  have hn : 0 ≤ defectExtension δ tl ul rl p :=
    div_nonneg (mul_nonneg (by norm_num) hb.1) hd0.le
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    defectExtension δ tl ul rl p ≤
        (4 * P2TableActionSourceOnly.h δ 2) /
          (max rl (ordinaryResidual p.1 p.2) * max tl p.1 * max ul p.2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2 (by norm_num)) hd0.le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hh2) hbase0 hd

theorem defectExtension_eq_literal {δ tl tr ul ur rl t u : ℝ}
    (ht : t ∈ Icc tl tr) (hu : u ∈ Icc ul ur)
    (hrl : rl ≤ ordinaryResidual t u) (hs5 : ordinaryResidual t u / ordinaryA ≤ 5) :
    defectExtension δ tl ul rl (t,u) = guardedDefectKernel δ t u := by
  simp only [defectExtension, guardedDefectKernel, max_eq_right hrl,
    max_eq_right ht.1, max_eq_right hu.1, boundedGuardedH_eq_guardedH δ hs5]

theorem guardedDefect_norm_on_rectangle {δ tl tr ul ur rl rh t u : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl)
    (ht : t ∈ Icc tl tr) (hu : u ∈ Icc ul ur)
    (hrange : ordinaryResidual t u ∈ Icc rl rh) (hhi : rh / ordinaryA ≤ 5) :
    ‖guardedDefectKernel δ t u‖ ≤
      4 * P2TableActionSourceOnly.h δ 2 / (rl * tl * ul) := by
  rw [← defectExtension_eq_literal ht hu hrange.1
    ((div_le_div_of_nonneg_right hrange.2 ordinaryA_pos.le).trans hhi)]
  exact defectExtension_norm_bound hδ hδhi htl hul hrl (t,u)

/-- Joint integrability and hence joint AE measurability hold for the
literal kernel on the actual product of restricted parent measures. -/
theorem guardedDefect_joint_integrable {δ tl tr ul ur rl rh : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) :
    Integrable (fun p : ℝ × ℝ => guardedDefectKernel δ p.1 p.2)
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc ul ur))) := by
  have hext : Integrable (defectExtension δ tl ul rl)
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc ul ur))) := by
    apply Integrable.of_bound
      (measurable_defectExtension hδ hδhi tl ul rl).aestronglyMeasurable
      (4 * P2TableActionSourceOnly.h δ 2 / (rl * tl * ul))
    exact Filter.Eventually.of_forall (defectExtension_norm_bound hδ hδhi htl hul hrl)
  apply hext.congr
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  have ht : p.1 ∈ Icc tl tr := ⟨hp.1.1.le,hp.1.2⟩
  have hu : p.2 ∈ Icc ul ur := ⟨hp.2.1.le,hp.2.2⟩
  exact defectExtension_eq_literal ht hu (hrange p.1 ht p.2 hu).1
    ((div_le_div_of_nonneg_right (hrange p.1 ht p.2 hu).2 ordinaryA_pos.le).trans hhi)

theorem guardedDefect_joint_aemeasurable {δ tl tr ul ur rl rh : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) :
    AEMeasurable (fun p : ℝ × ℝ => guardedDefectKernel δ p.1 p.2)
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc ul ur))) := by
  exact (guardedDefect_joint_integrable hδ hδhi htl hul hrl hrange hhi).aemeasurable

/-- Inner AND outer integrability of the literal guarded kernel, including
cells crossing s=2. No continuity or integrability hypothesis is supplied. -/
theorem guardedDefect_integrability {δ tl tr ul ur rl rh : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl)
    (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) :
    (∀ t ∈ Icc tl tr, IntervalIntegrable (guardedDefectKernel δ t) volume ul ur) ∧
      IntervalIntegrable (fun t => ∫ u in ul..ur, guardedDefectKernel δ t u) volume tl tr := by
  let μt : Measure ℝ := volume.restrict (Ioc tl tr)
  let μu : Measure ℝ := volume.restrict (Ioc ul ur)
  let ext := defectExtension δ tl ul rl
  let C : ℝ := 4 * P2TableActionSourceOnly.h δ 2 / (rl * tl * ul)
  letI : IsFiniteMeasure μt := by dsimp [μt]; infer_instance
  letI : IsFiniteMeasure μu := by dsimp [μu]; infer_instance
  have hm : Measurable ext := measurable_defectExtension hδ hδhi tl ul rl
  have hb : ∀ p, ‖ext p‖ ≤ C := defectExtension_norm_bound hδ hδhi htl hul hrl
  have hprod : Integrable ext (μt.prod μu) := by
    apply Integrable.of_bound hm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall hb
  have hslice (t : ℝ) : Integrable (fun u => ext (t,u)) μu := by
    apply Integrable.of_bound
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) C
    exact Filter.Eventually.of_forall (fun u => hb (t,u))
  have heq : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur,
      ext (t,u) = guardedDefectKernel δ t u := by
    intro t ht' u hu'
    exact defectExtension_eq_literal ht' hu' (hrange t ht' u hu').1
      ((div_le_div_of_nonneg_right (hrange t ht' u hu').2 ordinaryA_pos.le).trans hhi)
  constructor
  · intro t ht'
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).mpr
    apply (hslice t).congr
    change (fun u => ext (t,u)) =ᵐ[volume.restrict (Ioc ul ur)] guardedDefectKernel δ t
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu'
    exact heq t ht' u ⟨hu'.1.le,hu'.2⟩
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
    apply hprod.integral_prod_left.congr
    change (fun t => ∫ u, ext (t,u) ∂μu) =ᵐ[volume.restrict (Ioc tl tr)]
      (fun t => ∫ u in ul..ur, guardedDefectKernel δ t u)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht'
    have htIcc : t ∈ Icc tl tr := ⟨ht'.1.le,ht'.2⟩
    calc
      (∫ u, ext (t,u) ∂μu) = ∫ u in ul..ur, ext (t,u) := by
        dsimp [μu]
        exact (intervalIntegral.integral_of_le hu).symm
      _ = ∫ u in ul..ur, guardedDefectKernel δ t u := by
        apply intervalIntegral.integral_congr
        intro u hu'
        rw [Set.uIcc_of_le hu] at hu'
        exact heq t htIcc u hu'

theorem guardedDefect_eq_actual_of_two_le {δ t u : ℝ}
    (hs : 2 ≤ ordinaryResidual t u / ordinaryA) :
    guardedDefectKernel δ t u = actualDefectKernel δ t u := by
  simp only [guardedDefectKernel, actualDefectKernel, guardedH, Set.indicator_of_mem hs]

/-- The previously explicit integrability obligations are now discharged
for every positive lower-defect cell with the source's s>=2 guard. -/
theorem actualDefect_integrability {δ tl tr ul ur rl rh : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hlo : 2 * ordinaryA ≤ rl)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) :
    (∀ t ∈ Icc tl tr, IntervalIntegrable (actualDefectKernel δ t) volume ul ur) ∧
      IntervalIntegrable (fun t => ∫ u in ul..ur, actualDefectKernel δ t u) volume tl tr := by
  have hrl : 0 < rl := by have := ordinaryA_pos; linarith
  have hi := guardedDefect_integrability hδ hδhi htl hul hrl ht hu hrange hhi
  have heq : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur,
      guardedDefectKernel δ t u = actualDefectKernel δ t u := by
    intro t ht' u hu'
    apply guardedDefect_eq_actual_of_two_le
    exact (le_div_iff₀ ordinaryA_pos).mpr (hlo.trans (hrange t ht' u hu').1)
  constructor
  · intro t ht'
    apply (hi.1 t ht').congr
    intro u hu'
    rw [Set.uIoc_of_le hu] at hu'
    exact heq t ht' u ⟨hu'.1.le,hu'.2⟩
  · apply hi.2.congr
    intro t ht'
    rw [Set.uIoc_of_le ht] at ht'
    apply intervalIntegral.integral_congr
    intro u hu'
    rw [Set.uIcc_of_le hu] at hu'
    exact heq t ⟨ht'.1.le,ht'.2⟩ u hu'

/-- Actual defect logmass lower bound with NO integrability premises. -/
theorem actual_defect_logmass_sound_no_integrability {δ tl tr ul ur rl rh hlow : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hlo : 2 * ordinaryA ≤ rl)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) (hh0 : 0 ≤ hlow)
    (hh : hlow ≤ P2TableActionSourceOnly.h δ (rh / ordinaryA)) :
    4 * hlow * realMass tl tr ul ur / rh ≤
      ∫ t in tl..tr, ∫ u in ul..ur, actualDefectKernel δ t u := by
  have hi := actualDefect_integrability hδ hδhi htl hul ht hu hlo hrange hhi
  exact actual_defect_logmass_sound hδ hδhi htl hul ht hu hlo hrange hhi hh0 hh hi.1 hi.2

theorem guarded_defect_integral_nonneg {δ tl tr ul ur rl rh : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) : 0 ≤ guardedDefectIntegral δ tl tr ul ur := by
  apply intervalIntegral.integral_nonneg ht
  intro t ht'
  apply intervalIntegral.integral_nonneg hu
  intro u hu'
  have hs5 := (div_le_div_of_nonneg_right (hrange t ht' u hu').2 ordinaryA_pos.le).trans hhi
  have hb := (boundedGuardedH_bounds hδ hδhi (ordinaryResidual t u / ordinaryA)).1
  rw [boundedGuardedH_eq_guardedH δ hs5] at hb
  exact div_nonneg (mul_nonneg (by norm_num) hb)
    (mul_nonneg (mul_nonneg (hrl.trans_le (hrange t ht' u hu').1).le
      (htl.trans_le ht'.1).le) (hul.trans_le hu'.1).le)

/-- Full guarded real lower-estimator semantics. A crossing input must
have table minimum zero, exactly as in the literal source lookup guard.
The nonzero branch retains only the local actual-h endpoint licence. -/
theorem guarded_defect_logmass_lower {δ tl tr ul ur rl rh hlow : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (htl : 0 < tl) (hul : 0 < ul) (hrl : 0 < rl) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hrange : ∀ t ∈ Icc tl tr, ∀ u ∈ Icc ul ur, ordinaryResidual t u ∈ Icc rl rh)
    (hhi : rh / ordinaryA ≤ 5) (hh0 : 0 ≤ hlow)
    (hcross : rl < 2 * ordinaryA → hlow = 0)
    (hh : 2 * ordinaryA ≤ rl → hlow ≤ P2TableActionSourceOnly.h δ (rh / ordinaryA)) :
    4 * hlow * realMass tl tr ul ur / rh ≤ guardedDefectIntegral δ tl tr ul ur := by
  by_cases hlo : 2 * ordinaryA ≤ rl
  · have ha := actual_defect_logmass_sound_no_integrability hδ hδhi htl hul ht hu
      hlo hrange hhi hh0 (hh hlo)
    have heq : guardedDefectIntegral δ tl tr ul ur =
        ∫ t in tl..tr, ∫ u in ul..ur, actualDefectKernel δ t u := by
      apply intervalIntegral.integral_congr
      intro t ht'
      rw [Set.uIcc_of_le ht] at ht'
      apply intervalIntegral.integral_congr
      intro u hu'
      rw [Set.uIcc_of_le hu] at hu'
      exact guardedDefect_eq_actual_of_two_le ((le_div_iff₀ ordinaryA_pos).mpr
        (hlo.trans (hrange t ht' u hu').1))
    rw [heq]
    exact ha
  · rw [hcross (lt_of_not_ge hlo)]
    simp only [mul_zero, zero_mul, zero_div]
    exact guarded_defect_integral_nonneg hδ hδhi htl hul hrl ht hu hrange hhi

/-! The actual imported pair512 grid discharges all geometric and positive
denominator requirements, including every crossing cell. -/

open P2SavedFloorSubdivisionEstimator

def parentResidualLower : ℝ := ordinaryResidual (59 / 250) (19 / 125)
def parentResidualUpper : ℝ := ordinaryResidual (25 / 128) (417 / 5000)

theorem parentResidualLower_pos : 0 < parentResidualLower := by
  norm_num [parentResidualLower, ordinaryResidual]

theorem parentResidualUpper_guard : parentResidualUpper / ordinaryA ≤ 5 := by
  norm_num [parentResidualUpper, ordinaryResidual, ordinaryA]

theorem actual_savedParent_residual_bounds (i j : Fin 512) :
    ∀ t ∈ Icc (parentTL i) (parentTR i), ∀ u ∈ Icc (parentUL j) (parentUR j),
      ordinaryResidual t u ∈ Icc parentResidualLower parentResidualUpper := by
  rcases parent_coordinates i j with ⟨_htl, htr, hul, hur⟩
  rcases parent_geometry i j with ⟨_ht0, _hu0, _htord, _huord, hmu⟩
  have hi : (i.val : ℝ) + 1 ≤ 512 := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hj : (j.val : ℝ) + 1 ≤ 512 := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hj0 : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have htmax : parentTR i ≤ (59 / 250 : ℝ) := by rw [htr]; nlinarith
  have humax : parentUR j ≤ (19 / 125 : ℝ) := by rw [hur]; nlinarith
  have humin : (417 / 5000 : ℝ) ≤ parentUL j := by rw [hul]; nlinarith
  intro t ht u hu
  exact ⟨ordinaryResidual_antitone (ht.2.trans htmax) (hu.2.trans humax),
    ordinaryResidual_antitone (hmu.trans ht.1) (humin.trans hu.1)⟩

/-- Concrete actual-parent integrability, with no residual-bound,
measurability, continuity or integrability premises beyond the source's
fixed delta domain. -/
theorem actual_savedParent_defect_integrability {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (i j : Fin 512) :
    (∀ t ∈ Icc (parentTL i) (parentTR i),
      IntervalIntegrable (guardedDefectKernel δ t) volume (parentUL j) (parentUR j)) ∧
      IntervalIntegrable
        (fun t => ∫ u in (parentUL j)..(parentUR j), guardedDefectKernel δ t u)
        volume (parentTL i) (parentTR i) := by
  rcases parent_geometry i j with ⟨htl, hul, ht, hu, _hmu⟩
  exact guardedDefect_integrability hδ hδhi htl hul parentResidualLower_pos ht hu
    (actual_savedParent_residual_bounds i j) parentResidualUpper_guard

theorem actual_savedParent_defect_joint_aemeasurable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (i j : Fin 512) :
    AEMeasurable (fun p : ℝ × ℝ => guardedDefectKernel δ p.1 p.2)
      ((volume.restrict (Ioc (parentTL i) (parentTR i))).prod
        (volume.restrict (Ioc (parentUL j) (parentUR j)))) := by
  rcases parent_geometry i j with ⟨htl, hul, _ht, _hu, _hmu⟩
  exact guardedDefect_joint_aemeasurable hδ hδhi htl hul parentResidualLower_pos
    (actual_savedParent_residual_bounds i j) parentResidualUpper_guard

end

end ImbalancedChen.P2HistoricDefectIntegralMeasurability
