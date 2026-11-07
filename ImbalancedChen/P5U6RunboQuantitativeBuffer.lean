import ImbalancedChen.CurrentChenUpsilon6KernelBuffer
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real

/-!
SOURCE_ONLY / UNCOMPILED. Quantitative loss for the literal Runbo product
buffer. Reverse Fubini computes the containing slanted strip's area exactly:
(59/250-19/125)*eta = (21/250)*eta. The actual discarded set retains both
original prime bands. No asymptotic boundary estimate is assumed.

The bounded-kernel estimate accepts an a.e. bound on the actual unbuffered
domain. Concrete reciprocal and ordinary kernels have explicit bounds
625000/7923 and 4000. This supplies explicit eta budgets, without evaluating
the original enhanced h248 estimator or its adopted L6 constant.
-/

namespace ImbalancedChen.P5U6RunboQuantitativeBufferSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Classical

abbrev Point := Fin 2 → ℝ

def discarded (eta : ℝ) : Set Point :=
  currentChenUpsilon6LogDomain 0 \ currentChenUpsilon6LogDomain eta

private def slantedStrip (eta : ℝ) : Set (ℝ × ℝ) :=
  {p | (19 / 125 : ℝ) ≤ p.2 ∧ p.2 < 59 / 250 ∧
    (833 / 2500 : ℝ) - eta - p.2 < p.1 ∧ p.1 ≤ (833 / 2500 : ℝ) - p.2}

private theorem measurableSet_slantedStrip (eta : ℝ) :
    MeasurableSet (slantedStrip eta) := by
  unfold slantedStrip
  exact ((isClosed_le continuous_const continuous_snd).measurableSet).inter
    (((isOpen_lt continuous_snd continuous_const).measurableSet).inter
      (((isOpen_lt (continuous_const.sub continuous_snd) continuous_fst).measurableSet).inter
        (isClosed_le continuous_fst (continuous_const.sub continuous_snd)).measurableSet))

private theorem slantedStrip_section (eta t : ℝ) :
    volume ((fun u : ℝ => (u, t)) ⁻¹' slantedStrip eta) =
      (Ico (19 / 125 : ℝ) (59 / 250)).indicator
        (fun _ => ENNReal.ofReal eta) t := by
  by_cases ht : t ∈ Ico (19 / 125 : ℝ) (59 / 250)
  · rw [indicator_of_mem ht]
    have hset : (fun u : ℝ => (u, t)) ⁻¹' slantedStrip eta =
        Ioc ((833 / 2500 : ℝ) - eta - t) ((833 / 2500 : ℝ) - t) := by
      ext u
      simp only [mem_preimage, slantedStrip, mem_setOf_eq, mem_Ioc]
      exact ⟨fun h => h.2.2, fun h => ⟨ht.1, ht.2, h⟩⟩
    rw [hset, Real.volume_Ioc]
    congr 1
    ring
  · rw [indicator_of_notMem ht]
    have hset : (fun u : ℝ => (u, t)) ⁻¹' slantedStrip eta = ∅ := by
      ext u
      simp only [mem_preimage, slantedStrip, mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      exact ht ⟨h.1, h.2.1⟩
    rw [hset, measure_empty]

/-- Fubini integrates the exact interval length eta in the first coordinate.
The original second-coordinate width is 21/250, not the full unit interval. -/
private theorem volume_slantedStrip {eta : ℝ} (heta : 0 ≤ eta) :
    volume (slantedStrip eta) = ENNReal.ofReal ((21 / 250 : ℝ) * eta) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_slantedStrip eta)]
  simp_rw [slantedStrip_section]
  rw [lintegral_indicator measurableSet_Ico]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
  rw [← ENNReal.ofReal_mul heta]
  congr 1
  ring

theorem measurableSet_productDomain (eta : ℝ) :
    MeasurableSet (currentChenUpsilon6LogDomain eta) :=
  measurableSet_currentChenUpsilon6LogRectangle.inter
    (isClosed_le ((continuous_apply 0).add (continuous_apply 1))
      continuous_const).measurableSet

theorem measurableSet_discarded (eta : ℝ) : MeasurableSet (discarded eta) :=
  (measurableSet_productDomain 0).diff (measurableSet_productDomain eta)

/-- The literal discarded domain is the strip 0 <= c-u-t < eta inside
the unchanged prime rectangle. Its two walls have exactly these inequalities. -/
theorem mem_discarded_iff (eta : ℝ) (x : Point) :
    x ∈ discarded eta ↔ x ∈ currentChenUpsilon6LogRectangle ∧
      0 ≤ (833 / 2500 : ℝ) - x 0 - x 1 ∧
        (833 / 2500 : ℝ) - x 0 - x 1 < eta := by
  constructor
  · rintro ⟨⟨hx, hx0⟩, hxeta⟩
    have hx0' : x 0 + x 1 ≤ (833 / 2500 : ℝ) := by
      simpa only [sub_zero] using hx0
    have hgt : (833 / 2500 : ℝ) - eta < x 0 + x 1 := by
      by_contra h
      exact hxeta ⟨hx, le_of_not_gt h⟩
    exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, h0, heta⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0
      linarith
    · intro h
      have hgate := h.2
      change x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta at hgate
      linarith

/-- Product Lebesgue measure of the actual lost domain is at most width
times eta. The volume-preserving map retains the original coordinate order. -/
theorem volume_discarded_le {eta : ℝ} (heta : 0 ≤ eta) :
    volume (discarded eta) ≤ ENNReal.ofReal ((21 / 250 : ℝ) * eta) := by
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  rw [← volume_slantedStrip heta, ← hE.measure_preimage_equiv (slantedStrip eta)]
  apply measure_mono
  intro x hx
  obtain ⟨hrect, h0, hη⟩ := (mem_discarded_iff eta x).mp hx
  obtain ⟨_, _, ht, hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hrect
  change (19 / 125 : ℝ) ≤ x 1 ∧ x 1 < 59 / 250 ∧
    (833 / 2500 : ℝ) - eta - x 1 < x 0 ∧ x 0 ≤ (833 / 2500 : ℝ) - x 1
  exact ⟨ht, hd, by linarith, by linarith⟩

theorem volumeReal_discarded_le {eta : ℝ} (heta : 0 ≤ eta) :
    (volume : Measure Point).real (discarded eta) ≤ (21 / 250 : ℝ) * eta := by
  have h := ENNReal.toReal_mono (by simp) (volume_discarded_le heta)
  simpa only [measureReal_def,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21 / 250) heta)] using h

/-- Exact subtraction identifies the analytic loss with the actual discarded
set, before a bounded-kernel estimate is applied. -/
theorem buffer_loss_eq_integral_discarded (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x in currentChenUpsilon6LogDomain 0, f x) -
      (∫ x in currentChenUpsilon6LogDomain eta, f x) =
        ∫ x in discarded eta, f x := by
  have hsub : currentChenUpsilon6LogDomain eta ⊆ currentChenUpsilon6LogDomain 0 := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hgate := hx.2
    change x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta at hgate
    change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0
    linarith
  exact (setIntegral_sdiff (measurableSet_productDomain eta)
    (hf.mono_set inter_subset_left) hsub).symm

/-- Quantitative a.e. bounded-kernel loss, with the requested original width.
The hypotheses contain no assumed tail limit or assumed strip mass bound. -/
theorem abs_buffer_loss_le (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) {eta M : ℝ}
    (heta : 0 ≤ eta) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x : Point ∂volume.restrict (currentChenUpsilon6LogDomain 0), ‖f x‖ ≤ M) :
    |(∫ x in currentChenUpsilon6LogDomain 0, f x) -
      (∫ x in currentChenUpsilon6LogDomain eta, f x)| ≤ (21 / 250 : ℝ) * M * eta := by
  rw [buffer_loss_eq_integral_discarded f hf heta, ← Real.norm_eq_abs]
  have hfin : volume (discarded eta) < ⊤ :=
    lt_of_le_of_lt (volume_discarded_le heta) ENNReal.ofReal_lt_top
  have hb : ∀ᵐ x : Point ∂volume.restrict (discarded eta), ‖f x‖ ≤ M :=
    ae_restrict_of_ae_restrict_of_subset sdiff_subset hbound
  calc
    ‖∫ x in discarded eta, f x‖ ≤ M * (volume : Measure Point).real (discarded eta) :=
      norm_setIntegral_le_of_norm_le_const_ae hfin hb
    _ ≤ M * ((21 / 250 : ℝ) * eta) :=
      mul_le_mul_of_nonneg_left (volumeReal_discarded_le heta) hM
    _ = _ := by ring

theorem reciprocal_norm_bound {x : Point} (hx : x ∈ currentChenUpsilon6LogRectangle) :
    ‖1 / (x 0 * x 1)‖ ≤ (625000 / 7923 : ℝ) := by
  obtain ⟨ha, _, hh, _⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  have h0 : 0 < x 0 := by linarith
  have h1 : 0 < x 1 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (mul_nonneg h0.le h1.le))]
  calc
    1 / (x 0 * x 1) ≤ 1 / ((417 / 5000 : ℝ) * (19 / 125 : ℝ)) :=
      one_div_le_one_div_of_le (by norm_num)
        (mul_le_mul ha hh (by norm_num) h0.le)
    _ = _ := by norm_num

/-- Explicit boundedness of the existing actual ordinary kernel on D0.
The crude bound 4000 is proved from log(s-1)<=s and the true positive box. -/
theorem ordinary_norm_bound {x : Point} (hx : x ∈ currentChenUpsilon6LogDomain 0) :
    ‖currentChenUpsilon6OrdinaryKernel x‖ ≤ (4000 : ℝ) := by
  let s := currentChenUpsilon6OrdinaryProfile x
  have hs : 2 ≤ s := (currentChenUpsilon6OrdinaryProfile_mem_firstInterval (by norm_num) hx).1
  have hsp : 0 < s := by linarith
  have hl : Real.log (s - 1) ≤ s :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < s - 1)).trans (by linarith)
  have hfactor : 4 * Real.log (s - 1) / (s * (417 / 5000 : ℝ)) ≤
      4 / (417 / 5000 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hsp (by norm_num))).mpr
    calc
      4 * Real.log (s - 1) ≤ 4 * s := mul_le_mul_of_nonneg_left hl (by norm_num)
      _ = (4 / (417 / 5000 : ℝ)) * (s * (417 / 5000 : ℝ)) := by ring
  have hrp : 0 ≤ 1 / (x 0 * x 1) := by
    obtain ⟨h0, h1⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hx.1
    positivity
  have hr : 1 / (x 0 * x 1) ≤ (625000 / 7923 : ℝ) := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using reciprocal_norm_bound hx.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (currentChenUpsilon6OrdinaryKernel_nonneg (by norm_num) hx)]
  change (4 * Real.log (s - 1) / (s * (417 / 5000 : ℝ))) *
    (1 / (x 0 * x 1)) ≤ 4000
  calc
    _ ≤ (4 / (417 / 5000 : ℝ)) * (625000 / 7923 : ℝ) :=
      mul_le_mul hfactor hr hrp (by norm_num)
    _ ≤ _ := by norm_num

theorem reciprocal_abs_buffer_loss_le {eta : ℝ} (heta : 0 ≤ eta) :
    |(∫ x in currentChenUpsilon6LogDomain 0, 1 / (x 0 * x 1)) -
      (∫ x in currentChenUpsilon6LogDomain eta, 1 / (x 0 * x 1))| ≤
        (21 / 250 : ℝ) * (625000 / 7923 : ℝ) * eta := by
  apply abs_buffer_loss_le (fun x : Point => 1 / (x 0 * x 1))
    integrableOn_currentChenUpsilon6LogRectangle heta (by norm_num)
  filter_upwards [ae_restrict_mem (measurableSet_productDomain 0)] with x hx
  exact reciprocal_norm_bound hx.1

theorem ordinary_abs_buffer_loss_le {eta : ℝ} (heta : 0 ≤ eta) :
    |(∫ x in currentChenUpsilon6LogDomain 0, currentChenUpsilon6OrdinaryKernel x) -
      (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x)| ≤
        336 * eta := by
  have h := abs_buffer_loss_le currentChenUpsilon6OrdinaryKernel
    integrableOn_currentChenUpsilon6OrdinaryKernel heta (by norm_num : (0 : ℝ) ≤ 4000)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_productDomain 0)] with x hx
      exact ordinary_norm_bound hx)
  norm_num at h ⊢
  exact h

/-- Direct rational choice of eta for later ordinary numerical certificates. -/
theorem ordinary_loss_le_tolerance {eta epsilon : ℝ} (heta : 0 ≤ eta)
    (hbudget : eta ≤ epsilon / 336) :
    |(∫ x in currentChenUpsilon6LogDomain 0, currentChenUpsilon6OrdinaryKernel x) -
      (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x)| ≤
        epsilon := by
  have h := ordinary_abs_buffer_loss_le heta
  have hb : 336 * eta ≤ epsilon := by linarith
  exact h.trans hb

end

end ImbalancedChen.P5U6RunboQuantitativeBufferSourceOnly
