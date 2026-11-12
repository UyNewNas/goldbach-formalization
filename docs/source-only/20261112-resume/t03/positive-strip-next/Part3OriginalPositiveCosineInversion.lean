import ImbalancedChen.Part3OriginalPositiveStripBoundary
import ImbalancedChen.Part3KCosineInversion
import Mathlib.Analysis.Fourier.Inversion

/-! The unweighted cosine transform of the original positive test and pointwise inversion. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveCosineInversion20261112
open Complex Set MeasureTheory FourierTransform
open scoped Topology FourierTransform BigOperators ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 (spectralTest_tsupport_strict)
open KFullLineFourierBridgeSourceOnly (fourier_even_eq_cosine)
open private frequency from ImbalancedChen.Part3ActualPositiveCosineProfile

theorem phi_compact (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : HasCompactSupport (spectralTest ell Y) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (Y/16) (16*Y)))
  exact fun q h => ⟨(spectralTest_tsupport_strict ell hY (subset_tsupport _ h)).1.le,
    (spectralTest_tsupport_strict ell hY (subset_tsupport _ h)).2.le⟩

theorem phi_vanish (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {q : ℝ} (hq : q≤0) :
    spectralTest ell Y q=0 := by
  by_contra nz
  have L := (spectralTest_tsupport_strict ell hY (subset_tsupport _ nz)).1
  linarith

private def base (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  ((phi_compact ell hY).add ((phi_compact ell hY).comp_homeomorph (Homeomorph.neg ℝ))).toSchwartzMap
    ((spectralTest_contDiff ell Y).add ((spectralTest_contDiff ell Y).comp contDiff_neg))

def C (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : SchwartzMap ℝ ℂ :=
  (1/2:ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequency (𝓕 (base ell hY))

private theorem base_even (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (q : ℝ) :
    base ell hY (-q)=base ell hY q := by
  change spectralTest ell Y (-q)+spectralTest ell Y (- -q)=_
  simp only [neg_neg]; exact add_comm _ _

private theorem base_pos (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {q : ℝ} (hq : 0≤q) :
    base ell hY q=spectralTest ell Y q := by
  change spectralTest ell Y q+spectralTest ell Y (-q)=_
  rw [phi_vanish ell hY (neg_nonpos.mpr hq),add_zero]

private theorem C_frequency (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (s : ℝ) :
    C ell hY s=(1/2:ℂ)*(𝓕 ((base ell hY:SchwartzMap ℝ ℂ):ℝ→ℂ)) (s/(2*Real.pi)) := by
  change (1/2:ℂ)*((𝓕 (base ell hY):SchwartzMap ℝ ℂ):ℝ→ℂ) (frequency s)=_
  rw [SchwartzMap.fourier_coe]
  congr 2; change (2*Real.pi)⁻¹*s=_; ring

theorem C_apply (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (s : ℝ) :
    C ell hY s=∫ q in Ioi (0:ℝ),(Real.cos (q*s):ℂ)*spectralTest ell Y q := by
  rw [C_frequency,fourier_even_eq_cosine _ (base ell hY).integrable (base_even ell hY)]
  rw [←mul_assoc,show (1/2:ℂ)*2=1 by norm_num,one_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  rw [base_pos ell hY hq.le]
  congr 2
  field_simp [Real.pi_ne_zero] <;> ring

theorem C_even (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (s : ℝ) : C ell hY (-s)=C ell hY s := by
  simp only [C_apply,mul_neg,Real.cos_neg]

theorem cosine_inversion (ell : D4→ℤ) {Y q : ℝ} (hY : 0<Y) (hq : 0≤q) :
    (∫ s in Ioi (0:ℝ),(Real.cos (q*s):ℂ)*C ell hY s)=(Real.pi/2:ℝ)*spectralTest ell Y q := by
  let f := base ell hY
  let G : ℝ→ℂ := 𝓕 (f:ℝ→ℂ)
  have hg : Integrable G := by simpa only [G,←SchwartzMap.fourier_coe] using ((𝓕 f:SchwartzMap ℝ ℂ).integrable)
  have scaled (u : ℝ) : G u=2*C ell hY (2*Real.pi*u) := by
    rw [C_frequency,show 2*Real.pi*u/(2*Real.pi)=u by field_simp [Real.pi_ne_zero]]
    dsimp [G,f]; ring
  have evenG (u : ℝ) : G (-u)=G u := by rw [scaled,scaled,mul_neg,C_even]
  have hh := congrFun (f.continuous.fourierInv_fourier_eq f.integrable hg) (-q)
  rw [Real.fourierInv_eq_fourier_neg,neg_neg,base_even,base_pos ell hY hq] at hh
  have hF := fourier_even_eq_cosine G hg evenG q
  have eq : spectralTest ell Y q=2*∫ x in Ioi (0:ℝ),(Real.cos (2*Real.pi*x*q):ℂ)*G x := hh.symm.trans hF
  let ff := fun s : ℝ => (Real.cos (q*s):ℂ)*C ell hY s
  have sub := integral_comp_mul_left_Ioi' ff 0 (show 0<2*Real.pi by positivity)
  rw [mul_zero,Complex.real_smul] at sub
  change ∫ s in Ioi (0:ℝ),ff s=_
  rw [←sub]
  have r : (∫ x in Ioi (0:ℝ),(Real.cos (2*Real.pi*x*q):ℂ)*G x)=
      2*∫ x in Ioi (0:ℝ),ff (2*Real.pi*x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by rw [scaled]; dsimp [ff]; rw [mul_comm (2*Real.pi*x) q]; ring
  rw [r] at eq
  push_cast
  linear_combination -(Real.pi:ℂ)/2*eq

end ImbalancedChen.Part3.OriginalPositiveCosineInversion20261112
end
