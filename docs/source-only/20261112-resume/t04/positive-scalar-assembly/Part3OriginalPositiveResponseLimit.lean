import ImbalancedChen.Part3OriginalPositiveRatioWindows
import ImbalancedChen.Part3OriginalPositiveStripThreshold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Batteries.Tactic.OpenPrivate

/-! The two cutoff limits have the same physical order as the Maaß
coefficient. The archimedean numerator uses order twice that order. -/
namespace ImbalancedChen.Part3.OriginalPositiveResponseLimit20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open OriginalPositiveRatioWindows20261112
open RadialSchrodingerL2Form20261025a P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open OriginalPositiveStrip20261112 (h hhat native_regular native_complementary threshold_second_moment)
open OriginalPositiveStripContour20261112 (wave angular)
open ActualPositiveCenteredKLimit20261112 ActualPositiveScalarPacket20261112
open ActualPrescribedPositiveJ20261112 (positiveWeight exceptionalWeight)
open private cut_le cut_eventually cut_smooth cut_compact from ImbalancedChen.Part3OriginalPositiveRatioWindows
open private moment_L1 from ImbalancedChen.Part3OriginalPositiveStripThreshold

theorem cutoff_integral (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (f : ℝ→ℂ)
    (hf : Continuous f) (hi : Integrable (fun w => h ell Y w*f w)) :
    Tendsto (fun n => ∫ w : ℝ,(ratio ell hY n).function w*f w) atTop
      (𝓝 (∫ w : ℝ,h ell Y w*f w)) := by
  have A : Tendsto (fun n => ∫ w : ℝ, cut n w*(h ell Y w*f w)) atTop (𝓝 (∫ w : ℝ,h ell Y w*f w)) := by
    apply tendsto_integral_of_dominated_convergence (fun w => ‖h ell Y w*f w‖)
    · exact fun n => ((cut_smooth n).continuous.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    · exact hi.norm
    · intro n; exact ae_of_all _ fun w => by rw [norm_mul]; simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (cut_le n w) (norm_nonneg _)
    · exact ae_of_all _ fun w => tendsto_const_nhds.congr' ((cut_eventually w).mono fun n he => by rw [he,one_mul])
  have B := (mass_limit ell hY).mul_const (∫ w : ℝ,unit.function w*f w)
  have C (n : ℕ) : Integrable (fun w => cut n w*(h ell Y w*f w)) :=
    ((cut_smooth n).continuous.mul ((OriginalPositiveStrip20261112.smooth ell hY).continuous.mul hf)).integrable_of_hasCompactSupport
      (cut_compact n).mul_right
  have D := (unit.smooth.continuous.mul hf).integrable_of_hasCompactSupport unit.compact.mul_right
  apply (show Tendsto (fun n => (∫ w : ℝ,cut n w*(h ell Y w*f w))-
      mass ell Y n*(∫ w : ℝ,unit.function w*f w)) atTop (𝓝 (∫ w : ℝ,h ell Y w*f w)) by
        simpa only [zero_mul,sub_zero] using A.sub B).congr'
  filter_upwards with n
  change _=∫ w : ℝ,(cut n w*h ell Y w-mass ell Y n*unit.function w)*f w
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (C n) (D.const_mul _),integral_const_mul]

private theorem double_gamma {ν : ℂ} (hz : ν≠0) :
    2*Gamma ν*Gamma (-ν)= -(2*Real.pi:ℂ)/(ν*Complex.sin ((Real.pi:ℂ)*ν)) := by
  have A := Complex.Gamma_mul_Gamma_one_sub ν
  rw [show 1-ν=-ν+1 by ring,Gamma_add_one (-ν) (neg_ne_zero.mpr hz)] at A
  rw [mul_comm ν (Complex.sin _),← div_div,eq_div_iff hz]
  linear_combination -2*A

private theorem regular_gamma {t : ℝ} (ht : t≠0) :
    2*Gamma ((t:ℂ)*I)*Gamma (-((t:ℂ)*I))=(2*Real.pi:ℂ)/((t:ℂ)*(Real.sinh (Real.pi*t):ℂ)) := by
  rw [double_gamma (mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero),
    show (Real.pi:ℂ)*((t:ℂ)*I)=((Real.pi*t:ℝ):ℂ)*I by push_cast; ring,
    Complex.sin_mul_I,← Complex.ofReal_sinh]
  rw [show (t:ℂ)*I*((Real.sinh (Real.pi*t):ℂ)*I) = -((t:ℂ)*(Real.sinh (Real.pi*t):ℂ)) by
    calc _ = (t:ℂ)*(Real.sinh (Real.pi*t):ℂ)*I^2 := by ring
         _ = _ := by rw [I_sq]; ring,neg_div_neg_eq]

private theorem complementary_gamma {a : ℝ} (ha : 0<a) :
    2*Gamma (a:ℂ)*Gamma (-(a:ℂ))= -(2*Real.pi:ℂ)/((a:ℂ)*(Real.sin (Real.pi*a):ℂ)) := by
  rw [double_gamma (ofReal_ne_zero.mpr ha.ne'),← ofReal_mul,← ofReal_sin]

private theorem even_angular (T : RadialTest) (e : ∀ w,T.function (-w)=T.function w)
    (ξ : ℂ) : (∫ w : ℝ,T.function w*Complex.cosh (-I*ξ*(w:ℂ)))=angular T.function ξ := by
  let f := fun w : ℝ => T.function w*wave ξ w
  have X : Integrable f := (T.smooth.continuous.mul (by unfold wave; fun_prop)).integrable_of_hasCompactSupport T.compact.mul_right
  have E (w : ℝ) : T.function w*Complex.cosh (-I*ξ*(w:ℂ))=(f w+f (-w))/2 := by
    dsimp only [f,wave]; rw [e,Complex.cosh]; push_cast
    ring_nf
  have refl := MeasureTheory.integral_neg_eq_self (f:=f) (μ:=volume)
  simp_rw [E]
  rw [integral_div,integral_add X X.comp_neg,refl]
  unfold angular; dsimp only [f]; ring

theorem ratio_regular (ell : D4→ℤ) {Y t : ℝ} (hY : 0<Y) (ht : t≠0) (n : ℕ) :
    response (ratio ell hY n) ((t:ℂ)*I)=((2*Real.pi:ℂ)/((t:ℂ)*(Real.sinh (Real.pi*t):ℂ)))*
      angular (ratio ell hY n).function (2*(t:ℂ)) := by
  rw [response_nonzero _ (ratio_zero ell hY n) (mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero),
    regular_gamma ht,← even_angular _ (ratio_even ell hY n)]
  congr 1; apply integral_congr_ae
  exact ae_of_all _ fun w => by rw [show 2*((t:ℂ)*I)*(w:ℂ) = -(-I*(2*(t:ℂ))*(w:ℂ)) by ring,Complex.cosh_neg]

theorem ratio_exceptional (ell : D4→ℤ) {Y a : ℝ} (hY : 0<Y) (ha : 0<a) (n : ℕ) :
    response (ratio ell hY n) (a:ℂ)=(-(2*Real.pi:ℂ)/((a:ℂ)*(Real.sin (Real.pi*a):ℂ)))*
      angular (ratio ell hY n).function (2*(a:ℂ)*I) := by
  rw [response_nonzero _ (ratio_zero ell hY n) (ofReal_ne_zero.mpr ha.ne'),
    complementary_gamma ha,← even_angular _ (ratio_even ell hY n)]
  congr 1; apply integral_congr_ae
  exact ae_of_all _ fun w => by rw [show -I*(2*(a:ℂ)*I)*(w:ℂ)=2*(a:ℂ)*(w:ℂ) by ring_nf; simp [I_sq]]

theorem regular_limit (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    Tendsto (fun n => response (ratio ell hY n) ((t:ℂ)*I)) atTop
      (𝓝 (positiveWeight (spectralTest ell Y) t/(Real.cosh (Real.pi*t):ℂ))) := by
  by_cases ht : t=0
  · subst t
    have P : Integrable (fun w : ℝ => h ell Y w*(w:ℂ)^2) := by
      apply ((moment_L1 ell hY 2).div_const 4).mono'
        (((OriginalPositiveStrip20261112.smooth ell hY).continuous.mul (Complex.continuous_ofReal.pow 2)).aestronglyMeasurable)
      exact ae_of_all _ fun w => by simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]; nlinarith
    have L := (cutoff_integral ell hY (fun w : ℝ => (w:ℂ)^2) (by fun_prop) P).const_mul (-4:ℂ)
    simp only [ofReal_zero,zero_mul,mul_zero,Real.cosh_zero,ofReal_one,div_one,response_zero,threshold_second_moment ell hY]
    simpa only [mul_comm ((_:ℂ)^2)] using L
  · have L := (cutoff_integral ell hY (fun w : ℝ => wave (2*(t:ℂ)) w) (by unfold wave; fun_prop)
      (OriginalPositiveStrip20261112.hhat_L1 ell hY (by simp))).const_mul ((2*Real.pi:ℂ)/((t:ℂ)*(Real.sinh (Real.pi*t):ℂ)))
    simp only [ratio_regular ell hY ht]
    rw [native_regular ell hY ht]
    simpa only [angular,hhat,div_mul_eq_mul_div] using L

/-- The exponential margin is paid at this individual complementary index. -/
theorem exceptional_limit (ell : D4→ℤ) {Y a : ℝ} (hY : 0<Y) (ha : 0<a) (ha1 : a<1/2) :
    Tendsto (fun n => response (ratio ell hY n) (a:ℂ)) atTop
      (𝓝 (exceptionalWeight (spectralTest ell Y) a/(Real.cos (Real.pi*a):ℂ))) := by
  have hs : |(2*(a:ℂ)*I).im|<1 := by simp [Complex.mul_im,abs_of_nonneg ha.le]; linarith
  have L := (cutoff_integral ell hY (fun w : ℝ => wave (2*(a:ℂ)*I) w) (by unfold wave; fun_prop)
    (OriginalPositiveStrip20261112.hhat_L1 ell hY hs)).const_mul (-(2*Real.pi:ℂ)/((a:ℂ)*(Real.sin (Real.pi*a):ℂ)))
  simp only [ratio_exceptional ell hY ha]
  rw [native_complementary ell hY ha ha1]
  simpa only [angular,hhat,div_mul_eq_mul_div] using L

end
end ImbalancedChen.Part3.OriginalPositiveResponseLimit20261112
