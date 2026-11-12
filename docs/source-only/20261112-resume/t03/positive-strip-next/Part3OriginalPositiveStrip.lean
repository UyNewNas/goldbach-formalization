import ImbalancedChen.Part3OriginalPositiveStripDensity
import ImbalancedChen.Part3ActualPrescribedPositiveJ
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! The prescribed scalar Fourier multiplier at real and complementary heights.
The removable zero height is obtained on the same moving spectral test. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStrip20261112
open Set Filter MeasureTheory Complex FourierTransform
open scoped BigOperators Topology FourierTransform
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveCosineProfile20261112 (profile profile_apply)
open ActualPrescribedPositiveJ20261112 (regular_transform exceptional_transform positiveWeight exceptionalWeight weightSchwartz)
open OriginalPositiveStripBoundary20261112 (B B_entire strip_bound Q Q_odd bottom top)
open OriginalPositiveStripDensity20261112 (Q_deriv h_jets h_even)
open OriginalPositiveStripContour20261112 (angular wave angular_L1 angular_derivative)
open KHeightSchwartzP3SourceOnly (heightFrequencyEquiv_apply)
open private h_smooth from ImbalancedChen.Part3OriginalPositiveStripDensity

abbrev h := OriginalPositiveStripBoundary20261112.h
def hhat (ell : D4→ℤ) (Y : ℝ) (ξ : ℂ) := angular (h ell Y) ξ
def Phat (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (ξ : ℂ) := angular (profile ell hY) ξ

private theorem Q_diff (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    HasDerivAt (Q ell Y) ((Real.pi:ℂ)*h ell Y w) w := by
  convert Q_deriv ell hY w using 1
  rw [OriginalPositiveStripDensity20261112.h_formula]
  field_simp [Real.pi_ne_zero]

private theorem boundary_L1 (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {ξ : ℂ} (hs : |ξ.im|<1) :
    Integrable (fun x : ℝ => profile ell hY x*wave ξ x) ∧
      Integrable (fun x : ℝ => Q ell Y x*wave ξ x) := by
  obtain ⟨C,hC,e⟩ := strip_bound ell hY
  have hb := angular_L1 (f:=fun x : ℝ => B ell Y x)
    ((B_entire ell hY).continuous.comp Complex.continuous_ofReal) hC
    (fun x => by simpa using e x 0 le_rfl Real.pi_pos.le) hs
  have ht := angular_L1 (f:=fun x : ℝ => B ell Y ((x:ℂ)+Real.pi*I))
    ((B_entire ell hY).continuous.comp (by fun_prop)) hC
    (fun x => e x Real.pi Real.pi_pos.le le_rfl) hs
  constructor
  · apply ((hb.add ht).div_const 2).congr
    exact ae_of_all _ fun x => by rw [bottom ell hY,top ell hY]; ring
  · apply ((hb.sub ht).div_const (2*I)).congr
    exact ae_of_all _ fun x => by rw [bottom ell hY,top ell hY]; field_simp [I_ne_zero] <;> ring

theorem hhat_L1 (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {ξ : ℂ} (hs : |ξ.im|<1) :
    Integrable (fun x : ℝ => h ell Y x*wave ξ x) := by
  obtain ⟨K,hK,hb⟩ := h_jets ell hY 0
  exact angular_L1 (h_smooth ell hY).continuous hK (by simpa only [iteratedDeriv_zero] using hb) hs

private theorem quotient_factor {ξ : ℂ} (hs : |ξ.im|<1) :
    let u := (Real.pi:ℂ)*ξ/2
    let E := Complex.exp (-(Real.pi:ℂ)*ξ)
    1+E≠0 ∧ (1-E)/(1+E)=Complex.tanh u := by
  let u := (Real.pi:ℂ)*ξ/2
  have him : |u.im|<Real.pi/2 := by
    have p := mul_lt_mul_of_pos_left hs Real.pi_pos
    simp [u,Complex.mul_im,abs_mul,abs_of_pos Real.pi_pos]
    linarith
  have hn : Complex.cosh u≠0 := by
    have hr : 0<(Complex.cosh u).re := by
      rw [←u.re_add_im,Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I]
      simpa [←Complex.ofReal_cosh,←Complex.ofReal_cos,←Complex.ofReal_sinh,←Complex.ofReal_sin,
        Complex.mul_re,Complex.mul_im] using mul_pos (Real.cosh_pos u.re) (Real.cos_pos_of_mem_Ioo (abs_lt.mp him))
    exact fun z => (ne_of_gt hr) (by simp [z])
  let E := Complex.exp (-(Real.pi:ℂ)*ξ)
  have ep : Complex.exp u*Complex.exp (-u)=1 := by rw [←Complex.exp_add,add_neg_cancel,Complex.exp_zero]
  have em : E=Complex.exp (-u)*Complex.exp (-u) := by
    rw [←Complex.exp_add]; dsimp only [E,u]; congr 1; ring
  have hp : 1+E=2*Complex.cosh u*Complex.exp (-u) := by rw [em,Complex.cosh]; linear_combination -ep
  have hminus : 1-E=2*Complex.sinh u*Complex.exp (-u) := by rw [em,Complex.sinh]; linear_combination -ep
  change 1+E≠0 ∧ (1-E)/(1+E)=Complex.tanh u
  rw [hp,hminus,Complex.tanh_eq_sinh_div_cosh]
  exact ⟨by exact mul_ne_zero (mul_ne_zero (by norm_num) hn) (Complex.exp_ne_zero _),
    by field_simp [hn,Complex.exp_ne_zero]⟩

theorem complex_strip (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) {ξ : ℂ} (hs : |ξ.im|<1) :
    hhat ell Y ξ=(ξ/(Real.pi:ℂ))*Complex.tanh ((Real.pi:ℂ)*ξ/2)*Phat ell hY ξ := by
  obtain ⟨C,hC,hB⟩ := strip_bound ell hY
  have S := OriginalPositiveStripContour20261112.horizontal (B_entire ell hY) hC hB hs
  obtain ⟨p,q⟩ := boundary_L1 ell hY hs
  let P0 := Phat ell hY ξ
  let Q0 := angular (Q ell Y) ξ
  let E := Complex.exp (-(Real.pi:ℂ)*ξ)
  have e : P0-I*Q0=E*(P0+I*Q0) := by
    unfold angular at S
    simp_rw [top ell hY,bottom ell hY,sub_mul,add_mul,mul_assoc] at S
    simpa only [P0,Q0,Phat,angular,E,integral_sub p (q.const_mul I),integral_add p (q.const_mul I),
      integral_const_mul] using S
  obtain ⟨hn,hf⟩ := quotient_factor hs
  have d := angular_derivative (Q_diff ell hY) q (by
    simpa only [mul_assoc] using (hhat_L1 ell hY hs).const_mul (Real.pi:ℂ))
  have d' : (Real.pi:ℂ)*hhat ell Y ξ=I*ξ*Q0 := by
    simpa only [angular,hhat,Q0,mul_assoc,integral_const_mul] using d
  change hhat ell Y ξ=ξ/(Real.pi:ℂ)*Complex.tanh ((Real.pi:ℂ)*ξ/2)*P0
  rw [←hf]
  change hhat ell Y ξ=ξ/(Real.pi:ℂ)*((1-E)/(1+E))*P0
  field_simp [hn,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  linear_combination (1+E)*d'-ξ*e

theorem zero_mass (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : ∫ w : ℝ,h ell Y w=0 := by
  have H := complex_strip ell hY (ξ:=0) (by norm_num)
  simpa [hhat,angular,wave] using H

theorem regular_read (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    positiveWeight (spectralTest ell Y) t=4*Phat ell hY (2*(t:ℂ)) := by
  rw [(regular_transform ell hY t).2]
  change 4*((𝓕 (profile ell hY):SchwartzMap ℝ ℂ):ℝ→ℂ) (_) = _
  rw [SchwartzMap.fourier_coe,heightFrequencyEquiv_apply,Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    simp only [Phat,angular,wave,smul_eq_mul]
    rw [mul_comm]
    congr 2; push_cast; field_simp [Real.pi_ne_zero] <;> ring

theorem regular_multiplier (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    hhat ell Y (2*(t:ℂ))=((t:ℂ)/(2*Real.pi))*Complex.tanh ((Real.pi:ℂ)*t)*
      positiveWeight (spectralTest ell Y) t := by
  rw [regular_read ell hY,complex_strip ell hY (by simp : |(2*(t:ℂ)).im|<1),
    show (Real.pi:ℂ)*(2*(t:ℂ))/2=Real.pi*t by ring]
  ring

theorem threshold (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    positiveWeight (spectralTest ell Y) 0=4*Phat ell hY 0 ∧
      Tendsto (fun t : ℝ => 4*Phat ell hY (2*(t:ℂ))) (𝓝[≠] 0)
        (𝓝 (positiveWeight (spectralTest ell Y) 0)) := by
  refine ⟨by simpa using regular_read ell hY 0,?_⟩
  have e : (fun t : ℝ => 4*Phat ell hY (2*(t:ℂ)))=weightSchwartz ell hY := funext
    (fun t => (regular_read ell hY t).symm.trans (regular_transform ell hY t).2)
  rw [e,(regular_transform ell hY 0).2]
  exact (weightSchwartz ell hY).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

theorem exceptional_read (ell : D4→ℤ) {Y a : ℝ} (hY : 0<Y) (ha : 0≤a) (ha1 : a<1/2) :
    exceptionalWeight (spectralTest ell Y) a=4*Phat ell hY (2*(a:ℂ)*I) := by
  have hs : |(2*(a:ℂ)*I).im|<1 := by simp [Complex.mul_im,Complex.mul_re,abs_of_nonneg ha]; linarith
  have i := (boundary_L1 ell hY hs).1
  let p := (profile ell hY:ℝ→ℂ)
  let F := fun x : ℝ => p x*wave (2*(a:ℂ)*I) x
  have fc (x : ℝ) : F x=p x*(Real.exp (2*a*x):ℂ) := by
    dsimp [F,wave]
    rw [Complex.ofReal_exp]
    congr 2; push_cast; ring_nf; simp [I_sq]
  have ep (x : ℝ) : p (-x)=p x := by dsimp [p]; simp only [profile_apply,Real.cosh_neg]
  have refl := integral_comp_neg_Ioi (0:ℝ) F
  have E := (integral_Iic_add_Ioi (a:=(0:ℝ)) (f:=F) i.integrableOn i.integrableOn).symm
  rw [←(by simpa only [neg_zero] using refl : (∫ x in Ioi (0:ℝ),F (-x))=∫ x in Iic 0,F x),
    ←integral_add i.comp_neg.integrableOn i.integrableOn] at E
  rw [(exceptional_transform ell hY ha ha1).2]
  change _=4*(∫ x,F x)
  rw [E,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    rw [fc,fc,ep,Real.cosh_eq]; push_cast; rw [mul_neg]; ring

theorem complementary_multiplier (ell : D4→ℤ) {Y a : ℝ} (hY : 0<Y) (ha : 0≤a) (ha1 : a<1/2) :
    hhat ell Y (2*(a:ℂ)*I) = -((a:ℂ)/(2*Real.pi))*(Real.tan (Real.pi*a):ℂ)*
      exceptionalWeight (spectralTest ell Y) a := by
  have hs : |(2*(a:ℂ)*I).im|<1 := by simp [Complex.mul_im,Complex.mul_re,abs_of_nonneg ha]; linarith
  rw [exceptional_read ell hY ha ha1,complex_strip ell hY hs,
    show (Real.pi:ℂ)*(2*(a:ℂ)*I)/2=((Real.pi*a:ℝ):ℂ)*I by push_cast; ring,
    Complex.tanh_mul_I,←Complex.ofReal_tan]
  ring_nf <;> simp [I_sq] <;> ring

end ImbalancedChen.Part3.OriginalPositiveStrip20261112
end
