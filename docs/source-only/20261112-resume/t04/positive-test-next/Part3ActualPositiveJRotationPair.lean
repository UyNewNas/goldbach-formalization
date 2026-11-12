import ImbalancedChen.Part3ActualCutPlaneKOrderZeroRemovable
import ImbalancedChen.Part3ActualIImaginaryArgumentJRotation
import ImbalancedChen.Part3ActualExceptionalJSmallKernel

/-! Add the two principal-slit boundary values before integrating a
same-sign test. Orders are either purely imaginary or real in [0,1).
The imaginary parameter t and the real parameter a have Bessel orders
2it and 2a respectively. -/
namespace ImbalancedChen.Part3.ActualPositiveJRotationPair20261112

noncomputable section
open Set Filter Complex
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualCutPlaneKIModel20261026b ActualCutPlaneKOrderZeroRemovable20261026b
open ActualIImaginaryArgumentJRotation20261026b ActualJCriticalOrderZero20261026a
open ActualJLocalOrderHolomorphic20261026a ActualExceptionalJSmallKernel20261102

def rotated (ν : ℂ) (q : ℝ) : ℂ :=
  cutPlaneKWithZero ν (I*(q:ℂ))+cutPlaneKWithZero ν ((-I)*(q:ℂ))

def regularKernel (q t : ℝ) : ℂ := (2*(Real.pi:ℂ))*criticalJRealKernel q (t:ℂ)

def complementaryKernel (q a : ℝ) : ℂ :=
  if a=0 then regularKernel q 0 else
    (2*(Real.pi:ℂ)/(Real.sin (Real.pi*a):ℂ))*(generalJ (-2*(a:ℂ)) q-generalJ (2*(a:ℂ)) q)

private theorem pair_nonintegral {ν : ℂ} (hs : Complex.sin ((Real.pi:ℂ)*ν)≠0) {q : ℝ} (hq : 0<q) :
    4*rotated ν q=(2*(Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*ν/2))*
      (generalJ (-ν) q-generalJ ν q) := by
  have hn : ν≠0 := by rintro rfl; simp at hs
  let x := (Real.pi:ℂ)*ν/2
  have dx : (Real.pi:ℂ)*ν=2*x := by dsimp only [x]; ring
  have s : Complex.sin ((Real.pi:ℂ)*ν)=2*Complex.sin x*Complex.cos x := by rw [dx,Complex.sin_two_mul]
  have ss : Complex.sin x≠0 := fun h => hs (by rw [s,h]; ring)
  have cc : Complex.cos x≠0 := fun h => hs (by rw [s,h]; ring)
  have ep : Complex.exp (I*(Real.pi:ℂ)*ν/2)+Complex.exp ((-I)*(Real.pi:ℂ)*ν/2)=2*Complex.cos x := by
    rw [Complex.two_cos]
    congr 1 <;> congr 1 <;> dsimp [x] <;> ring
  rw [rotated,cutPlaneKWithZero_of_ne_zero hn,cutPlaneKNonintegral,cutPlaneKWithZero_of_ne_zero hn,
    cutPlaneKNonintegral,complexArgumentI_rotate_upper _ hq,complexArgumentI_rotate_upper _ hq,
    complexArgumentI_rotate_lower _ hq,complexArgumentI_rotate_lower _ hq]
  have e1 : I*(Real.pi:ℂ)*(-ν)/2=(-I)*(Real.pi:ℂ)*ν/2 := by ring
  have e2 : (-I)*(Real.pi:ℂ)*(-ν)/2=I*(Real.pi:ℂ)*ν/2 := by ring
  rw [e1,e2]
  calc
    _ = (4*((Real.pi:ℂ)/(2*Complex.sin ((Real.pi:ℂ)*ν))))*
        (Complex.exp (I*(Real.pi:ℂ)*ν/2)+Complex.exp ((-I)*(Real.pi:ℂ)*ν/2))*
        (generalJ (-ν) q-generalJ ν q) := by ring
    _ = _ := by rw [ep,s]; change _=(2*(Real.pi:ℂ)/Complex.sin x)*_; field_simp [ss,cc] <;> ring

private theorem regular_nz {t q : ℝ} (ht : t≠0) (hq : 0<q) :
    4*rotated (2*I*(t:ℂ)) q=regularKernel q t := by
  have hn : (2*I*(t:ℂ)).im≠0 := by simpa [Complex.mul_im,Complex.mul_re] using mul_ne_zero (by norm_num : (2:ℝ)≠0) ht
  have H := pair_nonintegral (sin_pi_order_ne_zero_of_imaginary hn) hq
  have h : (Real.pi:ℂ)*(2*I*(t:ℂ))/2=(((Real.pi*t:ℝ):ℂ)*I) := by push_cast; ring
  rw [h,Complex.sin_mul_I,← Complex.ofReal_sinh] at H
  rw [H,regularKernel,criticalJRealKernel,criticalJQuotient_eq (Complex.ofReal_ne_zero.mpr ht),
    ← Complex.ofReal_mul,← Complex.ofReal_sinh]
  simp only [div_eq_mul_inv,mul_inv_rev,Complex.inv_I]
  ring

theorem regular_rotation {q : ℝ} (hq : 0<q) (t : ℝ) :
    4*rotated (2*I*(t:ℂ)) q=regularKernel q t := by
  by_cases z : t=0
  · subst t
    have a : ContinuousAt (fun s : ℝ => 2*I*(s:ℂ)) 0 := by fun_prop
    have ca (w : ℂ) (hw : w≠0) : ContinuousAt (fun s : ℝ => cutPlaneKWithZero (2*I*(s:ℂ)) w) 0 := by
      have H : ContinuousAt (fun ν => cutPlaneKWithZero ν w) (2*I*((0:ℝ):ℂ)) := by
        simpa only [Complex.ofReal_zero,mul_zero] using cutPlaneKWithZero_continuousAt_order_zero hw
      exact H.comp a
    have left : ContinuousAt (fun s : ℝ => 4*rotated (2*I*(s:ℂ)) q) 0 := continuousAt_const.mul
      ((ca _ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'))).add
        (ca _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr hq.ne'))))
    have right : ContinuousAt (regularKernel q) 0 := continuousAt_const.mul
      (by simpa using (criticalJRealKernel_analyticAt_zero hq).continuousAt.comp Complex.continuous_ofReal.continuousAt)
    apply tendsto_nhds_unique (left.tendsto.mono_left (show 𝓝[≠] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds))
    exact ((right.tendsto.mono_left nhdsWithin_le_nhds).congr' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (regular_nz (by simpa using hs) hq).symm))
  · exact regular_nz z hq

theorem regular_threshold {q : ℝ} (hq : 0<q) :
    regularKernel q 0=(-8)*actualJOrderDerivative 0 q := by
  rw [regularKernel,Complex.ofReal_zero,criticalJRealKernel_zero hq]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

theorem complementary_rotation {q a : ℝ} (hq : 0<q) (ha : 0≤a) (hb : a<1/2) :
    4*rotated (2*(a:ℂ)) q=complementaryKernel q a := by
  by_cases z : a=0
  · subst a
    simpa [complementaryKernel] using regular_rotation hq 0
  · have hL : 0<(2*(a:ℂ)).re := by simp; linarith [lt_of_le_of_ne ha z.symm]
    have hU : (2*(a:ℂ)).re<1 := by simp; linarith
    have E := pair_nonintegral (sin_pi_order_ne_zero_of_positive_strip hL hU) hq
    rw [show (Real.pi:ℂ)*(2*(a:ℂ))/2=((Real.pi*a:ℝ):ℂ) by push_cast; ring,← Complex.ofReal_sin] at E
    simpa only [complementaryKernel,if_neg z,neg_mul] using E

/-- The earlier physical exceptional budget uses Pascadi's pi/(2 sin)
normalization at order 2a. -/
theorem complementary_old {q a : ℝ} (hq : 0<q) (ha : 0≤a) (hc : 2*a≤exceptionalCap) :
    complementaryKernel q a=(-4)*positiveSignKernel (2*a) q := by
  by_cases z : a=0
  · subst a
    simp only [complementaryKernel,if_true,mul_zero,positiveSignKernel_zero,regular_threshold hq]
    ring
  · rw [complementaryKernel,if_neg z,positiveSignKernel_eq (mul_ne_zero (by norm_num) z)]
    rw [show Real.pi*(2*a)/2=Real.pi*a by ring]
    push_cast
    ring

end
end ImbalancedChen.Part3.ActualPositiveJRotationPair20261112

