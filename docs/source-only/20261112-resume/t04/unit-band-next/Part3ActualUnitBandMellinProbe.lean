import ImbalancedChen.Part3ActualComplexTwoKMellin
import ImbalancedChen.Part3ImaginaryOrderKFirstMoment
import ImbalancedChen.Part3ImaginaryGammaNormalization

/-! Mellin probes on the real spectral line. Both orders in the
physical kernel are measured in their original Whittaker convention. -/
namespace ImbalancedChen.Part3.ActualUnitBandMellinProbe20261112

noncomputable section
open Set MeasureTheory Complex
open ActualComplexTwoKMellin20261025a ComplexOrderKBridgeSourceOnly
open ImaginaryOrderKFirstMoment20261025a ImaginaryGammaNormalization20261025a

def probeDensity (T : ℝ) (ν : ℂ) (q : ℝ) : ℂ :=
  (q : ℂ)^(-((T : ℂ)*I))*complexOrderK 0 q*complexOrderK ν q

def probeIntegral (T : ℝ) (ν : ℂ) : ℂ := ∫ q in Ioi (0 : ℝ),probeDensity T ν q

theorem probe_integrable (T : ℝ) {ν : ℂ} (hν : |ν.re|<1) :
    IntegrableOn (probeDensity T ν) (Ioi (0 : ℝ)) := by
  let s := 1-(T:ℂ)*I
  have hs : |(0 : ℂ).re|+|ν.re|<s.re := by simpa [s,Complex.mul_re] using hν
  have E : s-1= -((T:ℂ)*I) := by dsimp [s]; ring
  simpa only [actualTwoKMellinDensity,E,probeDensity] using
    (actualTwoKMellinDensity_integrable (nu := 0) (mu := ν) (s := s) hs)

private theorem four_gamma (T t : ℝ) :
    probeIntegral T ((t : ℂ)*I) =
      (2 : ℂ)^((1-(T:ℂ)*I)-3)/Gamma (1-(T:ℂ)*I) *
      Gamma ((1/2:ℂ)+(( (t-T)/2 : ℝ):ℂ)*I)^2 *
      Gamma ((1/2:ℂ)+((-(T+t)/2 : ℝ):ℂ)*I)^2 := by
  let s := 1-(T:ℂ)*I
  let ν := (t:ℂ)*I
  have hs : |(0:ℂ).re|+|ν.re|<s.re := by simp [s,ν,Complex.mul_re]
  have H := actual_complex_twoK_mellin (nu := 0) (mu := ν) (s := s) hs
  have e : s-1= -((T:ℂ)*I) := by dsimp [s]; ring
  have A : (s+ν)/2=(1/2:ℂ)+(((t-T)/2:ℝ):ℂ)*I := by dsimp [s,ν]; push_cast; ring
  have B : (s-ν)/2=(1/2:ℂ)+((-(T+t)/2:ℝ):ℂ)*I := by dsimp [s,ν]; push_cast; ring
  simp only [e,add_zero,sub_zero,A,B] at H
  exact H.trans (by ring)

/-- The denominator formula is used only at positive T. All real t,
including t=0 and negative heights, retain their actual kernel. -/
theorem gamma_norm (T t : ℝ) (hT : 0<T) :
    ‖probeIntegral T ((t:ℂ)*I)‖^2 =
      (Real.pi^3/4)*Real.sinh (Real.pi*T)/
        (T*(Real.cosh (Real.pi*T)+Real.cosh (Real.pi*t))^2) := by
  let A := Real.pi*((t-T)/2)
  let B := Real.pi*(-(T+t)/2)
  have add : A+B= -(Real.pi*T) := by dsimp [A,B]; ring
  have sub : A-B=Real.pi*t := by dsimp [A,B]; ring
  have twice : 2*Real.cosh A*Real.cosh B=Real.cosh (Real.pi*T)+Real.cosh (Real.pi*t) := by
    rw [← Real.cosh_neg (Real.pi*T),← add,← sub,Real.cosh_add,Real.cosh_sub]
    ring
  have scale : ‖(2:ℂ)^((1-(T:ℂ)*I)-3)‖=1/4 := by
    rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    norm_num [Complex.sub_re,Complex.mul_re]
  have g := norm_gamma_one_add_mul_I_sq (-T) (neg_ne_zero.mpr hT.ne')
  rw [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg,show Real.pi*(-T)= -(Real.pi*T) by ring,
    Real.sinh_neg] at g
  rw [four_gamma,norm_mul,norm_mul,norm_div,norm_pow,norm_pow,scale]
  rw [norm_gamma_half_add_mul_I_sq,norm_gamma_half_add_mul_I_sq]
  change ((1/4)/‖Gamma (1-(T:ℂ)*I)‖*(Real.pi/Real.cosh A)*(Real.pi/Real.cosh B))^2=_
  rw [mul_pow,mul_pow,div_pow,g,← twice]
  field_simp [(Real.cosh_pos A).ne',(Real.cosh_pos B).ne',Real.pi_ne_zero,hT.ne',
    (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hT)).ne'] <;> ring

private theorem cosh_compare {x y d : ℝ} (h : |x-y|≤d) :
    Real.cosh x≤Real.exp d*Real.cosh y := by
  have a := Real.exp_le_exp.mpr (show x≤d+y by linarith [(abs_le.mp h).2])
  have b := Real.exp_le_exp.mpr (show -x≤d+(-y) by linarith [(abs_le.mp h).1])
  rw [Real.exp_add] at a b
  rw [Real.cosh_eq,Real.cosh_eq]
  nlinarith only [a,b]

/-- The lower estimate controls the reciprocal cosh weight on the
entire positive and negative unit band. It is independent of the
level, cusp, frequency and central height. -/
theorem reciprocal_cosh_le :
    ∃ C : ℝ,0<C ∧ ∀ {T t : ℝ},1≤T → | |t| - T |≤1 →
      (Real.cosh (Real.pi*t))⁻¹ ≤ C*T*‖probeIntegral T ((t:ℂ)*I)‖^2 := by
  let A := 1+Real.exp Real.pi
  let C := 4*A^2*Real.cosh Real.pi/(Real.pi^3*Real.sinh Real.pi)
  have hπ := Real.pi_pos
  have hs := Real.sinh_pos_iff.mpr hπ
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T t hT ht
  have Tpos : 0<T := zero_lt_one.trans_le hT
  let X := Real.cosh (Real.pi*T)
  let Y := Real.cosh (Real.pi*t)
  have Xpos : 0<X := Real.cosh_pos _
  have Ypos : 0<Y := Real.cosh_pos _
  have dist : |Real.pi*|t|-Real.pi*T|≤Real.pi := by
    rw [← mul_sub,abs_mul,abs_of_pos hπ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hπ.le
  have ey : Real.cosh (Real.pi*|t|)=Y := by
    rw [show Real.pi*|t|=|Real.pi*t| by rw [abs_mul,abs_of_pos hπ],Real.cosh_abs]
  have a := cosh_compare dist
  have b := cosh_compare (show |Real.pi*T-Real.pi*|t| |≤Real.pi by rwa [abs_sub_comm])
  rw [ey] at a b
  have upper : (X+Y)^2≤A^2*X*Y := by
    have h₁ : X+Y≤A*X := by dsimp only [A]; linarith only [a]
    have h₂ : X+Y≤A*Y := by dsimp only [A]; linarith only [b]
    nlinarith only [mul_le_mul h₁ h₂ (add_pos Xpos Ypos).le (mul_pos hA Xpos).le]
  have hyper := Real.sinh_nonneg_iff.mpr (show 0≤Real.pi*T-Real.pi by nlinarith [hT,hπ])
  rw [Real.sinh_sub] at hyper
  have ratio : X*Real.sinh Real.pi≤Real.cosh Real.pi*Real.sinh (Real.pi*T) := by
    simpa only [X,mul_comm] using sub_nonneg.mp hyper
  have hprod : (X+Y)^2*Real.sinh Real.pi≤A^2*Y*Real.cosh Real.pi*Real.sinh (Real.pi*T) := by
    have cut := mul_le_mul_of_nonneg_right upper hs.le
    have scale := mul_le_mul_of_nonneg_left ratio (mul_nonneg (sq_nonneg A) Ypos.le)
    nlinarith only [cut,scale]
  rw [gamma_norm T t Tpos]
  change Y⁻¹≤C*T*((Real.pi^3/4)*Real.sinh (Real.pi*T)/(T*(X+Y)^2))
  calc
    _ ≤ A^2*Real.cosh Real.pi*Real.sinh (Real.pi*T)/(Real.sinh Real.pi*(X+Y)^2) := by
      rw [inv_eq_one_div,div_le_div_iff₀ Ypos (mul_pos hs (sq_pos_of_pos (add_pos Xpos Ypos)))]
      linarith only [hprod]
    _ = _ := by
      dsimp only [C]
      field_simp [hπ.ne',hs.ne',Tpos.ne',(add_pos Xpos Ypos).ne'] <;> ring

/-- A uniform positive probe at every physically possible real order.
The bound does not depend on the number of exceptional eigenvectors. -/
theorem exceptional_probe_floor :
    ∃ c : ℝ,0<c ∧ ∀ α∈Icc (0:ℝ) (1/2),c≤‖probeIntegral 0 (α:ℂ)‖^2 := by
  let f := fun α : ℝ => ((Real.Gamma ((1+α)/2)*Real.Gamma ((1-α)/2))^2/4)^2
  have pA {α : ℝ} (h : α∈Icc (0:ℝ) (1/2)) : 0<(1+α)/2 := by linarith [h.1]
  have pB {α : ℝ} (h : α∈Icc (0:ℝ) (1/2)) : 0<(1-α)/2 := by linarith [h.2]
  have hf : ContinuousOn f (Icc 0 (1/2)) := by
    intro α h
    have G {x : ℝ} (hx : 0<x) : ContinuousAt Real.Gamma x :=
      (Real.differentiableAt_Gamma x (fun n => by have := (Nat.cast_nonneg (R := ℝ) n); linarith)).continuousAt
    exact (((((G (pA h)).comp α (by fun_prop)).mul ((G (pB h)).comp α (by fun_prop))).pow 2).div_const 4 |>.pow 2).continuousWithinAt
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) hf
  have positive : 0<f u := by
    have a := Real.Gamma_pos_of_pos (pA hu)
    have b := Real.Gamma_pos_of_pos (pB hu)
    dsimp only [f]
    positivity
  refine ⟨f u,positive,?_⟩
  intro α hα
  have H := actual_complex_twoK_mellin (nu := 0) (mu := (α:ℂ)) (s := 1)
    (by simp only [Complex.zero_re,abs_zero,zero_add,Complex.ofReal_re,Complex.one_re,abs_of_nonneg hα.1]; linarith [hα.2])
  have A : ((1:ℂ)+(α:ℂ))/2=(((1+α)/2 : ℝ):ℂ) := by push_cast; ring
  have B : ((1:ℂ)-(α:ℂ))/2=(((1-α)/2 : ℝ):ℂ) := by push_cast; ring
  have scale : (2:ℂ)^((1:ℂ)-3)=(1/4:ℂ) := by
    rw [show (1:ℂ)-3=((-2:ℤ):ℂ) by norm_num,Complex.cpow_intCast]
    norm_num
  have val : probeIntegral 0 (α:ℂ)=((Real.Gamma ((1+α)/2)*Real.Gamma ((1-α)/2))^2/4 : ℝ) := by
    simp only [probeIntegral,probeDensity,Complex.ofReal_zero,zero_mul,neg_zero,Complex.cpow_zero,one_mul]
    simp only [sub_self,Complex.cpow_zero,one_mul,add_zero,sub_zero,A,B,Complex.Gamma_one,div_one,
      Complex.Gamma_ofReal,scale] at H
    refine H.trans ?_
    push_cast
    ring
  have pa := Real.Gamma_pos_of_pos (pA hα)
  have pb := Real.Gamma_pos_of_pos (pB hα)
  rw [val,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact isMinOn_iff.mp hmin α hα

end
end ImbalancedChen.Part3.ActualUnitBandMellinProbe20261112
