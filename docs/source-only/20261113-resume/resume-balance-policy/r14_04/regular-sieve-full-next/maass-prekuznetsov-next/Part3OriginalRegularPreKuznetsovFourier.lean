import ImbalancedChen.Part3OriginalRegularPreKuznetsovGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Fourier transform of the precise r² Gaussian in the dyadic positive
majorant. Its second-order polynomial has the cancellation needed at
long moduli. Both integrations by parts are on the full real axis. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovFourier20261113
open Complex MeasureTheory
open OriginalRegularPreKuznetsovGaussian20261113 (weight)

def character (v r : ℝ) : ℂ := exp (I*(2*(v:ℂ))*(r:ℂ))

private def kernel (β v r : ℝ) : ℂ := character v r*exp (-(β:ℂ)*(r:ℂ)^2)

private theorem kernel_norm (β v r : ℝ) : ‖kernel β v r‖=Real.exp (-β*r^2) := by
  rw [kernel,character,norm_mul,norm_exp,norm_exp,←Real.exp_add]
  congr 1
  simp [Complex.mul_re,Complex.mul_im,pow_two] <;> ring

private theorem kernel_int {β : ℝ} (hβ : 0<β) (v : ℝ) : Integrable (kernel β v) := by
  apply (integrable_exp_neg_mul_sq hβ).mono' (show Continuous (kernel β v) by unfold kernel character; fun_prop).aestronglyMeasurable
  exact ae_of_all _ (fun r => (kernel_norm β v r).le)

private theorem first_int {β : ℝ} (hβ : 0<β) (v : ℝ) :
    Integrable (fun r : ℝ => (r:ℂ)*kernel β v r) := by
  apply (integrable_mul_exp_neg_mul_sq hβ).norm.mono'
    (show Continuous (fun r : ℝ => (r:ℂ)*kernel β v r) by unfold kernel character; fun_prop).aestronglyMeasurable
  exact ae_of_all _ (fun r => by
    simp only [norm_mul,kernel_norm,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,le_refl])

private theorem second_int {β : ℝ} (hβ : 0<β) (v : ℝ) :
    Integrable (fun r : ℝ => (r:ℂ)^2*kernel β v r) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hβ (by norm_num : (-1:ℝ)<(2:ℝ))
  apply h.mono' (show Continuous (fun r : ℝ => (r:ℂ)^2*kernel β v r) by unfold kernel character; fun_prop).aestronglyMeasurable
  exact ae_of_all _ (fun r => by
    simp only [norm_mul,kernel_norm,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.rpow_two,le_refl])

private theorem kernel_diff (β v r : ℝ) : HasDerivAt (kernel β v)
    ((2*(v:ℂ)*I)*kernel β v r-(2*(β:ℂ))*((r:ℂ)*kernel β v r)) r := by
  have A : HasDerivAt (fun x : ℝ => I*(2*(v:ℂ))*(x:ℂ)) (I*(2*(v:ℂ))) r := by
    simpa only [id_eq,Complex.ofReal_one,mul_one] using ((hasDerivAt_id r).ofReal_comp.const_mul (I*(2*(v:ℂ))))
  have B : HasDerivAt (fun x : ℝ => -(β:ℂ)*(x:ℂ)^2) (-(β:ℂ)*(2*(r:ℂ))) r := by
    convert (((hasDerivAt_id r).ofReal_comp.pow 2).const_mul (-(β:ℂ))) using 1 <;> push_cast <;> ring
  convert A.cexp.mul B.cexp using 1 <;> unfold kernel character <;> ring

private theorem moment {β : ℝ} (hβ : 0<β) (v : ℝ) :
    (∫ r : ℝ,(r:ℂ)^2*kernel β v r)=
      (1/(2*(β:ℂ))-(v:ℂ)^2/(β:ℂ)^2)*(∫ r : ℝ,kernel β v r) := by
  let A := 2*(v:ℂ)*I
  let B := 2*(β:ℂ)
  let f := kernel β v
  let g := fun r : ℝ => (r:ℂ)*f r
  let j := fun r : ℝ => (r:ℂ)^2*f r
  have fi := kernel_int hβ v
  have gi := first_int hβ v
  have ji := second_int hβ v
  have d1 (r : ℝ) : HasDerivAt f (A*f r-B*g r) r := kernel_diff β v r
  have d2 (r : ℝ) : HasDerivAt g (f r+A*g r-B*j r) r := by
    convert (hasDerivAt_id r).ofReal_comp.mul (d1 r) using 1 <;> dsimp only [g,j,id_eq] <;> push_cast <;> ring
  have a := integral_eq_zero_of_hasDerivAt_of_integrable d1 ((fi.const_mul A).sub (gi.const_mul B)) fi
  have b := integral_eq_zero_of_hasDerivAt_of_integrable d2 ((fi.add (gi.const_mul A)).sub (ji.const_mul B)) gi
  rw [integral_sub (fi.const_mul A) (gi.const_mul B),integral_const_mul,integral_const_mul] at a
  rw [integral_sub (fi.add (gi.const_mul A)) (ji.const_mul B),integral_add fi (gi.const_mul A),
    integral_const_mul,integral_const_mul] at b
  change A*(∫ r,f r)-B*(∫ r,g r)=0 at a
  change (∫ r,f r)+A*(∫ r,g r)-B*(∫ r,j r)=0 at b
  change (∫ r,j r)=(1/(2*(β:ℂ))-(v:ℂ)^2/(β:ℂ)^2)*(∫ r,f r)
  have bn : (β:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have rel : B^2*(∫ r,j r)=(B+A^2)*(∫ r,f r) := by
    linear_combination -B*b-A*a
  have Ai : A^2= -4*(v:ℂ)^2 := by dsimp only [A]; rw [mul_pow,I_sq]; ring
  rw [Ai] at rel
  dsimp only [B] at rel
  apply mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero (by norm_num : (2:ℂ)≠0) bn))
  calc
    _ = (2*(β:ℂ)+ -4*(v:ℂ)^2)*(∫ r,f r) := rel
    _ = _ := by field_simp [bn] <;> ring

/-- Full-line transform; the phase is exp(2 i v r), with no remaining
2π convention to be chosen in the orbital logarithmic coordinate. -/
theorem fourier_gaussian_weight {K : ℝ} (hK : 0<K) (v : ℝ) :
    (∫ r : ℝ, (weight K r:ℂ)*character v r)=
      ((Real.sqrt Real.pi*K^3/2*(1-2*(K*v)^2)*Real.exp (-(K*v)^2):ℝ):ℂ) := by
  let β := (K^2)⁻¹
  have β0 : 0<β := inv_pos.mpr (sq_pos_of_pos hK)
  have βC : (β:ℂ)≠0 := Complex.ofReal_ne_zero.mpr β0.ne'
  have hF := fourierIntegral_gaussian (b:=(β:ℂ)) (by simpa only [Complex.ofReal_re] using β0) (2*(v:ℂ))
  have F : (∫ r : ℝ,kernel β v r)=((Real.sqrt Real.pi*K*Real.exp (-(K*v)^2):ℝ):ℂ) := by
    change (∫ r : ℝ,exp (I*(2*(v:ℂ))*(r:ℂ))*exp (-(β:ℂ)*(r:ℂ)^2))=_
    rw [hF]
    have ext1 : -(2*(v:ℂ))^2/(4*(β:ℂ))=((-((K*v)^2):ℝ):ℂ) := by
      dsimp only [β]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hK.ne'] <;> ring
    have ext2 : ((Real.pi:ℂ)/(β:ℂ))^(1/2:ℂ)=((Real.sqrt (Real.pi/β):ℝ):ℂ) := by
      rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow (div_nonneg Real.pi_pos.le β0.le)]
      simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    have ext3 : Real.sqrt (Real.pi/β)=Real.sqrt Real.pi*K := by
      dsimp only [β]
      rw [div_inv_eq_mul,Real.sqrt_mul Real.pi_pos.le,Real.sqrt_sq hK.le]
    rw [ext1,ext2,ext3,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have ker (r : ℝ) : (weight K r:ℂ)*character v r=(r:ℂ)^2*kernel β v r := by
    have expval : -(r/K)^2= -β*r^2 := by dsimp only [β]; rw [div_pow]; ring
    simp only [weight,expval,kernel,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow]
    ring
  simp_rw [ker]
  rw [moment β0 v,F]
  dsimp only [β]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hK.ne'] <;> ring

/-- The diagonal has its exact cubic price before the shell factor K is
divided out. -/
theorem full_gaussian_diagonal {K : ℝ} (hK : 0<K) :
    (∫ r : ℝ,weight K r)=Real.sqrt Real.pi*K^3/2 := by
  have F := fourier_gaussian_weight hK 0
  simp only [character,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one,
    zero_pow (by decide : 2≠0),neg_zero,Real.exp_zero,sub_zero,integral_complex_ofReal] at F
  exact Complex.ofReal_injective F

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovFourier20261113
end

