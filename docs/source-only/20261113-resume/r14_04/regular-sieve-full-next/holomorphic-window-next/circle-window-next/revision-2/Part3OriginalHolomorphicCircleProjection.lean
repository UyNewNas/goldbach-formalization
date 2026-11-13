import ImbalancedChen.Part3OriginalHolomorphicPoissonHeight

/-! Project the summed complex Bessel height to its real circle kernel.
The imaginary part of the complex phase retains the odd orders. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicCircleProjection20261113
open Set MeasureTheory
open OriginalHolomorphicBesselCoefficient20261113 (wave)
open OriginalHolomorphicPoissonHeight20261113 (heightKernel orderTerm poisson_height_sum)
open CompletedKWeightedIntegral20261026b (integerPhase integerPhase_norm)
open Real

def theta (y : ℝ) := 2*π*y
def radius (u : ℝ) := Real.exp (-u)
def polar (u y : ℝ) : ℂ := (radius u : ℂ)*integerPhase (-1) y
def denominator (u θ : ℝ) := 1+(radius u)^2-2*radius u*cos θ
def rational (u θ : ℝ) :=
  (radius u*(1+(radius u)^2)*cos θ-2*(radius u)^2)/(denominator u θ)^2
def radialImag (u θ : ℝ) :=
  radius u*((radius u)^2-1)*sin θ/(denominator u θ)^2

theorem den_positive {u : ℝ} (hu : 0<u) (θ : ℝ) : 0<denominator u θ := by
  have rp : 0<radius u := exp_pos _
  have r1 : radius u<1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have d := sq_pos_of_pos (sub_pos.mpr r1)
  have h := mul_nonneg rp.le (sub_nonneg.mpr (cos_le_one θ))
  dsimp only [denominator]
  nlinarith only [d,h]

private theorem polar_parts (u y : ℝ) :
    (polar u y).re=radius u*cos (theta y) ∧ (polar u y).im= -(radius u*sin (theta y)) := by
  have E : 2*π*((-1:ℤ):ℝ)*y= -(theta y) := by dsimp only [theta]; push_cast <;> ring
  simp only [polar,integerPhase,E,Complex.exp_mul_I,Complex.ofReal_neg,Complex.cos_neg,
    Complex.sin_neg,←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  constructor <;> ring

theorem height_coordinates {u : ℝ} (hu : 0<u) (y : ℝ) :
    (heightKernel u y).re=rational u (theta y) ∧
    (heightKernel u y).im=radialImag u (theta y) := by
  let Z := polar u y
  let r := radius u
  let D := denominator u (theta y)
  obtain ⟨re,im⟩ := polar_parts u y
  have trig := sin_sq_add_cos_sq (theta y)
  have norm : Complex.normSq (1-Z)=D := by
    simp only [Z,D,denominator,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.one_re,Complex.one_im,re,im]
    linear_combination r^2*trig
  have i : (1-Z)⁻¹=(star (1-Z))/(D:ℂ) := by
    rw [Complex.inv_def,norm]
    simp only [div_eq_mul_inv,Complex.ofReal_inv,Complex.star_def]
  have expr : heightKernel u y = Z*(star (1-Z))^2/((D^2:ℝ):ℂ) := by
    change Z/(1-Z)^2=_
    rw [div_eq_mul_inv,←inv_pow,i,div_pow,Complex.ofReal_pow]
    ring
  rw [expr]
  have base : (Z*(star (1-Z))^2).re = r*(1+r^2)*cos (theta y)-2*r^2 ∧
      (Z*(star (1-Z))^2).im = r*(r^2-1)*sin (theta y) := by
    simp only [Z,pow_two,Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,
      Complex.conj_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,re,im]
    constructor
    · linear_combination (r^3*cos (theta y)-2*r^2)*trig
    · linear_combination r^3*sin (theta y)*trig
  simp [Complex.div_ofReal_re,Complex.div_ofReal_im,base.1,base.2,rational,radialImag,D,r]

private theorem rational_cont {u : ℝ} (hu : 0<u) : Continuous (rational u) :=
  ((continuous_const.mul continuous_cos).sub continuous_const).div
    ((continuous_const.sub (continuous_const.mul continuous_cos)).pow 2)
    (fun y => (sq_pos_of_pos (den_positive hu y)).ne')

private theorem radial_imag_cont {u : ℝ} (hu : 0<u) : Continuous (radialImag u) :=
  (continuous_const.mul continuous_sin).div
    ((continuous_const.sub (continuous_const.mul continuous_cos)).pow 2)
    (fun y => (sq_pos_of_pos (den_positive hu y)).ne')

theorem wave_coordinates (x y : ℝ) :
    (wave x y).re=cos (x*cos (theta y)) ∧ (wave x y).im=sin (x*cos (theta y)) := by
  simp only [wave,theta,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  constructor <;> ring

private theorem reflection (x u : ℝ) :
    (∫ y in (0:ℝ)..1,cos (x*cos (theta y))*radialImag u (theta y))=0 := by
  let f := fun y : ℝ => cos (x*cos (theta y))*radialImag u (theta y)
  have ref (y : ℝ) : f (1-y) = -f y := by
    have e : theta (1-y)=2*π-theta y := by dsimp only [theta]; ring
    dsimp only [f,radialImag,denominator]
    rw [e,cos_two_pi_sub,sin_two_pi_sub]
    ring
  have h := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=1) f 1
  simp only [sub_self,sub_zero,ref,intervalIntegral.integral_neg] at h
  change (∫ y in (0:ℝ)..1, f y)=0
  linarith only [h]

def imaginaryHeight (u x : ℝ) := (∑' h, orderTerm u x h).im

/-- Imaginary part of the native order sum equals the real circle
integral with the differentiated Poisson kernel. -/
theorem native_circle_integral {u : ℝ} (hu : 0<u) (x : ℝ) :
    imaginaryHeight u x =
      ∫ y in (0:ℝ)..1, rational u (theta y)*sin (x*cos (theta y)) := by
  have ct : Continuous theta := continuous_const.mul continuous_id
  have wc : Continuous (wave x) := by unfold wave; fun_prop
  have C : Continuous (heightKernel u) := by
    have H : ∀ y, 1-polar u y≠0 := by
      intro y h
      have eq : polar u y=1 := by linear_combination -h
      have norm := congrArg norm eq
      have r0 : 0<radius u := exp_pos _
      have r1 : radius u<1 := exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
      simp only [polar,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos r0,
        integerPhase_norm,mul_one,norm_one] at norm
      exact r1.ne norm
    have p : Continuous (polar u) := continuous_const.mul
      (CompletedKWeightedIntegral20261026b.integerPhase_continuous _)
    exact p.div ((continuous_const.sub p).pow 2) (fun y => pow_ne_zero 2 (H y))
  have Q := ((rational_cont hu).comp ct).mul
    (continuous_sin.comp (continuous_const.mul (continuous_cos.comp ct)))
  have E := (continuous_cos.comp (continuous_const.mul (continuous_cos.comp ct))).mul
    ((radial_imag_cont hu).comp ct)
  rw [imaginaryHeight,(poisson_height_sum hu x).tsum_eq]
  calc
    _ = ∫ y in (0:ℝ)..1, (wave x y*heightKernel u y).im := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      exact (integral_im (((wc.mul C).intervalIntegrable (0:ℝ) 1).1)).symm
    _ = ∫ y in (0:ℝ)..1, rational u (theta y)*sin (x*cos (theta y))+
          cos (x*cos (theta y))*radialImag u (theta y) := by
      apply intervalIntegral.integral_congr
      intro y _
      rw [Complex.mul_im,(wave_coordinates x y).1,(wave_coordinates x y).2,
        (height_coordinates hu y).1,(height_coordinates hu y).2]
      ring
    _ = _ := by rw [intervalIntegral.integral_add (Q.intervalIntegrable _ _) (E.intervalIntegrable _ _),
      reflection,add_zero]

end ImbalancedChen.Part3.OriginalHolomorphicCircleProjection20261113
end
