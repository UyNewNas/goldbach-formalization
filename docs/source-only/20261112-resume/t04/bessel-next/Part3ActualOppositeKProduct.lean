import ImbalancedChen.Part3ImaginaryKExponentialOrderBound
import ImbalancedChen.Part3ActualKUnequalHyperbolicDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The oscillatory K product of the opposite-sign physical Bruhat
orbit. The order may be complex, including the exceptional real orders. -/
namespace ImbalancedChen.Part3.ActualOppositeKProduct20261112

noncomputable section
open Set Filter MeasureTheory Complex
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open ImaginaryKContourRectangle20261025a ImaginaryKExponentialOrderBound20261025a
open ActualKUnequalHyperbolicDistance20261026b

def oscillation (b v : ℝ) : ℂ := exp (I*((b*Real.sinh v : ℝ) : ℂ))

theorem norm_oscillation (b v : ℝ) : ‖oscillation b v‖=1 := by
  simp [oscillation,Complex.norm_exp,Complex.mul_re]

private theorem tilted_zero {a : ℝ} (ha : 0<a) (b : ℝ) :
    (∫ v : ℝ, exp ((-a*Real.cosh v : ℝ) : ℂ)*oscillation b v) =
      2*complexOrderK 0 (Real.sqrt (a^2+b^2)) := by
  let R := Real.sqrt (a^2+b^2)
  let θ := Real.arctan (-b/a)
  have hR : 0<R := by dsimp [R]; positivity
  have hθ : |θ|<Real.pi/2 := abs_lt.mpr (Real.arctan_mem_Ioo _)
  have root : Real.sqrt (1+(-b/a)^2)=R/a := by
    have R2 : R^2=a^2+b^2 := Real.sq_sqrt (by positivity)
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg hR.le ha.le)).mp
    rw [Real.sq_sqrt (by positivity),div_pow,R2]
    field_simp [ha.ne'] <;> ring
  have c : R*Real.cos θ=a := by
    rw [Real.cos_arctan,root]
    field_simp [ha.ne',hR.ne'] <;> ring
  have s : R*Real.sin θ= -b := by
    rw [Real.sin_arctan,root]
    field_simp [ha.ne',hR.ne'] <;> ring
  have eqn (v : ℝ) : exp ((-a*Real.cosh v : ℝ) : ℂ)*oscillation b v = horizontal R 0 θ v := by
    rw [oscillation,← exp_add]
    simp only [horizontal,contourKernel,Complex.ofReal_zero,zero_mul,add_zero,Complex.cosh_add,
      Complex.cosh_mul_I,Complex.sinh_mul_I,← Complex.ofReal_cosh,← Complex.ofReal_sinh,
      ← Complex.ofReal_cos,← Complex.ofReal_sin]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) c
    have hs := congrArg (fun x : ℝ => (x : ℂ)) s
    push_cast at hc hs ⊢
    congr 1
    linear_combination hc*(Real.cosh v : ℂ)+hs*(Real.sinh v : ℂ)*I
  simp_rw [eqn]
  rw [← horizontal_integral_eq_shift hR 0 θ hθ,horizontal_zero_integral hR]
  simp only [Complex.ofReal_zero,zero_mul,R]

private def joint (ν : ℂ) (c b : ℝ) (v r : ℝ) : ℂ :=
  oscillation b v*tiltedDensity (2*ν) (c*Real.cosh v) r

private theorem joint_integrable (ν : ℂ) {c : ℝ} (hc : 0<c) (b : ℝ) :
    Integrable (Function.uncurry (joint ν c b)) ((volume : Measure ℝ).prod volume) := by
  have h := (RealOrderKPositiveLaplace.tiltedCoshDensity_integrable 0 (half_pos hc)).mul_prod
    (RealOrderKPositiveLaplace.tiltedCoshDensity_integrable (2*ν.re) (half_pos hc))
  apply h.mono' (by
    have : Continuous (Function.uncurry (joint ν c b)) := by
      unfold Function.uncurry joint oscillation tiltedDensity
      fun_prop
    exact this.aestronglyMeasurable)
  apply ae_of_all
  rintro ⟨v,r⟩
  simp only [Function.uncurry,joint,norm_mul,norm_oscillation,one_mul,tiltedDensity,Complex.norm_exp,
    Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.ofNat_re,Complex.ofNat_im,zero_mul,RealOrderKPositiveLaplace.tiltedCoshDensity,
    add_zero,← Real.exp_add,Real.exp_le_exp]
  have V := Real.one_le_cosh v
  have W := Real.one_le_cosh r
  nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr V) (Real.cosh_pos r).le),
    mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr W) (Real.cosh_pos v).le)]

/-- The sign comes from the conjugation in the original N,M pairing.
No spectral growth bound or unspecified oscillatory integral enters. -/
theorem opposite_product (ν : ℂ) {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    let c := 2*Real.sqrt (A*B)
    let f := fun v : ℝ => oscillation (A-B) v * complexOrderK (2*ν) (c*Real.cosh v)
    Integrable f ∧ (∫ v : ℝ,f v)=complexOrderK ν A*complexOrderK ν B := by
  let c := 2*Real.sqrt (A*B)
  have hc : 0<c := by dsimp [c]; positivity
  let J := joint ν c (A-B)
  have hJ := joint_integrable ν hc (A-B)
  have L (v : ℝ) : (∫ r : ℝ,J v r)=2*(oscillation (A-B) v*complexOrderK (2*ν) (c*Real.cosh v)) := by
    dsimp only [J,joint]
    rw [integral_const_mul,tiltedDensity_integral _ (mul_pos hc (Real.cosh_pos v))]
    ring
  have c2 : c^2=4*(A*B) := by
    dsimp only [c]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hA.le hB.le)]
    ring
  have d (r : ℝ) : Real.sqrt ((c*Real.cosh r)^2+(A-B)^2)=hyperbolicDistance A B (-2*r) := by
    unfold hyperbolicDistance
    rw [show -2*r= -(2*r) by ring,Real.cosh_neg,Real.cosh_two_mul,mul_pow,c2]
    congr 1
    linear_combination 2*A*B*(Real.cosh_sq_sub_sinh_sq r)
  have R (r : ℝ) : (∫ v : ℝ,J v r)=2*weightedDistanceKernel ν A B (-2*r) := by
    have sep (v : ℝ) : J v r = exp ((2*ν)*(r : ℂ))*
        (exp ((-(c*Real.cosh r)*Real.cosh v : ℝ) : ℂ)*oscillation (A-B) v) := by
      simp only [J,joint,tiltedDensity,oscillation,← exp_add,Complex.ofReal_mul,Complex.ofReal_neg]
      congr 1
      ring
    simp_rw [sep]
    rw [integral_const_mul,tilted_zero (mul_pos hc (Real.cosh_pos r)),d,weightedDistanceKernel]
    push_cast
    rw [show -ν*(-2*(r : ℂ))=(2*ν)*(r : ℂ) by ring]
    ring
  let f := fun v : ℝ => oscillation (A-B) v*complexOrderK (2*ν) (c*Real.cosh v)
  have hx : Integrable (fun v => 2*f v) := by
    simpa only [Function.uncurry,L,f,J] using hJ.integral_prod_left
  have I : Integrable f := by
    simpa only [show ∀ v,(2:ℂ)⁻¹*(2*f v)=f v by intro v; ring] using hx.const_mul ((2:ℂ)⁻¹)
  refine ⟨I,?_⟩
  have H := integral_integral_swap (f := J) hJ
  simp_rw [L,R] at H
  rw [integral_const_mul,integral_const_mul,Measure.integral_comp_mul_left (weightedDistanceKernel ν A B) (-2)]
    at H
  rw [actual_K_unequal_distance_full_line ν hA hB]
  norm_num [Complex.real_smul] at H
  linear_combination H/2

end
end ImbalancedChen.Part3.ActualOppositeKProduct20261112
