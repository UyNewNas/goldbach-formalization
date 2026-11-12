import ImbalancedChen.Part3ImaginaryKExponentialOrderBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Fourier transport across the actual width pi.  The same estimate treats
the complementary spectral parameters without any appeal to a real-axis limit. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStripContour20261112

open Set Filter MeasureTheory Complex
open scoped Topology

def wave (ξ z : ℂ) := Complex.exp (-(Complex.I*ξ*z))
def angular (f : ℝ→ℂ) (ξ : ℂ) := ∫ x : ℝ, f x*wave ξ x

private theorem abs_exp_integrable {a : ℝ} (ha : 0<a) :
    Integrable (fun x : ℝ => Real.exp (-a*|x|)) := by
  rw [←integrableOn_univ,←Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic ha 0).congr_fun _ measurableSet_Iic
    intro x hx
    rw [abs_of_nonpos hx]; congr 1; ring
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun _ measurableSet_Ioi
    intro x hx; rw [abs_of_pos hx]

theorem norm_wave (ξ : ℂ) (x y : ℝ) :
    ‖wave ξ ((x:ℂ)+(y:ℂ)*I)‖=Real.exp (ξ.im*x+ξ.re*y) := by
  rw [wave,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]; ring

theorem norm_wave_real (ξ : ℂ) (x : ℝ) : ‖wave ξ x‖=Real.exp (ξ.im*x) := by
  simpa using norm_wave ξ x 0

theorem angular_L1 {f : ℝ→ℂ} (hf : Continuous f)
    {C : ℝ} (hC : 0≤C) (h : ∀ x,‖f x‖≤C*Real.exp (-|x|))
    {ξ : ℂ} (hξ : |ξ.im|<1) : Integrable (fun x : ℝ => f x*wave ξ x) := by
  apply ((abs_exp_integrable (show 0<1-|ξ.im| by linarith)).const_mul C).mono'
    ((hf.mul (by unfold wave; fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    rw [norm_mul,norm_wave_real]
    have he : ξ.im*x≤|ξ.im|*|x| := by simpa [abs_mul] using le_abs_self (ξ.im*x)
    calc
      _ ≤ C*Real.exp (-|x|)*Real.exp (ξ.im*x) := mul_le_mul_of_nonneg_right (h x) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_assoc,←Real.exp_add]; gcongr <;> linarith

/-- The horizontal equality uses both finite vertical edges, with their common
majorant tending to zero for every complex angular frequency in the open strip. -/
theorem horizontal {B : ℂ→ℂ} (hol : Differentiable ℂ B)
    {C : ℝ} (hC : 0≤C) (bound : ∀ x y : ℝ, 0≤y → y≤Real.pi →
      ‖B ((x:ℂ)+y*I)‖≤C*Real.exp (-|x|)) {ξ : ℂ} (strip : |ξ.im|<1) :
    angular (fun x => B ((x:ℂ)+Real.pi*I)) ξ =
      Complex.exp (-(Real.pi:ℂ)*ξ)*angular (fun x => B x) ξ := by
  let F := fun z : ℂ => B z*wave ξ z
  let edge := fun R : ℝ => ∫ y in (0:ℝ)..Real.pi,F ((R:ℂ)+y*I)
  have g (x y : ℝ) (hy : 0≤y) (hp : y≤Real.pi) :
      ‖F ((x:ℂ)+y*I)‖ ≤ (C*Real.exp (|ξ.re|*Real.pi))*Real.exp (-(1-|ξ.im|)*|x|) := by
    rw [show ‖F ((x:ℂ)+y*I)‖=‖B ((x:ℂ)+y*I)‖*‖wave ξ ((x:ℂ)+y*I)‖ by exact norm_mul _ _,norm_wave]
    have hI : ξ.im*x ≤ |ξ.im|*|x| := by simpa [abs_mul] using le_abs_self (ξ.im*x)
    have hR : ξ.re*y ≤ |ξ.re|*Real.pi :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hy).trans (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
    apply (mul_le_mul_of_nonneg_right (bound x y hy hp) (Real.exp_pos _).le).trans
    rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr; linarith
  have gi (y : ℝ) (hy : 0≤y) (hp : y≤Real.pi) : Integrable (fun x : ℝ => F ((x:ℂ)+y*I)) := by
    apply ((abs_exp_integrable (show 0<1-|ξ.im| by linarith)).const_mul (C*Real.exp (|ξ.re|*Real.pi))).mono'
    · dsimp [F,wave]; fun_prop (disch := exact hol.continuous)
    · exact ae_of_all _ fun x => g x y hy hp
  have edge_bound (R : ℝ) : ‖edge R‖ ≤
      ((C*Real.exp (|ξ.re|*Real.pi))*Real.exp (-(1-|ξ.im|)*|R|))*Real.pi := by
    simpa only [edge,sub_zero,abs_of_pos Real.pi_pos] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=Real.pi)
        (f:=fun y : ℝ => F ((R:ℂ)+y*I)) fun y hy => by
          rw [Set.uIoc_of_le Real.pi_pos.le] at hy
          exact g _ _ hy.1.le hy.2)
  have t : Tendsto (fun R : ℝ => ((C*Real.exp (|ξ.re|*Real.pi))*Real.exp (-(1-|ξ.im|)*R))*Real.pi)
      atTop (𝓝 0) := by
    have k := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (show -(1-|ξ.im|)<0 by linarith))
    simpa using (k.const_mul (C*Real.exp (|ξ.re|*Real.pi))).mul_const Real.pi
  have Z (sgn : ℝ→ℝ) (hsgn : ∀ R≥(0:ℝ),|sgn R|=R) :
      Tendsto (fun R => edge (sgn R)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ t
    filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
    simpa only [hsgn R hR] using edge_bound (sgn R)
  have zd := Z (fun x => x) (fun _ h => abs_of_nonneg h)
  have zl := Z Neg.neg (fun _ h => by rw [abs_neg,abs_of_nonneg h])
  have horiz (y : ℝ) (hy : 0≤y) (hp : y≤Real.pi) :=
    intervalIntegral_tendsto_integral (gi y hy hp) tendsto_neg_atTop_atBot tendsto_id
  have zero (R : ℝ) := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F (⟨-R,0⟩:ℂ) (⟨R,Real.pi⟩:ℂ) ((hol.mul (by unfold wave; fun_prop)).differentiableOn)
  have lim := (((horiz 0 le_rfl Real.pi_pos.le).sub (horiz Real.pi Real.pi_pos.le le_rfl)).add
      (zd.const_mul I)).sub (zl.const_mul I)
  have eq : (∫ x : ℝ,F x) = ∫ x : ℝ,F ((x:ℂ)+Real.pi*I) := by
    have hz : Tendsto (fun _ : ℝ => (0:ℂ)) atTop
        (𝓝 ((∫ x : ℝ,F x)-∫ x : ℝ,F ((x:ℂ)+Real.pi*I))) := by
      convert lim using 1
      · funext R
        simpa [edge,smul_eq_mul] using (zero R).symm
      · simp
    exact sub_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)
  have fac (x : ℝ) : wave ξ ((x:ℂ)+Real.pi*I)=Complex.exp ((Real.pi:ℂ)*ξ)*wave ξ x := by
    rw [wave,wave,←Complex.exp_add]
    congr 1; ring_nf; simp [I_sq]
  dsimp only [F] at eq
  simp_rw [fac,mul_left_comm (B _) (Complex.exp _)] at eq
  rw [integral_const_mul] at eq
  unfold angular
  rw [eq,←mul_assoc,←Complex.exp_add]
  simp

/-- Integration by parts for precisely the angular convention used by
the two sides of the Cauchy rectangle. -/
theorem angular_derivative {ξ : ℂ} {f g : ℝ→ℂ} (hf : ∀ x, HasDerivAt f (g x) x)
    (fg : Integrable (fun x : ℝ => f x*wave ξ x))
    (gg : Integrable (fun x : ℝ => g x*wave ξ x)) :
    angular g ξ=I*ξ*angular f ξ := by
  have hw (x : ℝ) : HasDerivAt (fun t : ℝ => wave ξ t) ((-I*ξ)*wave ξ x) x := by
    have D := (((hasDerivAt_id (x:=(x:ℂ))).const_mul (-I*ξ)).cexp).comp_ofReal
    convert D using 1 <;> first | funext t; dsimp [wave]; ring_nf | dsimp [wave]; ring
  have hi : Integrable (fun x : ℝ => f x*((-I*ξ)*wave ξ x)) := by
    convert fg.const_mul (-I*ξ) using 1; funext x; ring
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u:=f) (v:=fun t : ℝ => wave ξ t)
    (u':=g) (v':=fun x => (-I*ξ)*wave ξ x) (fun x _ => hf x) (fun x _ => hw x) hi gg fg
  change (∫ x : ℝ,f x*((-I*ξ)*wave ξ x)) = -angular g ξ at ibp
  simp_rw [mul_left_comm (f _) (-I*ξ)] at ibp
  rw [integral_const_mul] at ibp
  unfold angular at *
  linear_combination ibp

end ImbalancedChen.Part3.OriginalPositiveStripContour20261112
end
