import ImbalancedChen.Part3OriginalRegularPreKuznetsovFourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Upper-semicircle integral in the positive same-cusp Bruhat kernel.
Its derivative turns the actual exponential seed into the sine in the
first Deshouillers--Iwaniec Gaussian orbital formula. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPreKuznetsovAngle20261113
open Complex Filter Set MeasureTheory
open scoped Topology

def ray (θ : ℝ) : ℂ := exp ((θ:ℂ)*I)
def angularWave (u θ : ℝ) : ℂ := exp ((u:ℂ)*I*ray θ)
def radialDerivative (u θ : ℝ) : ℂ := I*ray θ*angularWave u θ
def angular (u : ℝ) : ℂ := ∫ θ in (0:ℝ)..Real.pi,angularWave u θ

theorem ray_components (θ : ℝ) : ray θ=(Real.cos θ:ℂ)+(Real.sin θ:ℂ)*I := by
  simp only [ray,Complex.exp_mul_I,Complex.ofReal_cos,Complex.ofReal_sin]

theorem angular_wave_norm (u θ : ℝ) : ‖angularWave u θ‖=Real.exp (-u*Real.sin θ) := by
  rw [angularWave,Complex.norm_exp,ray_components]
  congr 1
  simp [Complex.mul_re,Complex.mul_im] <;> ring

theorem wave_norm_le_one {u θ : ℝ} (hu : 0≤u) (hθ : θ∈Icc 0 Real.pi) :
    ‖angularWave u θ‖≤1 := by
  rw [angular_wave_norm,Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (Real.sin_nonneg_of_mem_Icc hθ)

private theorem ray_norm (θ : ℝ) : ‖ray θ‖=1 := by simp [ray,Complex.norm_exp,Complex.mul_re]

private theorem radial_diff (u θ : ℝ) :
    HasDerivAt (fun v : ℝ => angularWave v θ) (radialDerivative u θ) u := by
  convert (((hasDerivAt_id u).ofReal_comp.mul_const I).mul_const (ray θ)).cexp using 1 <;>
    simp only [angularWave,radialDerivative,id_eq,Complex.ofReal_one,one_mul] <;> ring

private theorem ray_diff (θ : ℝ) : HasDerivAt ray (I*ray θ) θ := by
  convert ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp using 1 <;>
    simp only [ray,id_eq,Complex.ofReal_one,one_mul] <;> ring

private theorem theta_diff (u θ : ℝ) :
    HasDerivAt (angularWave u) ((-(u:ℂ))*ray θ*angularWave u θ) θ := by
  have k : ((u:ℂ)*I)*(I*ray θ)= -(u:ℂ)*ray θ := by
    linear_combination (norm := ring) ((u:ℂ)*ray θ)*I_sq
  simpa only [angularWave,k,mul_comm (Complex.exp _)] using ((ray_diff θ).const_mul ((u:ℂ)*I)).cexp

private theorem integral_radial (u : ℝ) (hu : u≠0) :
    (∫ θ in (0:ℝ)..Real.pi,radialDerivative u θ)=((-2*Real.sin u/u:ℝ):ℂ) := by
  let d := fun θ : ℝ => (-(u:ℂ))*ray θ*angularWave u θ
  have cd : Continuous d := by unfold d angularWave ray; fun_prop
  have T := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=Real.pi) (f:=angularWave u) (f':=d)
    (fun θ _ => theta_diff u θ) (cd.intervalIntegrable 0 Real.pi)
  have rayπ : ray Real.pi= -1 := by simp [ray_components]
  have ray0 : ray 0=1 := by simp [ray_components]
  have ends : angularWave u Real.pi-angularWave u 0= -2*(Real.sin u:ℂ)*I := by
    simp only [angularWave,rayπ,ray0,mul_neg_one,mul_one,←neg_mul,Complex.exp_mul_I,
      Complex.cos_neg,Complex.sin_neg,←Complex.ofReal_sin]
    ring
  rw [ends] at T
  have uC := Complex.ofReal_ne_zero.mpr hu
  have E (θ : ℝ) : radialDerivative u θ=(-I/(u:ℂ))*d θ := by
    dsimp only [radialDerivative,d]; field_simp [uC] <;> ring
  simp_rw [E,intervalIntegral.integral_const_mul]
  rw [T]
  push_cast
  field_simp [uC]
  linear_combination (norm := ring) (2*(Real.sin u:ℂ))*I_sq

/-- Differentiation under the actual half-circle integral, including its
endpoint evaluation. -/
theorem angular_derivative {u : ℝ} (hu : 0<u) :
    HasDerivAt angular ((-2*Real.sin u/u:ℝ):ℂ) u := by
  have U : Ioi (0:ℝ)∈𝓝 u := Ioi_mem_nhds hu
  have F (v : ℝ) : Continuous (angularWave v) := by unfold angularWave ray; fun_prop
  have D (v : ℝ) : Continuous (radialDerivative v) := by unfold radialDerivative angularWave ray; fun_prop
  have bound : ∀ᵐ θ : ℝ ∂volume, θ∈Ι (0:ℝ) Real.pi →
      ∀ v∈Ioi (0:ℝ),‖radialDerivative v θ‖≤1 := ae_of_all _ (fun θ hθ v hv => by
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    simpa only [radialDerivative,norm_mul,norm_I,ray_norm,one_mul] using wave_norm_le_one hv.le ⟨hθ.1.le,hθ.2⟩)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=angularWave) (F':=radialDerivative) (bound:=fun _ : ℝ => (1:ℝ)) (μ:=volume)
    (a:=(0:ℝ)) (b:=Real.pi) U (Eventually.of_forall (fun v => (F v).aestronglyMeasurable))
    ((F u).intervalIntegrable 0 Real.pi) ((D u).aestronglyMeasurable) bound intervalIntegrable_const
    (ae_of_all _ (fun θ _ v _ => radial_diff v θ))
  simpa only [angular,integral_radial u hu.ne'] using h.2

theorem angular_norm {u : ℝ} (hu : 0≤u) : ‖angular u‖≤Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=Real.pi)
    (C:=1) (f:=angularWave u) (fun θ hθ => by
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      exact wave_norm_le_one hu ⟨hθ.1.le,hθ.2⟩)
  simpa only [angular,sub_zero,abs_of_pos Real.pi_pos,one_mul,mul_one] using h

end ImbalancedChen.Part3.OriginalRegularPreKuznetsovAngle20261113
end
