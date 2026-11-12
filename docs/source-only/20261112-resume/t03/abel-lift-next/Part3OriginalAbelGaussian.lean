import ImbalancedChen.Part3OriginalPrescribedAbelProfile
import ImbalancedChen.Part3ActualMarkedBruhatTest
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Gaussian on the ratio of the two positive heights. Its Fourier
transform is normalized for the period-one geometric phase. -/
namespace ImbalancedChen.Part3.OriginalAbelGaussian
noncomputable section
open Set MeasureTheory Complex
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalPrescribedAbelProfile
open P3Period64NativeReconstructionSourceOnly (e norm_e)

def g (w : ℝ) : ℝ := 2*Real.sqrt Real.pi*Real.cosh w*
  Real.exp (-(4*Real.pi^2)*Real.sinh w^2)

def height (ell : D4→ℤ) (Y a b : ℝ) : ℂ :=
  if 0<a ∧ 0<b then h ell Y (a*b)*(g (Real.log (a/b)/2):ℝ) else 0

theorem g_pos (w : ℝ) : 0<g w := by unfold g; positivity

private theorem sinh_chart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (G : ℝ→V) :
    (∫w:ℝ,Real.cosh w • G (Real.sinh w))=∫t:ℝ,G t := by
  have J := integral_image_eq_integral_abs_deriv_smul measurableSet_univ
    (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt) Real.sinh_injective.injOn G
  simpa [image_univ,Real.sinh_surjective.range_eq,abs_of_pos (Real.cosh_pos _)] using J.symm

theorem g_integrable : Integrable g := by
  let G := fun t:ℝ => (2*Real.sqrt Real.pi)*Real.exp (-(4*Real.pi^2)*t^2)
  have Gint : Integrable G := (integrable_exp_neg_mul_sq (by positivity : 0<4*Real.pi^2)).const_mul _
  have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
    (fun x _ => (Real.hasDerivAt_sinh x).hasDerivWithinAt) Real.sinh_injective.injOn G
  rw [image_univ,Real.sinh_surjective.range_eq,integrableOn_univ,integrableOn_univ] at J
  exact (J.mp Gint).congr (ae_of_all _ (fun x => by
    rw [abs_of_pos (Real.cosh_pos x),smul_eq_mul]; dsimp [g,G]; ring))

/-- Signed frequency t includes both signs of the original real orbit. -/
theorem transform (t : ℝ) :
    (∫w:ℝ,(g w:ℂ)*e (2*t*Real.sinh w))=(Real.exp (-t^2):ℝ) := by
  let B : ℂ := ((4*Real.pi^2:ℝ):ℂ)
  let c : ℂ := ((4*Real.pi*t:ℝ):ℂ)
  have hB : 0<B.re := by dsimp [B]; simpa using (by positivity : 0<4*Real.pi^2)
  have F := fourierIntegral_gaussian (b := B) hB c
  let Z := fun z:ℝ => (2*Real.sqrt Real.pi:ℂ)*
    (Complex.exp (I*c*(z:ℂ))*Complex.exp (-B*(z:ℂ)^2))
  have chart : (∫w:ℝ,(g w:ℂ)*e (2*t*Real.sinh w))=∫z:ℝ,Z z := by
    rw [←sinh_chart Z]
    apply integral_congr_ae; filter_upwards with w
    simp only [g,Z,e,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_exp,Complex.ofReal_neg,B,c]
    push_cast
    ring_nf
  have root : ((Real.pi:ℂ)/B)^(1/2:ℂ) = ((2*Real.sqrt Real.pi:ℂ))⁻¹ := by
    have h0 := Real.pi_pos
    have r : Real.sqrt (Real.pi/(4*Real.pi^2))= (2*Real.sqrt Real.pi)⁻¹ := by
      apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (by positivity),inv_pow,mul_pow,Real.sq_sqrt h0.le]
      field_simp [h0.ne']; ring
    calc
      _ = (((Real.pi/(4*Real.pi^2))^(1/2:ℝ):ℝ):ℂ) := by
        rw [Complex.ofReal_cpow (by positivity)]; dsimp [B]; push_cast; rfl
      _ = _ := by rw [←Real.sqrt_eq_rpow,r]; push_cast; rfl
  have arg : -(c^2)/(4*B)=((-t^2:ℝ):ℂ) := by
    dsimp [c,B]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]; ring
  rw [chart,show (∫z:ℝ,Z z)=_ from integral_const_mul _ _,F,root,arg,←Complex.ofReal_exp]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne']

def productAt (k s : ℝ) := k/(1+s^2)
def dilation (p w : ℝ) := Real.sqrt p*Real.exp w

theorem coordinate_identity {p : ℝ} (hp : 0<p) (w : ℝ) :
    let a := dilation p w
    0<a ∧ 0<p/a ∧ a*(p/a)=p ∧ Real.log (a/(p/a))/2=w ∧
      a-p/a=2*Real.sqrt p*Real.sinh w := by
  let r := Real.sqrt p
  have r0 : 0<r := Real.sqrt_pos.mpr hp
  have e0 := Real.exp_pos w
  have r2 : r^2=p := Real.sq_sqrt hp.le
  have b : p/dilation p w=r*Real.exp (-w) := by
    dsimp [dilation,r]; rw [Real.exp_neg]
    field_simp [r0.ne',e0.ne']; nlinarith [Real.sq_sqrt hp.le]
  dsimp only
  rw [b]
  have a : dilation p w=r*Real.exp w := rfl
  rw [a]
  have P : r*Real.exp w*(r*Real.exp (-w))=p := by
    rw [Real.exp_neg]; field_simp [e0.ne']; nlinarith
  have R : r*Real.exp w/(r*Real.exp (-w))=Real.exp (w+w) := by
    rw [Real.exp_neg,Real.exp_add]; field_simp [e0.ne',r0.ne']
  exact ⟨mul_pos r0 e0,mul_pos r0 (Real.exp_pos _),P,by rw [R,Real.log_exp]; ring,
    by rw [Real.sinh_eq]; ring⟩

theorem scaled_density {k : ℝ} (hk : 0<k) (s w : ℝ) (ell : D4→ℤ) (Y : ℝ) :
    let p := productAt k s
    let a := dilation p w
    height ell Y a (p/a)*e ((a-p/a)*s)=h ell Y p*((g w:ℂ)*e (2*(Real.sqrt p*s)*Real.sinh w)) := by
  let p := productAt k s
  have hp : 0<p := by dsimp [p,productAt]; positivity
  obtain ⟨ha,hb,hab,hw,hs⟩ := coordinate_identity hp w
  dsimp only [height]; rw [if_pos ⟨ha,hb⟩,hab,hw,hs]
  rw [show 2*Real.sqrt p*Real.sinh w*s=2*(Real.sqrt p*s)*Real.sinh w by ring]
  ring

end
end ImbalancedChen.Part3.OriginalAbelGaussian
