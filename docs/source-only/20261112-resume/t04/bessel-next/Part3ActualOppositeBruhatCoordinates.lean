import ImbalancedChen.Part3ActualOppositeKProduct
import ImbalancedChen.Part3ActualMarkedBruhatTest
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The exact two real changes of variables in the signed Bruhat
overlap, both for the complex integral and its nonnegative mass. -/
namespace ImbalancedChen.Part3.ActualOppositeBruhatCoordinates20261112

noncomputable section
open Set Filter MeasureTheory Complex
open ActualOppositeKProduct20261112 ActualMarkedBruhatTest20261112
open CompactCuspGeometricFubini20261025a ComplexOrderKBridgeSourceOnly
open P3Period64NativeReconstructionSourceOnly (e)

abbrev posMeasure : Measure ℝ := volume.restrict (Ioi 0)

def raw (ν : ℂ) (ψ φ : ℝ → ℂ) (a x q : ℝ) : ℂ :=
  ((4*Real.pi/q^2 : ℝ) : ℂ)*complexOrderK (2*ν) q*
    star (orbitTestKernel (-1) ψ φ ((q/(4*Real.pi))^2) x a)

def amp (a : ℝ) : ℝ := (a⁻¹)^2*Real.sqrt a

def transformed (ν : ℂ) (ψ φ : ℝ → ℂ) (a v b : ℝ) : ℂ :=
  ((amp a*amp b/2 : ℝ) : ℂ)*(ψ a*star (φ b))*
    (oscillation (2*Real.pi*a-2*Real.pi*b) v*
      complexOrderK (2*ν) (4*Real.pi*Real.sqrt (a*b)*Real.cosh v))

private def rate (a v : ℝ) := 4*Real.pi*Real.sqrt a*Real.cosh v
private def dx (a v : ℝ) := a*Real.cosh v
private def dq (a v b : ℝ) := rate a v/(2*Real.sqrt b)

private theorem rate_pos {a : ℝ} (ha : 0<a) (v : ℝ) : 0<rate a v := by
  unfold rate
  positivity

theorem k_measurable (ν : ℂ) : Measurable (complexOrderK ν) := by
  have C : Continuous (Function.uncurry (complexOrderIntegrand ν)) := by
    unfold Function.uncurry complexOrderIntegrand
    fun_prop
  exact (C.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioi 0))).measurable

private theorem phase_pair (a b v : ℝ) :
    star (e (-(a*Real.sinh v))*e (b*Real.sinh v))=oscillation (2*Real.pi*a-2*Real.pi*b) v := by
  simp only [e,oscillation,← Complex.exp_add,Complex.star_def,← Complex.exp_conj,
    map_add,map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_sub,Complex.ofReal_ofNat]
  congr 1
  ring

private theorem chart_value (ν : ℂ) (ψ φ : ℝ → ℂ) {a b : ℝ} (ha : 0<a) (hb : 0<b) (v : ℝ) :
    dx a v • (dq a v b • raw ν ψ φ a (a*Real.sinh v) (rate a v*Real.sqrt b)) =
      transformed ν ψ φ a v b := by
  let A := Real.sqrt a
  let B := Real.sqrt b
  let ch := Real.cosh v
  let sh := Real.sinh v
  have a2 : A^2=a := Real.sq_sqrt ha.le
  have b2 : B^2=b := Real.sq_sqrt hb.le
  have hp : Real.pi≠0 := Real.pi_ne_zero
  have hA : A≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hB : B≠0 := (Real.sqrt_pos.mpr hb).ne'
  have hch : ch≠0 := (Real.cosh_pos v).ne'
  have d : (a*sh)^2+a^2=a^2*ch^2 := by
    dsimp [sh,ch]
    rw [Real.cosh_sq]
    ring
  have k : ((rate a v*Real.sqrt b)/(4*Real.pi))^2=a*b*ch^2 := by
    change ((4*Real.pi*A*ch*B)/(4*Real.pi))^2=_
    rw [show 4*Real.pi*A*ch*B/(4*Real.pi)=A*B*ch by field_simp [hp] <;> ring]
    rw [mul_pow,mul_pow,a2,b2]
  have kx : (a*b*ch^2)*(a*sh)/((a*sh)^2+a^2)=b*sh := by
    rw [d]
    field_simp [ha.ne',hch] <;> ring
  have ky : (a*b*ch^2)*a/((a*sh)^2+a^2)=b := by
    rw [d]
    field_simp [ha.ne',hch] <;> ring
  have Q : rate a v*Real.sqrt b = 4*Real.pi*Real.sqrt (a*b)*ch := by
    rw [Real.sqrt_mul ha.le]
    dsimp [rate,ch]
    ring
  have coeff : dx a v*dq a v b*(4*Real.pi/(rate a v*Real.sqrt b)^2)*(a⁻¹)^2=amp a*amp b/2 := by
    change a*ch*((4*Real.pi*A*ch)/(2*B))*(4*Real.pi/(4*Real.pi*A*ch*B)^2)*(a⁻¹)^2 =
      ((a⁻¹)^2*A)*((b⁻¹)^2*B)/2
    rw [← a2,← b2]
    field_simp [hA,hB,hp,hch] <;> ring
  have P := phase_pair a b v
  change star (e (-(a*sh))*e (b*sh))=_ at P
  rw [star_mul'] at P
  simp only [raw,transformed,orbitTestKernel,Int.cast_neg,Int.cast_one,neg_neg,one_mul,k,kx,ky,
    radialWeight,star_mul',star_star,Complex.real_smul]
  have j := congrArg (fun z : ℝ => (z : ℂ)) coeff
  push_cast at j
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_ofNat] at P ⊢
  rw [← Q,← P]
  linear_combination j*(complexOrderK (2*ν) (rate a v*Real.sqrt b)*ψ a*conj (φ b)*
    conj (e (-(a*sh)))*conj (e (b*sh)))

private theorem x_range {a : ℝ} (ha : 0<a) : (fun v : ℝ => a*Real.sinh v) '' univ=univ := by
  rw [image_univ]
  apply Function.Surjective.range_eq
  intro x
  obtain ⟨v,hv⟩ := Real.sinh_surjective (x/a)
  exact ⟨v,by rw [hv]; field_simp [ha.ne']⟩

private theorem q_range {a : ℝ} (ha : 0<a) (v : ℝ) :
    (fun b : ℝ => rate a v*Real.sqrt b) '' Ioi 0=Ioi 0 := by
  ext q
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact mul_pos (rate_pos ha v) (Real.sqrt_pos.mpr hb)
  · intro hq
    have r := rate_pos ha v
    refine ⟨(q/rate a v)^2,sq_pos_of_pos (div_pos hq r),?_⟩
    rw [Real.sqrt_sq (div_nonneg hq.le r.le)]
    field_simp [r.ne']

private theorem derivative_x {a : ℝ} (v : ℝ) : HasDerivAt (fun w : ℝ => a*Real.sinh w) (dx a v) v :=
  (Real.hasDerivAt_sinh v).const_mul a

private theorem derivative_q (a v : ℝ) {b : ℝ} (hb : 0<b) :
    HasDerivAt (fun w : ℝ => rate a v*Real.sqrt w) (dq a v b) b := by
  simpa only [dq,div_eq_mul_inv,one_mul] using (Real.hasDerivAt_sqrt hb.ne').const_mul (rate a v)

private theorem inject_q {a : ℝ} (ha : 0<a) (v : ℝ) : InjOn (fun b : ℝ => rate a v*Real.sqrt b) (Ioi 0) := by
  intro b hb c hc eqn
  exact (Real.sqrt_inj hb.le hc.le).mp (mul_left_cancel₀ (rate_pos ha v).ne' eqn)

private theorem inject_x {a : ℝ} (ha : 0<a) : InjOn (fun v : ℝ => a*Real.sinh v) univ :=
  fun _ _ _ _ h => Real.sinh_injective (mul_left_cancel₀ ha.ne' h)

theorem change_integral (ν : ℂ) (ψ φ : ℝ → ℂ) {a : ℝ} (ha : 0<a) :
    (∫ x : ℝ,∫ q,raw ν ψ φ a x q ∂posMeasure) =
      ∫ v : ℝ,∫ b,transformed ν ψ φ a v b ∂posMeasure := by
  let F := raw ν ψ φ a
  have X := integral_image_eq_integral_abs_deriv_smul measurableSet_univ
    (fun v _ => (derivative_x (a := a) v).hasDerivWithinAt) (inject_x ha)
    (fun x => ∫ q,F x q ∂posMeasure)
  rw [x_range ha,integral_univ,integral_univ] at X
  refine X.trans (integral_congr_ae (ae_of_all _ (fun v => ?_)))
  have B := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun b hb => (derivative_q a v hb).hasDerivWithinAt) (inject_q ha v) (F (a*Real.sinh v))
  rw [q_range ha v] at B
  rw [B,abs_of_pos (mul_pos ha (Real.cosh_pos v)),← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro b hb
  rw [abs_of_pos (div_pos (rate_pos ha v) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hb)))]
  exact chart_value ν ψ φ ha hb v

theorem change_mass (ν : ℂ) (ψ φ : ℝ → ℂ) {a : ℝ} (ha : 0<a) :
    (∫⁻ x : ℝ,∫⁻ q,‖raw ν ψ φ a x q‖ₑ ∂posMeasure) =
      ∫⁻ v : ℝ,∫⁻ b,‖transformed ν ψ φ a v b‖ₑ ∂posMeasure := by
  let F := fun x q => ‖raw ν ψ φ a x q‖ₑ
  have X := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_univ
    (fun v _ => (derivative_x (a := a) v).hasDerivWithinAt) (inject_x ha)
    (fun x => ∫⁻ q,F x q ∂posMeasure)
  rw [x_range ha,setLIntegral_univ,setLIntegral_univ] at X
  refine X.trans (lintegral_congr (fun v => ?_))
  have B := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun b hb => (derivative_q a v hb).hasDerivWithinAt) (inject_q ha v) (F (a*Real.sinh v))
  rw [q_range ha v] at B
  have xv : 0<dx a v := mul_pos ha (Real.cosh_pos v)
  rw [B,abs_of_pos xv,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with b hb
  have qv : 0<dq a v b := div_pos (rate_pos ha v) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hb))
  rw [← chart_value ν ψ φ ha hb v,enorm_smul,enorm_smul,Real.enorm_eq_ofReal xv.le,Real.enorm_eq_ofReal qv.le,abs_of_pos qv]

end
end ImbalancedChen.Part3.ActualOppositeBruhatCoordinates20261112
