import ImbalancedChen.Part3WeightedHeightLogMeasure
import ImbalancedChen.Part3RadialSmoothCoreDerivativeClosure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Native weighted-height L2 is unitarily equivalent to radial L2(dr)

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

For every a>0 this is an ACTUAL linear isometry equivalence between the
existing subtype heightMeasure=dy/y^2 and the original radial L2(dr):

 U_a f(r) = sqrt(a)*exp(-r/2)*f(exp(r)/a),
 V_a F(y) = sqrt(y)*F(log(a*y)).

Membership is proved for arbitrary Lp quotient vectors by the full
nonnegative-integral Jacobian and both nonsingular coordinate maps.
Pointwise inverse scalar identities then prove surjectivity and the
almost-everywhere inverse formula. No compact smooth approximation,
form-domain equality, formal inverse or target norm identity is assumed.
No held cusp-constant-mode or defective single-mode extension is imported.
-/

namespace ImbalancedChen.Part3.WeightedHeightNativeUnitary20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
open CuspCylinderMeasure20261024z WeightedHeightLogMeasure20261026a
open RadialSchrodingerL2Form20261025a
attribute [local instance] Measure.Subtype.measureSpace

abbrev HeightL2 := Lp ℂ 2 heightMeasure

def heightForwardAmplitude (a r : ℝ) : ℝ := Real.sqrt a * Real.exp (-r / 2)

theorem heightForwardAmplitude_pos {a : ℝ} (ha : 0 < a) (r : ℝ) :
    0 < heightForwardAmplitude a r := mul_pos (Real.sqrt_pos.mpr ha) (Real.exp_pos _)

theorem heightForwardAmplitude_sq {a : ℝ} (ha : 0 < a) (r : ℝ) :
    heightForwardAmplitude a r ^ 2 = radialHeightDensity a r := by
  unfold heightForwardAmplitude radialHeightDensity
  rw [mul_pow, Real.sq_sqrt ha.le]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem heightForwardAmplitude_inverse_coefficient (a : ℝ) (ha : 0 < a) (r : ℝ) :
    heightForwardAmplitude a r * Real.sqrt (scaledHeightEquiv a ha r : ℝ) = 1 := by
  have hy : 0 < (scaledHeightEquiv a ha r : ℝ) := (scaledHeightEquiv a ha r).property
  have hsq : (heightForwardAmplitude a r * Real.sqrt (scaledHeightEquiv a ha r : ℝ)) ^ 2 = 1 := by
    rw [mul_pow, heightForwardAmplitude_sq ha, Real.sq_sqrt hy.le]
    unfold radialHeightDensity
    rw [scaledHeightEquiv_coe, Real.exp_neg]
    field_simp [ha.ne', (Real.exp_pos r).ne']
    <;> ring
  have hn : 0 ≤ heightForwardAmplitude a r * Real.sqrt (scaledHeightEquiv a ha r : ℝ) :=
    mul_nonneg (heightForwardAmplitude_pos ha r).le (Real.sqrt_nonneg _)
  exact (sq_eq_sq₀ hn zero_le_one).mp (by simpa only [one_pow] using hsq)

def heightToRadialFunction (a : ℝ) (ha : 0 < a) (f : PositiveHeight → ℂ) (r : ℝ) : ℂ :=
  (heightForwardAmplitude a r : ℂ) * f (scaledHeightEquiv a ha r)

def radialToHeightFunction (a : ℝ) (ha : 0 < a) (F : ℝ → ℂ) (y : PositiveHeight) : ℂ :=
  (Real.sqrt (y : ℝ) : ℂ) * F ((scaledHeightEquiv a ha).symm y)

theorem heightToRadialFunction_radialToHeightFunction
    (a : ℝ) (ha : 0 < a) (F : ℝ → ℂ) :
    heightToRadialFunction a ha (radialToHeightFunction a ha F) = F := by
  funext r
  unfold heightToRadialFunction radialToHeightFunction
  rw [(scaledHeightEquiv a ha).symm_apply_apply, ← mul_assoc,
    ← Complex.ofReal_mul, heightForwardAmplitude_inverse_coefficient]
  simp

theorem radialToHeightFunction_heightToRadialFunction
    (a : ℝ) (ha : 0 < a) (f : PositiveHeight → ℂ) :
    radialToHeightFunction a ha (heightToRadialFunction a ha f) = f := by
  funext y
  have hcoef := heightForwardAmplitude_inverse_coefficient a ha ((scaledHeightEquiv a ha).symm y)
  rw [(scaledHeightEquiv a ha).apply_symm_apply] at hcoef
  unfold heightToRadialFunction radialToHeightFunction
  rw [(scaledHeightEquiv a ha).apply_symm_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (Real.sqrt (y : ℝ)), hcoef]
  simp

/-- All-function nonnegative energy identity, before selecting any Lp
representative. It remains valid without integrability assumptions. -/
theorem heightToRadialFunction_lintegral_sq (a : ℝ) (ha : 0 < a) (f : PositiveHeight → ℂ) :
    (∫⁻ r : ℝ, ENNReal.ofReal (‖heightToRadialFunction a ha f r‖ ^ 2)) =
      ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂heightMeasure := by
  rw [height_lintegral_scaled_exp a ha]
  apply lintegral_congr
  intro r
  unfold heightToRadialFunction
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    heightForwardAmplitude_sq ha, ENNReal.ofReal_mul (radialHeightDensity_pos ha r).le]

private theorem memLp_of_lintegral_sq_lt_top {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {f : X → ℂ} (hm : AEStronglyMeasurable f mu)
    (hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂mu) < ⊤) : MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg ‖f x‖))).mpr hfin

private theorem memLp_sq_lintegral_lt_top {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {f : X → ℂ} (hf : MemLp f 2 mu) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂mu) < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg ‖f x‖))).mp
    hi.hasFiniteIntegral

theorem heightToRadialFunction_memLp (a : ℝ) (ha : 0 < a) (f : HeightL2) :
    MemLp (heightToRadialFunction a ha f) 2 volume := by
  have hc : Continuous (fun r : ℝ => (heightForwardAmplitude a r : ℂ)) := by
    unfold heightForwardAmplitude
    fun_prop
  have hm : AEStronglyMeasurable (heightToRadialFunction a ha f) volume :=
    hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      (scaledHeightEquiv_quasiMeasurePreserving a ha))
  apply memLp_of_lintegral_sq_lt_top hm
  rw [heightToRadialFunction_lintegral_sq]
  exact memLp_sq_lintegral_lt_top (Lp.memLp f)

theorem radialToHeightFunction_memLp (a : ℝ) (ha : 0 < a) (F : RadialL2) :
    MemLp (radialToHeightFunction a ha F) 2 heightMeasure := by
  have hc : Continuous (fun y : PositiveHeight => (Real.sqrt (y : ℝ) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (radialToHeightFunction a ha F) heightMeasure :=
    hc.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable F).comp_quasiMeasurePreserving
      (scaledHeightEquiv_symm_quasiMeasurePreserving a ha))
  apply memLp_of_lintegral_sq_lt_top hm
  rw [← heightToRadialFunction_lintegral_sq a ha,
    heightToRadialFunction_radialToHeightFunction]
  exact memLp_sq_lintegral_lt_top (Lp.memLp F)

def heightToRadialLp (a : ℝ) (ha : 0 < a) (f : HeightL2) : RadialL2 :=
  (heightToRadialFunction_memLp a ha f).toLp (heightToRadialFunction a ha f)

def radialToHeightLp (a : ℝ) (ha : 0 < a) (F : RadialL2) : HeightL2 :=
  (radialToHeightFunction_memLp a ha F).toLp (radialToHeightFunction a ha F)

theorem heightToRadialLp_ae (a : ℝ) (ha : 0 < a) (f : HeightL2) :
    heightToRadialLp a ha f =ᵐ[(volume : Measure ℝ)] heightToRadialFunction a ha f :=
  (heightToRadialFunction_memLp a ha f).coeFn_toLp

theorem radialToHeightLp_ae (a : ℝ) (ha : 0 < a) (F : RadialL2) :
    radialToHeightLp a ha F =ᵐ[heightMeasure] radialToHeightFunction a ha F :=
  (radialToHeightFunction_memLp a ha F).coeFn_toLp

private theorem scalarL2_norm_sq_integral {X : Type*} [MeasurableSpace X]
    {mu : Measure X} (u : Lp ℂ 2 mu) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  have hL2 : inner ℂ u u = ∫ x, inner ℂ (u x) (u x) ∂mu := L2.inner_def _ _
  simp_rw [inner_self_eq_norm_sq_to_K] at hL2
  rw [integral_ofReal] at hL2
  exact Complex.ofReal_injective hL2

theorem heightToRadialLp_norm (a : ℝ) (ha : 0 < a) (f : HeightL2) :
    ‖heightToRadialLp a ha f‖ = ‖f‖ := by
  have hu := (memLp_two_iff_integrable_sq_norm
    (heightToRadialFunction_memLp a ha f).aestronglyMeasurable).mp
      (heightToRadialFunction_memLp a ha f)
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have henergy := heightToRadialFunction_lintegral_sq a ha (f : PositiveHeight → ℂ)
  rw [← ofReal_integral_eq_lintegral_ofReal hu (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall (fun _ => sq_nonneg _))] at henergy
  have hreal := congrArg ENNReal.toReal henergy
  simp only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))] at hreal
  have hsq : ‖heightToRadialLp a ha f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [scalarL2_norm_sq_integral, scalarL2_norm_sq_integral]
    calc
      _ = ∫ r : ℝ, ‖heightToRadialFunction a ha f r‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [heightToRadialLp_ae a ha f] with r hr
        rw [hr]
      _ = _ := hreal
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def heightToRadialLinear (a : ℝ) (ha : 0 < a) : HeightL2 →ₗ[ℂ] RadialL2 where
  toFun := heightToRadialLp a ha
  map_add' f g := by
    apply Lp.ext
    have hin := (scaledHeightEquiv_quasiMeasurePreserving a ha).ae (Lp.coeFn_add f g)
    filter_upwards [heightToRadialLp_ae a ha (f + g), hin,
      Lp.coeFn_add (heightToRadialLp a ha f) (heightToRadialLp a ha g),
      heightToRadialLp_ae a ha f, heightToRadialLp_ae a ha g]
        with r hout hadd hsum hf hg
    rw [hout, hsum, hf, hg]
    unfold heightToRadialFunction
    rw [hadd, mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hin := (scaledHeightEquiv_quasiMeasurePreserving a ha).ae (Lp.coeFn_smul c f)
    filter_upwards [heightToRadialLp_ae a ha (c • f), hin,
      Lp.coeFn_smul c (heightToRadialLp a ha f), heightToRadialLp_ae a ha f]
        with r hout hsmul hcoe hf
    rw [hout, hcoe, hf]
    unfold heightToRadialFunction
    rw [hsmul]
    simp only [smul_eq_mul]
    ring

def heightToRadialIsometry (a : ℝ) (ha : 0 < a) : HeightL2 →ₗᵢ[ℂ] RadialL2 :=
  { heightToRadialLinear a ha with norm_map' := heightToRadialLp_norm a ha }

theorem heightToRadialLp_radialToHeightLp (a : ℝ) (ha : 0 < a) (F : RadialL2) :
    heightToRadialLp a ha (radialToHeightLp a ha F) = F := by
  apply Lp.ext
  have hV := (scaledHeightEquiv_quasiMeasurePreserving a ha).ae (radialToHeightLp_ae a ha F)
  filter_upwards [heightToRadialLp_ae a ha (radialToHeightLp a ha F), hV] with r hU hVr
  rw [hU]
  unfold heightToRadialFunction
  rw [hVr]
  exact congrFun (heightToRadialFunction_radialToHeightFunction a ha (F : ℝ → ℂ)) r

theorem heightToRadialIsometry_surjective (a : ℝ) (ha : 0 < a) :
    Function.Surjective (heightToRadialIsometry a ha) :=
  fun F => ⟨radialToHeightLp a ha F, heightToRadialLp_radialToHeightLp a ha F⟩

/-- The actual native subtype weighted-height unitary, for arbitrary Lp
vectors, with surjectivity proved by the explicit inverse representative. -/
def weightedHeightUnitary (a : ℝ) (ha : 0 < a) : HeightL2 ≃ₗᵢ[ℂ] RadialL2 :=
  LinearIsometryEquiv.ofSurjective (heightToRadialIsometry a ha)
    (heightToRadialIsometry_surjective a ha)

theorem weightedHeightUnitary_forward_ae (a : ℝ) (ha : 0 < a) (f : HeightL2) :
    weightedHeightUnitary a ha f =ᵐ[(volume : Measure ℝ)]
      (fun r => ((Real.sqrt a * Real.exp (-r / 2) : ℝ) : ℂ) *
        f ⟨Real.exp r / a, div_pos (Real.exp_pos r) ha⟩) :=
  heightToRadialLp_ae a ha f

theorem weightedHeightUnitary_inverse_eq_radialToHeightLp (a : ℝ) (ha : 0 < a) (F : RadialL2) :
    (weightedHeightUnitary a ha).symm F = radialToHeightLp a ha F := by
  apply (weightedHeightUnitary a ha).injective
  rw [(weightedHeightUnitary a ha).apply_symm_apply]
  exact (heightToRadialLp_radialToHeightLp a ha F).symm

theorem weightedHeightUnitary_inverse_ae (a : ℝ) (ha : 0 < a) (F : RadialL2) :
    (weightedHeightUnitary a ha).symm F =ᵐ[heightMeasure]
      (fun y : PositiveHeight => (Real.sqrt (y : ℝ) : ℂ) * F (Real.log (a * (y : ℝ)))) := by
  rw [weightedHeightUnitary_inverse_eq_radialToHeightLp]
  exact radialToHeightLp_ae a ha F

theorem weightedHeightUnitary_inverse_on_core_ae (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    (weightedHeightUnitary a ha).symm (radialCoreL2 T) =ᵐ[heightMeasure]
      (fun y : PositiveHeight => (Real.sqrt (y : ℝ) : ℂ) * T.function (Real.log (a * (y : ℝ)))) := by
  have hT := (scaledHeightEquiv_symm_quasiMeasurePreserving a ha).ae T.function_memLp.coeFn_toLp
  filter_upwards [weightedHeightUnitary_inverse_ae a ha (radialCoreL2 T), hT] with y hV hrep
  rw [hV, hrep]

end
end ImbalancedChen.Part3.WeightedHeightNativeUnitary20261026a
