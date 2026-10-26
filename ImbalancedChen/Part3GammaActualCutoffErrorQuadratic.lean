import ImbalancedChen.Part3GammaActualClosedFormCutoffConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual quotient cutoff-gradient coefficient gives a bounded physical
L2 multiplier. Its quadratic pairing is exactly the genuine weighted IMS
error integral, with integrability proved for every original quotient L2
vector. The actual completed form's real mixed pairing is also identified
with the global carrier-gradient mixed pairing by genuine polarization.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffErrorQuadratic20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0CarrierGradientHilbertMap20261026b Gamma0WeightedCutoffDefectLimit20261026a
open Gamma0ModularFiniteCoverMeasure20261025a ActualModularCutoffEnergyBudget20261025a
open ActualModularCutoffGradient20261025a ActualCuspStripCutoff20261025a

theorem completedCarrierGradient_re_inner (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    (inner ℂ (completedCarrierGradient N d) (completedCarrierGradient N e)).re =
      (actualDirichletPair N d e).re := by
  have hdiag (x : EnergyCompletion N) : ‖completedCarrierGradient N x‖^2 =
      ‖x‖^2-‖physicalProjection N x‖^2 := by
    rw [completedCarrierGradient_norm_sq,actualDirichletPair,Complex.sub_re,
      ← InnerProductSpace.norm_sq_eq_re_inner,← InnerProductSpace.norm_sq_eq_re_inner]
  have hd := hdiag d
  have he := hdiag e
  have hde := hdiag (d+e)
  simp only [map_add] at hde
  have hG := norm_add_sq (𝕜 := ℂ) (completedCarrierGradient N d) (completedCarrierGradient N e)
  have hE := norm_add_sq (𝕜 := ℂ) d e
  have hP := norm_add_sq (𝕜 := ℂ) (physicalProjection N d) (physicalProjection N e)
  simp only [actualDirichletPair,Complex.sub_re]
  nlinarith

theorem quotientCutoffEnergy_measurable (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    Measurable (quotientCutoffEnergy N Y hY) :=
  (quotientModularEnergy_measurable Y hY).comp (forgetLevel_measurable N)

theorem quotientCutoffEnergy_uniform_bound (N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (q : Gamma0OrbitSpace N) :
    quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q ≤ cutoffEnergyConstant :=
  Quotient.inductionOn q (fun z => cutoffEnergyH_uniform Y hY z)

private theorem energyCoefficient_norm_le (N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (q : Gamma0OrbitSpace N) :
    ‖(quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q : ℂ)‖ ≤ cutoffEnergyConstant := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (quotientCutoffEnergy_nonneg N Y _ q)]
  exact quotientCutoffEnergy_uniform_bound N Y hY q

private theorem cutoffErrorProduct_memLp (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : MemLp
      (fun q => (quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q : ℂ)*f q)
      2 (carrierPushforward N) := by
  apply (Lp.memLp f).of_le_mul
    ((Complex.measurable_ofReal.comp (quotientCutoffEnergy_measurable N Y
      (lt_trans (by norm_num) hY))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun q => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (energyCoefficient_norm_le N Y hY q) (norm_nonneg _))

def cutoffErrorProduct (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : QuotientL2 N :=
  (cutoffErrorProduct_memLp N Y hY f).toLp
    (fun q => (quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q : ℂ)*f q)

theorem cutoffErrorProduct_coe_ae (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : cutoffErrorProduct N Y hY f =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q : ℂ)*f q) :=
  (cutoffErrorProduct_memLp N Y hY f).coeFn_toLp

def cutoffErrorProductLinear (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    QuotientL2 N →ₗ[ℂ] QuotientL2 N where
  toFun := cutoffErrorProduct N Y hY
  map_add' f g := by
    apply Lp.ext
    filter_upwards [cutoffErrorProduct_coe_ae N Y hY (f+g),Lp.coeFn_add f g,
      Lp.coeFn_add (cutoffErrorProduct N Y hY f) (cutoffErrorProduct N Y hY g),
      cutoffErrorProduct_coe_ae N Y hY f,cutoffErrorProduct_coe_ae N Y hY g]
      with q hleft hin hright hf hg
    rw [hleft,hright,hf,hg,hin]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [cutoffErrorProduct_coe_ae N Y hY (c • f),Lp.coeFn_smul c f,
      Lp.coeFn_smul c (cutoffErrorProduct N Y hY f),cutoffErrorProduct_coe_ae N Y hY f]
      with q hleft hin hright hf
    rw [hleft,hright,hf,hin]
    simp only [smul_eq_mul]
    ring

theorem cutoffErrorProduct_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : ‖cutoffErrorProduct N Y hY f‖ ≤ cutoffEnergyConstant*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cutoffErrorProduct_coe_ae N Y hY f] with q hq
  rw [hq,norm_mul]
  exact mul_le_mul_of_nonneg_right (energyCoefficient_norm_le N Y hY q) (norm_nonneg _)

def actualCutoffErrorMultiplier (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  (cutoffErrorProductLinear N Y hY).mkContinuous cutoffEnergyConstant
    (cutoffErrorProduct_norm_le N Y hY)

private theorem star_mul_self_complex (z : ℂ) : star z*z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]

theorem actualCutoffError_quadratic_integrable
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    Integrable (fun q => quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2)
      (carrierPushforward N) := by
  apply (L2.integrable_inner (𝕜 := ℂ) f (actualCutoffErrorMultiplier N Y hY f)).re.congr
  filter_upwards [cutoffErrorProduct_coe_ae N Y hY f] with q hq
  rw [hq]
  simp only [RCLike.inner_apply']
  have halg : star (f q)*((quotientCutoffEnergy N Y _ q : ℂ)*f q) =
      (quotientCutoffEnergy N Y _ q : ℂ)*(star (f q)*f q) := by ring
  rw [halg,star_mul_self_complex]
  simp

theorem actualCutoffError_quadratic_integral
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    (inner ℂ f (actualCutoffErrorMultiplier N Y hY f)).re =
      ∫ q, quotientCutoffEnergy N Y (lt_trans (by norm_num) hY) q * ‖f q‖^2
        ∂carrierPushforward N := by
  rw [L2.inner_def,← integral_re (L2.integrable_inner (𝕜 := ℂ) f (actualCutoffErrorMultiplier N Y hY f))]
  apply integral_congr_ae
  filter_upwards [cutoffErrorProduct_coe_ae N Y hY f] with q hq
  rw [hq]
  simp only [RCLike.inner_apply']
  have halg : star (f q)*((quotientCutoffEnergy N Y _ q : ℂ)*f q) =
      (quotientCutoffEnergy N Y _ q : ℂ)*(star (f q)*f q) := by ring
  rw [halg,star_mul_self_complex]
  simp

end
end ImbalancedChen.Part3.GammaActualCutoffErrorQuadratic20261026b
