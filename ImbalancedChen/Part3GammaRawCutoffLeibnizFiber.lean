import ImbalancedChen.Part3GammaRawWeightedFiberL2
import ImbalancedChen.Part3GammaActualCutoffCoreUniformEnergy
import ImbalancedChen.Part3GammaRawCarrierWeightedCutoffLimits

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal raw Leibniz fibre chi W+f grad(chi) belongs to the ORIGINAL
native carrier vector L2. The cutoff derivative is the existing actual
nativeWeightedGradient, with its proved cutoffEnergyH norm identity.
Neither f nor W is assumed to arise from the completed energy form. -/

namespace ImbalancedChen.Part3.GammaRawCutoffLeibnizFiber20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactCoreGradient20261025a Gamma0CarrierGradientHilbertMap20261026b
open GammaRawWeightedFiberL220261026b GammaCoreMultiplierGradientProduct20261026b
open GammaActualCutoffCoreUniformEnergy20261026b GammaActualCutoffNativeGradientBudget20261026b
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffGradient20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open Gamma0WeightedCutoffDefectLimit20261026a GammaRawCarrierWeightedCutoffLimits20261026b
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactGreenProductL120261025a
open GammaNativeMaassLeibniz20261026a ActualCuspStripCutoff20261025a
open MaassWeakOperatorCore20261024zz

theorem actualCarrierPullback_memLp (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    MemLp (fun z => f (orbitProjection N z)) 2 (carrierVolume N) := by
  have hf : MemLp f 2 ((carrierVolume N).map (orbitProjection N)) := f.memLp
  exact hf.comp_of_map (orbitProjection_measurable N).aemeasurable

theorem nativeCutoffGradient_continuous (Y : ℝ) (hY : 0<Y) :
    Continuous (nativeWeightedGradient (complexGlobalH Y)) := by
  have hs := extendGlobal_C2 Y hY
  have hs1 : ContDiffOn ℝ 1 (extendUpper (complexGlobalH Y)) positiveChart := hs.of_le (by norm_num)
  have hchart : Continuous (fun z : UpperHalfPlane => (z.re,z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have hx : Continuous (nativeDx (complexGlobalH Y)) :=
    (sliceDx_continuousOn_of_C1 _ hs1).comp_continuous hchart (fun z => z.im_pos)
  have hy : Continuous (nativeDy (complexGlobalH Y)) :=
    (sliceDy_continuousOn_of_C1 _ hs1).comp_continuous hchart (fun z => z.im_pos)
  apply PiLp.continuous_toLp.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hx
  · exact (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul hy

theorem complexGlobalH_measurable (Y : ℝ) (hY : 0<Y) : Measurable (complexGlobalH Y) := by
  have h := Complex.measurable_ofReal.comp
    ((quotientCutoff_measurable 1 Y hY).comp (orbitProjection_measurable 1))
  exact h

def cutoffMainFiber (Y : ℝ) (W : UpperHalfPlane → GradientFiber) (z : UpperHalfPlane) : GradientFiber :=
  complexGlobalH Y z • W z

def cutoffErrorFiber (N : ℕ) (f : QuotientL2 N) (Y : ℝ) (z : UpperHalfPlane) : GradientFiber :=
  f (orbitProjection N z) • nativeWeightedGradient (complexGlobalH Y) z

def rawLeibnizFiber (N : ℕ) (f : QuotientL2 N) (W : UpperHalfPlane → GradientFiber)
    (n : ℕ) : UpperHalfPlane → GradientFiber :=
  cutoffMainFiber (cutoffHeight n) W+cutoffErrorFiber N f (cutoffHeight n)

theorem cutoffMainFiber_memLp (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1<Y)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) :
    MemLp (cutoffMainFiber Y W) 2 (carrierVolume N) := by
  apply hW.of_le ((complexGlobalH_measurable Y (by linarith)).aestronglyMeasurable.smul
    hW.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    rw [cutoffMainFiber,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (actualCutoff_norm_le_one Y hY.le z)

theorem cutoffErrorFiber_norm_sq (N : ℕ) (f : QuotientL2 N) (Y : ℝ) (z : UpperHalfPlane) :
    ‖cutoffErrorFiber N f Y z‖^2=cutoffEnergyH Y z*‖f (orbitProjection N z)‖^2 := by
  rw [cutoffErrorFiber,norm_smul,mul_pow,nativeWeightedGradient_norm_sq,nativeEnergySq_actualCutoff]
  ring

theorem cutoffErrorFiber_memLp (N : ℕ) [NeZero N] (f : QuotientL2 N) (Y : ℝ) (hY : 1<Y) :
    MemLp (cutoffErrorFiber N f Y) 2 (carrierVolume N) := by
  have hf := actualCarrierPullback_memLp N f
  have hm : AEStronglyMeasurable (cutoffErrorFiber N f Y) (carrierVolume N) :=
    hf.aestronglyMeasurable.smul (nativeCutoffGradient_continuous Y (by linarith)).aestronglyMeasurable
  have hmass := hf.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have he : Integrable (fun z => cutoffEnergyH Y z*‖f (orbitProjection N z)‖^2) (carrierVolume N) := by
    apply (hmass.const_mul cutoffEnergyConstant).mono'
      ((cutoffEnergyH_continuous Y (by linarith)).aestronglyMeasurable.mul hmass.aestronglyMeasurable)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (cutoffEnergyH_nonneg Y z) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (cutoffEnergyH_uniform Y hY z) (sq_nonneg _)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  exact he.congr (Eventually.of_forall fun z => (cutoffErrorFiber_norm_sq N f Y z).symm)

theorem rawLeibnizFiber_memLp (N : ℕ) [NeZero N] (f : QuotientL2 N)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) (n : ℕ) :
    MemLp (rawLeibnizFiber N f W n) 2 (carrierVolume N) :=
  (cutoffMainFiber_memLp N (cutoffHeight n) (cutoffHeight_gt_one n) hW).add
    (cutoffErrorFiber_memLp N f (cutoffHeight n) (cutoffHeight_gt_one n))

def cutoffMainFiberL2 (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1<Y)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) : CarrierGradientL2 N :=
  (cutoffMainFiber_memLp N Y hY hW).toLp (cutoffMainFiber Y W)

def cutoffErrorFiberL2 (N : ℕ) [NeZero N] (f : QuotientL2 N) (Y : ℝ) (hY : 1<Y) : CarrierGradientL2 N :=
  (cutoffErrorFiber_memLp N f Y hY).toLp (cutoffErrorFiber N f Y)

def rawLeibnizFiberL2 (N : ℕ) [NeZero N] (f : QuotientL2 N)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) (n : ℕ) : CarrierGradientL2 N :=
  (rawLeibnizFiber_memLp N f hW n).toLp (rawLeibnizFiber N f W n)

theorem rawLeibnizFiberL2_eq_add (N : ℕ) [NeZero N] (f : QuotientL2 N)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) (n : ℕ) :
    rawLeibnizFiberL2 N f hW n=
      cutoffMainFiberL2 N (cutoffHeight n) (cutoffHeight_gt_one n) hW+
        cutoffErrorFiberL2 N f (cutoffHeight n) (cutoffHeight_gt_one n) :=
  MemLp.toLp_add _ _

end
end ImbalancedChen.Part3.GammaRawCutoffLeibnizFiber20261026b
