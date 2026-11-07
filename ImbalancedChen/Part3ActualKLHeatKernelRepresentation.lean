import ImbalancedChen.Part3ActualKLHeatKernelAbsolute
import ImbalancedChen.Part3ActualKLIntegrableSpectralInverse

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
The positive-time literal raw-KL kernel is an actual continuous representative
of the independently constructed radial heat evolution of each smooth compact
input. Absolute convergence is proved first, then the genuine L1-intersect-L2
inverse theorem is consumed. This is not a formal definition of heat by kernel.
-/
namespace ImbalancedChen.Part3.ActualKLHeatKernelRepresentation20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactTestWeightedL220261025a
open ActualKLHeatTransport20261026a ActualKLHeatKernelAbsolute20261026a
open ActualKLIntegrableSpectralInverse20261026a

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

/-- Uniform-in-order bound for the literal transform of a compact input. -/
theorem compact_transform_norm_le (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (τ : ℝ) :
    ‖actualKtransform f τ‖ ≤ ∫ r, ‖f r‖ * Kzero r := by
  apply norm_integral_le_of_norm_le
    ((hf.norm.mul Kzero_continuous).integrable_of_hasCompactSupport hc.norm.mul_right)
  exact Eventually.of_forall fun r => by
    change ‖f r * K τ r‖ ≤ ‖f r‖ * Kzero r
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (K_norm_le τ r) (norm_nonneg _)

def heatAmplitude (t : ℝ) (F : RadialTest) (τ : ℝ) : ℂ :=
  (Real.exp (-t*τ^2) : ℂ) * actualKtransform F.function τ

/-- Positive time makes the literal spectral amplitude L1 for raw mu.
This is the extra convergence needed for an honest scalar inverse integral. -/
theorem heatAmplitude_integrable {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    Integrable (heatAmplitude t F) tauMeasure := by
  apply ((gaussian_integrable ht).mul_const (∫ r, ‖F.function r‖*Kzero r)).mono'
  · exact ((by fun_prop : AEStronglyMeasurable
      (fun τ : ℝ => (Real.exp (-t*τ^2) : ℂ)) tauMeasure).mul
      (actualKtransform_stronglyMeasurable F).aestronglyMeasurable)
  · exact Eventually.of_forall fun τ => by
      simp only [heatAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (compact_transform_norm_le F.function F.smooth.continuous F.compact τ)
        (Real.exp_pos _).le

/-- L2 membership follows from the independently proved actual heat
intertwining, not from a guessed inverse formula. -/
theorem heatAmplitude_memLp {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    MemLp (heatAmplitude t F) 2 tauMeasure :=
  (Lp.memLp (actualKLUnitary (actualRadialHeat t (radialCoreL2 F)))).congr
    (actualKL_heat_on_test_ae t ht.le F)

theorem heatAmplitude_toLp {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    (heatAmplitude_memLp ht F).toLp (heatAmplitude t F) =
      actualKLUnitary (actualRadialHeat t (radialCoreL2 F)) := by
  apply Lp.ext
  exact (heatAmplitude_memLp ht F).coeFn_toLp.trans
    (actualKL_heat_on_test_ae t ht.le F).symm

/-- The literal kernel integral is everywhere absolutely convergent. -/
theorem heatKernel_input_integrable {t : ℝ} (ht : 0 < t)
    (F : RadialTest) (r : ℝ) :
    Integrable (fun s => heatKernel t r s * F.function s) := by
  have hc : Continuous (fun s =>
      gaussianMass t * Kzero r * (Kzero s*‖F.function s‖)) := by
    exact continuous_const.mul (Kzero_continuous.mul F.smooth.continuous.norm)
  have hmajor := hc.integrable_of_hasCompactSupport
    ((F.compact.norm.mul_left).mul_left)
  apply hmajor.mono'
  · exact (((heatKernel_measurable t).comp
      (measurable_const.prodMk measurable_id)).mul F.smooth.continuous.measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun s => by
      rw [norm_mul]
      calc
        ‖heatKernel t r s‖ * ‖F.function s‖ ≤
            (gaussianMass t * (Kzero r*Kzero s))*‖F.function s‖ :=
          mul_le_mul_of_nonneg_right (heatKernel_norm_le ht r s) (norm_nonneg _)
        _ = _ := by ring

def heatKernelApply (t : ℝ) (F : RadialTest) (r : ℝ) : ℂ :=
  ∫ s, heatKernel t r s * F.function s

theorem heatKernelApply_eq_spectralInverse {t : ℝ} (ht : 0 < t)
    (F : RadialTest) :
    heatKernelApply t F = spectralL1Inverse (heatAmplitude t F) := by
  funext r
  rw [heatKernelApply, compact_input_fubini ht F.function F.smooth.continuous F.compact r]
  apply integral_congr_ae
  exact Eventually.of_forall fun τ => by
    dsimp [spectralL1Inverse, heatAmplitude, K, inverseKKernel]
    ring

/-- Main actual representative theorem. Heat was already defined through the
actual native radial resolvent. The literal absolutely convergent raw kernel
now represents that same operator, with no inverse/heat hypothesis. -/
theorem heatKernelApply_eq_actualHeat_ae {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    heatKernelApply t F =ᵐ[(volume : Measure ℝ)]
      (actualRadialHeat t (radialCoreL2 F) : RadialL2) := by
  rw [heatKernelApply_eq_spectralInverse ht F]
  have h := spectralL1Inverse_eq_unitary_inverse_ae
    (heatAmplitude_integrable ht F) (heatAmplitude_memLp ht F)
  rw [heatAmplitude_toLp ht F, actualKLUnitary.symm_apply_apply] at h
  exact h

/-- Global physical L2 is a conclusion, even though no single K_(i*tau)
radial function was placed in physical L2. -/
theorem heatKernelApply_memLp {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    MemLp (heatKernelApply t F) 2 (volume : Measure ℝ) :=
  (Lp.memLp (actualRadialHeat t (radialCoreL2 F))).congr
    (heatKernelApply_eq_actualHeat_ae ht F).symm

theorem heatKernelApply_continuous {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    Continuous (heatKernelApply t F) := by
  rw [heatKernelApply_eq_spectralInverse ht F]
  exact spectralL1Inverse_continuous (heatAmplitude_integrable ht F)

/-- Equality of genuine physical Hilbert-space vectors. -/
theorem heatKernelApply_toLp {t : ℝ} (ht : 0 < t) (F : RadialTest) :
    (heatKernelApply_memLp ht F).toLp (heatKernelApply t F) =
      actualRadialHeat t (radialCoreL2 F) := by
  apply Lp.ext
  exact (heatKernelApply_memLp ht F).coeFn_toLp.trans
    (heatKernelApply_eq_actualHeat_ae ht F)

/-- The kernel classes recover the original input strongly in L2.
The harmless t<=0 branch only totalizes this right-limit expression. -/
theorem heatKernelApply_initial (F : RadialTest) :
    Tendsto (fun t : ℝ => if ht : 0 < t then
        (heatKernelApply_memLp ht F).toLp (heatKernelApply t F) else radialCoreL2 F)
      (𝓝[>] 0) (𝓝 (radialCoreL2 F)) := by
  apply (actualRadialHeat_initial (radialCoreL2 F)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [dif_pos ht, heatKernelApply_toLp ht F]

end
end ImbalancedChen.Part3.ActualKLHeatKernelRepresentation20261026a
