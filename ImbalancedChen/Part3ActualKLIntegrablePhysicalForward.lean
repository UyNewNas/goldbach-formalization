import ImbalancedChen.Part3ActualKLIntegrableSpectralInverse
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Actual forward K integral for nonsmooth integrable physical data

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

A physical L1 amplitude supported above a finite radial lower bound has a
continuous scalar K transform. If it is also L2, compact smooth spectral
tests, genuine scalar Fubini and the independently proved inverse integral
identify that transform with the actual KL unitary. No smoothness of the
physical amplitude, hTransform or extra norm assumption is introduced.
-/

namespace ImbalancedChen.Part3.ActualKLIntegrablePhysicalForward20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ActualKLIntegrableSpectralInverse20261026a
open ComplexOrderKBridgeSourceOnly ComplexOrderKHolomorphicSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ComplexOrderKUniformStripDecay20261025a
open ActualGreenBoundaryDiagonal20261025a

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

local instance : IsLocallyFiniteMeasure tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  exact IsLocallyFiniteMeasure.withDensity_ofReal (by unfold tauDensity; fun_prop)

def physicalL1Forward (f : ℝ → ℂ) (tau : ℝ) : ℂ :=
  ∫ r : ℝ, f r * inverseKKernel tau r

private theorem supported_kernel_bound {f : ℝ → ℂ} {a : ℝ}
    (ha : ∀ r : ℝ, r < a → f r = 0) (r tau : ℝ) :
    ‖f r * inverseKKernel tau r‖ ≤ stripDecayConstant 0 (Real.exp a) 1 * ‖f r‖ := by
  by_cases hr : r < a
  · simp only [ha r hr, zero_mul, norm_zero, mul_zero, le_refl]
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (inverseKKernel_uniform_bound a (le_of_not_gt hr) tau)
      (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem physicalL1Forward_integrable {f : ℝ → ℂ} (hf : Integrable f)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) (tau : ℝ) :
    Integrable (fun r : ℝ => f r * inverseKKernel tau r) := by
  apply (hf.norm.const_mul (stripDecayConstant 0 (Real.exp a) 1)).mono'
    (hf.aestronglyMeasurable.mul (inverseKKernel_radial_continuous tau).aestronglyMeasurable)
  exact Eventually.of_forall (fun r => supported_kernel_bound ha r tau)

theorem physicalL1Forward_continuous {f : ℝ → ℂ} (hf : Integrable f)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) : Continuous (physicalL1Forward f) := by
  apply continuous_iff_continuousAt.mpr
  intro tau0
  change Tendsto (fun tau => ∫ r : ℝ, f r * inverseKKernel tau r) (𝓝 tau0)
    (𝓝 (∫ r : ℝ, f r * inverseKKernel tau0 r))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r => stripDecayConstant 0 (Real.exp a) 1 * ‖f r‖)
  · exact Eventually.of_forall (fun tau => (physicalL1Forward_integrable hf ha tau).aestronglyMeasurable)
  · exact Eventually.of_forall (fun tau => Eventually.of_forall (fun r => supported_kernel_bound ha r tau))
  · exact hf.norm.const_mul _
  · exact Eventually.of_forall (fun r => by
      have hd := complexOrderK_hasDerivAt ((tau0 : ℂ) * Complex.I) (Real.exp r)
        (Real.exp_pos r) (by simp; norm_num)
      exact (continuousAt_const.mul (hd.continuousAt.comp (by fun_prop))).tendsto)

theorem physical_spectral_product_integrable {f h : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0)
    (hh : Integrable h tauMeasure) :
    Integrable (fun p : ℝ × ℝ =>
      (f p.1 * inverseKKernel p.2 p.1) * star (h p.2)) (volume.prod tauMeasure) := by
  have hmajor := (hf.norm.const_mul (stripDecayConstant 0 (Real.exp a) 1)).mul_prod hh.norm
  have hk : StronglyMeasurable (fun p : ℝ × ℝ => inverseKKernel p.2 p.1) :=
    inverseKKernel_joint_stronglyMeasurable.comp_measurable measurable_swap
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (f p.1 * inverseKKernel p.2 p.1) * star (h p.2)) (volume.prod tauMeasure) :=
    ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).mul
      hk.aestronglyMeasurable).mul
        (hh.aestronglyMeasurable.star.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  apply hmajor.mono' hm
  exact Eventually.of_forall (fun p => by
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (supported_kernel_bound ha p.1 p.2) (norm_nonneg _))

/-- Scalar Fubini with actual spectral test amplitudes. The physical
amplitude remains merely integrable, with no smooth core shortcut. -/
theorem physicalL1Forward_test_pairing {f h : ℝ → ℂ}
    (hf : Integrable f) {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0)
    (hh : Integrable h tauMeasure) :
    (∫ tau, physicalL1Forward f tau * star (h tau) ∂tauMeasure) =
      ∫ r : ℝ, f r * star (spectralL1Inverse h r) := by
  calc
    _ = ∫ tau, ∫ r : ℝ,
        (f r * inverseKKernel tau r) * star (h tau) ∂tauMeasure := by
      simp only [physicalL1Forward, integral_mul_const]
    _ = ∫ r : ℝ, ∫ tau,
        (f r * inverseKKernel tau r) * star (h tau) ∂tauMeasure :=
      (integral_integral_swap (physical_spectral_product_integrable hf ha hh)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by
        unfold spectralL1Inverse
        rw [← integral_conj, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun tau => by
          simp only [inverseKKernel, radialK, star_mul, complexOrderK_imaginary_star]
          ring))

private theorem physical_forward_unitary_pairing {f h : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0)
    (hh : Integrable h tauMeasure) (hh2 : MemLp h 2 tauMeasure) :
    (∫ tau, physicalL1Forward f tau * star (h tau) ∂tauMeasure) =
      ∫ tau, actualKLUnitary (hf2.toLp f) tau * star (h tau) ∂tauMeasure := by
  let V : RadialL2 := actualKLUnitary.symm (hh2.toLp h)
  have hunit := actualKLUnitary.inner_map_map V (hf2.toLp f)
  rw [actualKLUnitary.apply_symm_apply] at hunit
  calc
    _ = ∫ r : ℝ, f r * star (spectralL1Inverse h r) := physicalL1Forward_test_pairing hf ha hh
    _ = inner ℂ V (hf2.toLp f) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [spectralL1Inverse_eq_unitary_inverse_ae hh hh2,
        hf2.coeFn_toLp] with r hInv hF
      simp only [hInv, hF, RCLike.inner_apply]
    _ = inner ℂ (hh2.toLp h) (actualKLUnitary (hf2.toLp f)) := hunit.symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hh2.coeFn_toLp] with tau hhrep
      simp only [hhrep, RCLike.inner_apply]

/-- Actual forward identification for nonsmooth L1 intersect L2
physical data with a finite lower support bound. Smoothness appears only
in separating SPECTRAL tests, whose membership follows from compactness. -/
theorem physicalL1Forward_eq_actualKL_ae {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    physicalL1Forward f =ᵐ[tauMeasure] (actualKLUnitary (hf2.toLp f) : ℝ → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (physicalL1Forward_continuous hf ha).locallyIntegrable
    ((Lp.memLp (actualKLUnitary (hf2.toLp f))).locallyIntegrable (by norm_num))
  intro g hg hgc
  let h : ℝ → ℂ := fun tau => (g tau : ℂ)
  have hc : Continuous h := by dsimp only [h]; fun_prop
  have hs : HasCompactSupport h := hgc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hh : Integrable h tauMeasure := hc.integrable_of_hasCompactSupport hs
  have hh2 : MemLp h 2 tauMeasure := hc.memLp_of_hasCompactSupport hs
  have hpair := physical_forward_unitary_pairing hf hf2 ha hh hh2
  simpa [h, Complex.real_smul, mul_comm] using hpair

theorem physicalL1Forward_memLp {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume)
    {a : ℝ} (ha : ∀ r : ℝ, r < a → f r = 0) :
    MemLp (physicalL1Forward f) 2 tauMeasure :=
  (Lp.memLp (actualKLUnitary (hf2.toLp f))).congr
    (physicalL1Forward_eq_actualKL_ae hf hf2 ha).symm

end
end ImbalancedChen.Part3.ActualKLIntegrablePhysicalForward20261026a
