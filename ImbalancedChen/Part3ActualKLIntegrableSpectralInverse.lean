import ImbalancedChen.Part3ActualKLOntoUnitary
import ImbalancedChen.Part3ActualKLInversionFubini
import ImbalancedChen.Part3ComplexOrderKUniformStripDecay
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Scalar inverse K integrals for integrable raw spectral data

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The inverse integral is a scalar integral against the ACTUAL raw KL
measure.  An L1 spectral amplitude gives a common bound on every compact
radial interval.  Fubini is applied only after a compact physical test is
inserted.  If the amplitude is also L2, the genuine actual KL unitary
and smooth-test separation identify the scalar integral with its inverse
L2 vector.  No single K_(i*tau)(exp r) is asserted to belong to L2(dr),
and no L2-valued kernel integral is used.
-/

namespace ImbalancedChen.Part3.ActualKLIntegrableSpectralInverse20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ComplexOrderKHolomorphicSourceOnly ComplexOrderKUniformStripDecay20261025a
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualGreenBoundaryMajorant20261025a ActualGreenBoundaryDiagonal20261025a

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

def inverseKKernel (tau r : ℝ) : ℂ := radialK ((tau : ℂ) * Complex.I) r

theorem inverseKKernel_radial_continuous (tau : ℝ) : Continuous (inverseKKernel tau) :=
  (radialK_C2 ((tau : ℂ) * Complex.I)).continuous

theorem inverseKKernel_joint_stronglyMeasurable :
    StronglyMeasurable (fun p : ℝ × ℝ => inverseKKernel p.1 p.2) := by
  have hbase : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      complexOrderIntegrand ((p.1.1 : ℂ) * Complex.I) (Real.exp p.1.2) p.2) := by
    unfold complexOrderIntegrand
    fun_prop
  exact hbase.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))

/-- A true scalar bound, uniform in ALL real imaginary-order parameters.
Its dependence on the radial lower bound is retained explicitly. -/
theorem inverseKKernel_uniform_bound (a : ℝ) {r : ℝ} (hr : a ≤ r) (tau : ℝ) :
    ‖inverseKKernel tau r‖ ≤ stripDecayConstant 0 (Real.exp a) 1 := by
  have hk := complexOrderK_uniform_exp_bound (Real.exp_pos a)
    (Real.exp_le_exp.mpr hr) (by simp : |((tau : ℂ) * Complex.I).re| ≤ (1 : ℝ))
  apply hk.trans
  apply mul_le_of_le_one_right (stripDecayConstant_pos 0 (Real.exp a) 1).le
  exact Real.exp_le_one_iff.mpr (by have := Real.exp_pos r; linarith)

def spectralL1Inverse (h : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ tau, h tau * inverseKKernel tau r ∂tauMeasure

theorem spectralL1Inverse_integrable {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (r : ℝ) :
    Integrable (fun tau => h tau * inverseKKernel tau r) tauMeasure := by
  have hk : AEStronglyMeasurable (fun tau => inverseKKernel tau r) tauMeasure := by
    have hc : Continuous (fun tau : ℝ => inverseKKernel tau r) := by
      apply continuous_iff_continuousAt.mpr
      intro tau
      have hd := complexOrderK_hasDerivAt ((tau : ℂ) * Complex.I) (Real.exp r)
        (Real.exp_pos r) (by simp; norm_num)
      exact hd.continuousAt.comp (by fun_prop)
    exact hc.aestronglyMeasurable
  apply (hh.norm.const_mul (stripDecayConstant 0 (Real.exp r) 1)).mono'
    (hh.aestronglyMeasurable.mul hk)
  exact Eventually.of_forall (fun tau => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (inverseKKernel_uniform_bound r le_rfl tau) (norm_nonneg _)).trans_eq (mul_comm _ _))

/-- The same integrable spectral majorant works throughout a compact
physical interval. This is a local scalar-integral statement. -/
theorem spectralL1Inverse_local_majorant {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (a b : ℝ) :
    Integrable (fun tau => stripDecayConstant 0 (Real.exp a) 1 * ‖h tau‖) tauMeasure ∧
      ∀ r ∈ Icc a b, ∀ tau : ℝ,
        ‖h tau * inverseKKernel tau r‖ ≤
          stripDecayConstant 0 (Real.exp a) 1 * ‖h tau‖ := by
  refine ⟨hh.norm.const_mul _, ?_⟩
  intro r hr tau
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (inverseKKernel_uniform_bound a hr.1 tau) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem spectralL1Inverse_continuous {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) : Continuous (spectralL1Inverse h) := by
  apply continuous_iff_continuousAt.mpr
  intro r0
  change Tendsto (fun r => ∫ tau, h tau * inverseKKernel tau r ∂tauMeasure)
    (𝓝 r0) (𝓝 (∫ tau, h tau * inverseKKernel tau r0 ∂tauMeasure))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun tau => stripDecayConstant 0 (Real.exp (r0 - 1)) 1 * ‖h tau‖)
  · exact Eventually.of_forall (fun r => (spectralL1Inverse_integrable hh r).aestronglyMeasurable)
  · filter_upwards [Ioi_mem_nhds (show r0 - 1 < r0 by linarith)] with r hr
    exact Eventually.of_forall (fun tau => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left
        (inverseKKernel_uniform_bound (r0 - 1) hr.le tau) (norm_nonneg _)).trans_eq (mul_comm _ _))
  · exact hh.norm.const_mul _
  · exact Eventually.of_forall (fun tau =>
      (continuous_const.mul (inverseKKernel_radial_continuous tau)).tendsto r0)

theorem inverse_test_product_integrable {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (U : RadialTest) :
    Integrable (fun p : ℝ × ℝ =>
      (h p.1 * inverseKKernel p.1 p.2) * star (U.function p.2)) (tauMeasure.prod volume) := by
  obtain ⟨a, ha⟩ := U.compact.bddBelow
  have htest : Integrable (fun r : ℝ => ‖U.function r‖) :=
    (U.smooth.continuous.integrable_of_hasCompactSupport U.compact).norm
  have hmajor := (hh.norm.const_mul (stripDecayConstant 0 (Real.exp a) 1)).mul_prod htest
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (h p.1 * inverseKKernel p.1 p.2) * star (U.function p.2)) (tauMeasure.prod volume) :=
    ((hh.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).mul
      inverseKKernel_joint_stronglyMeasurable.aestronglyMeasurable).mul
        (U.smooth.continuous.star.aestronglyMeasurable.comp_quasiMeasurePreserving
          quasiMeasurePreserving_snd)
  apply hmajor.mono' hmeas
  exact Eventually.of_forall (fun p => by
    rw [norm_mul, norm_mul, norm_star]
    by_cases hz : U.function p.2 = 0
    · simp only [hz, norm_zero, mul_zero]
    have hk := inverseKKernel_uniform_bound a (ha (subset_tsupport U.function hz)) p.1
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (norm_nonneg (h p.1)))
      (norm_nonneg (U.function p.2))).trans_eq (by ring))

/-- Compact physical tests are inserted BEFORE applying scalar Fubini. -/
theorem spectralL1Inverse_test_pairing {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (U : RadialTest) :
    (∫ r : ℝ, spectralL1Inverse h r * star (U.function r)) =
      ∫ tau, h tau * star (actualKtransform U.function tau) ∂tauMeasure := by
  calc
    _ = ∫ r : ℝ, ∫ tau, (h tau * inverseKKernel tau r) * star (U.function r) ∂tauMeasure := by
      simp only [spectralL1Inverse, integral_mul_const]
    _ = ∫ tau, ∫ r : ℝ, (h tau * inverseKKernel tau r) * star (U.function r) ∂tauMeasure :=
      (integral_integral_swap (inverse_test_product_integrable hh U)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun tau => by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        change h tau * rawRadialKTransform (fun r => star (U.function r)) tau = _
        rw [rawRadialKTransform_star, rawRadialKTransform_eq_actualKtransform])

private theorem unitary_inverse_test_pairing {h : ℝ → ℂ}
    (hh2 : MemLp h 2 tauMeasure) (U : RadialTest) :
    (∫ r : ℝ, (actualKLUnitary.symm (hh2.toLp h) : RadialL2) r * star (U.function r)) =
      ∫ tau, h tau * star (actualKtransform U.function tau) ∂tauMeasure := by
  let V : RadialL2 := actualKLUnitary.symm (hh2.toLp h)
  have hinner := actualKLUnitary.inner_map_map (radialCoreL2 U) V
  rw [actualKLUnitary_on_test, actualKLUnitary.apply_symm_apply] at hinner
  calc
    _ = inner ℂ (radialCoreL2 U) V := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [U.function_memLp.coeFn_toLp] with r hU
      simp only [radialCoreL2, hU, RCLike.inner_apply]
    _ = inner ℂ (rawKLTestTransform U) (hh2.toLp h) := hinner.symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [rawKLTestTransform_ae U, hh2.coeFn_toLp] with tau hU hh
      simp only [hU, hh, RCLike.inner_apply]

/-- Actual inverse representation for L1 intersect L2 spectral data.
Global physical L2 membership is a CONCLUSION of weak test separation. -/
theorem spectralL1Inverse_eq_unitary_inverse_ae {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (hh2 : MemLp h 2 tauMeasure) :
    spectralL1Inverse h =ᵐ[(volume : Measure ℝ)]
      (actualKLUnitary.symm (hh2.toLp h) : RadialL2) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (spectralL1Inverse_continuous hh).locallyIntegrable
    ((Lp.memLp (actualKLUnitary.symm (hh2.toLp h))).locallyIntegrable (by norm_num))
  intro g hg hgc
  let U : RadialTest :=
    { function := fun r : ℝ => (g r : ℂ)
      smooth := by fun_prop
      compact := hgc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp) }
  have hpair := (spectralL1Inverse_test_pairing hh U).trans
    (unitary_inverse_test_pairing hh2 U).symm
  simpa [U, Complex.real_smul, mul_comm] using hpair

theorem spectralL1Inverse_memLp {h : ℝ → ℂ}
    (hh : Integrable h tauMeasure) (hh2 : MemLp h 2 tauMeasure) :
    MemLp (spectralL1Inverse h) 2 volume :=
  (Lp.memLp (actualKLUnitary.symm (hh2.toLp h))).congr
    (spectralL1Inverse_eq_unitary_inverse_ae hh hh2).symm

/-- Correct literal raw-KL measure factor. No Gamma quotient measure is
identified with this density. -/
theorem spectralL1Inverse_literal_weight (h : ℝ → ℂ) (r : ℝ) :
    spectralL1Inverse h r = ∫ tau in Ioi (0 : ℝ),
      (((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau) : ℝ) : ℂ) *
        h tau * complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) := by
  unfold spectralL1Inverse tauMeasure positiveDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) by
      unfold tauDensity
      fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  rw [ENNReal.toReal_ofReal (show 0 ≤ tauDensity tau from actualKLWeight_nonneg htau.le)]
  simp only [Complex.real_smul, inverseKKernel, radialK, tauDensity]
  ring

end
end ImbalancedChen.Part3.ActualKLIntegrableSpectralInverse20261026a
