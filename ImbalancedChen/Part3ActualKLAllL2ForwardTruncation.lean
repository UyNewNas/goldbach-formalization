import ImbalancedChen.Part3ActualKLIntegrablePhysicalForward
import ImbalancedChen.Part3IndicatorInvariantCyclicDensity
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Arbitrary physical L2 KL transform by nonsmooth compact truncation

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The physical cutoff F*1_[-R,R] is proved L1 and L2; no smoothness is
claimed.  Its actual scalar K integral is identified with the original
unitary via the genuine inverse/compact-spectral-test duality theorem.
These integral representatives converge in the original raw KL L2 space.
Both the exact error norm and its literal (2/pi^2)tau*sinh(pi*tau)
weighted-square form are supplied. No uncut pointwise integral for
arbitrary physical L2 data or automorphic Gamma quotient assertion is made.
-/

namespace ImbalancedChen.Part3.ActualKLAllL2ForwardTruncation20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ActualKLCompactTestWeightedL220261025a ActualKLIntegrableSpectralInverse20261026a
open ActualKLIntegrablePhysicalForward20261026a IndicatorInvariantCyclicDensity20261025a

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

def physicalCutoffFunction (F : RadialL2) (R : ℝ) : ℝ → ℂ := (Icc (-R) R).indicator F

def actualKLPhysicalTruncation (F : RadialL2) (R : ℝ) : RadialL2 :=
  indicatorL2 volume (Icc (-R) R) measurableSet_Icc F

theorem actualKLPhysicalTruncation_ae (F : RadialL2) (R : ℝ) :
    actualKLPhysicalTruncation F R =ᵐ[(volume : Measure ℝ)] physicalCutoffFunction F R :=
  indicatorL2_coe_ae volume (Icc (-R) R) measurableSet_Icc F

theorem physicalCutoffFunction_memLp (F : RadialL2) (R : ℝ) :
    MemLp (physicalCutoffFunction F R) 2 volume :=
  (Lp.memLp F).indicator measurableSet_Icc

theorem physicalCutoffFunction_integrable (F : RadialL2) (R : ℝ) :
    Integrable (physicalCutoffFunction F R) := by
  have hi : IntegrableOn (F : ℝ → ℂ) (Icc (-R) R) :=
    MemLp.integrable (by norm_num) ((Lp.memLp F).restrict (Icc (-R) R))
  exact (integrable_indicator_iff measurableSet_Icc).mpr hi

theorem physicalCutoffFunction_zero_below (F : RadialL2) (R r : ℝ) (hr : r < -R) :
    physicalCutoffFunction F R r = 0 := by
  have hn : r ∉ Icc (-R) R := fun h => not_le_of_gt hr h.1
  simp only [physicalCutoffFunction, indicator_of_notMem hn]

def actualKLForwardTruncatedIntegral (F : RadialL2) (R tau : ℝ) : ℂ :=
  ∫ r in Icc (-R) R, F r * inverseKKernel tau r

theorem actualKLForwardTruncatedIntegral_eq_L1Forward (F : RadialL2) (R tau : ℝ) :
    actualKLForwardTruncatedIntegral F R tau = physicalL1Forward (physicalCutoffFunction F R) tau := by
  unfold actualKLForwardTruncatedIntegral physicalL1Forward
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => by
    by_cases hr : r ∈ Icc (-R) R
    · simp only [physicalCutoffFunction, indicator_of_mem hr]
    · simp only [physicalCutoffFunction, indicator_of_notMem hr, zero_mul])

/-- Scalar K integrability on every finite physical cutoff, even though
the physical vector is merely L2 and its cutoff need not be C-infinity. -/
theorem actualKLForwardTruncatedIntegral_integrable (F : RadialL2) (R tau : ℝ) :
    IntegrableOn (fun r : ℝ => F r * inverseKKernel tau r) (Icc (-R) R) := by
  have hi := physicalL1Forward_integrable (physicalCutoffFunction_integrable F R)
    (physicalCutoffFunction_zero_below F R) tau
  apply (integrable_indicator_iff measurableSet_Icc).mp
  apply hi.congr
  exact Eventually.of_forall (fun r => by
    by_cases hr : r ∈ Icc (-R) R
    · simp only [physicalCutoffFunction, indicator_of_mem hr]
    · simp only [physicalCutoffFunction, indicator_of_notMem hr, zero_mul])

theorem actualKLForwardTruncatedIntegral_continuous (F : RadialL2) (R : ℝ) :
    Continuous (actualKLForwardTruncatedIntegral F R) := by
  have he : actualKLForwardTruncatedIntegral F R = physicalL1Forward (physicalCutoffFunction F R) :=
    funext (actualKLForwardTruncatedIntegral_eq_L1Forward F R)
  rw [he]
  exact physicalL1Forward_continuous (physicalCutoffFunction_integrable F R)
    (physicalCutoffFunction_zero_below F R)

/-- Actual quotient-level forward representation for every finite
nonsmooth physical cutoff. It is obtained from genuine spectral duality. -/
theorem actualKLForwardTruncatedIntegral_eq_transform_ae (F : RadialL2) (R : ℝ) :
    actualKLForwardTruncatedIntegral F R =ᵐ[tauMeasure]
      (actualKLUnitary (actualKLPhysicalTruncation F R) : ℝ → ℂ) := by
  have hae := physicalL1Forward_eq_actualKL_ae (physicalCutoffFunction_integrable F R)
    (physicalCutoffFunction_memLp F R) (physicalCutoffFunction_zero_below F R)
  have he : actualKLForwardTruncatedIntegral F R = physicalL1Forward (physicalCutoffFunction F R) :=
    funext (actualKLForwardTruncatedIntegral_eq_L1Forward F R)
  rw [he]
  simpa only [actualKLPhysicalTruncation, indicatorL2] using hae

theorem actualKLForwardTruncatedIntegral_memLp (F : RadialL2) (R : ℝ) :
    MemLp (actualKLForwardTruncatedIntegral F R) 2 tauMeasure :=
  (Lp.memLp (actualKLUnitary (actualKLPhysicalTruncation F R))).congr
    (actualKLForwardTruncatedIntegral_eq_transform_ae F R).symm

theorem actualKLForwardTruncatedIntegral_toLp (F : RadialL2) (R : ℝ) :
    (actualKLForwardTruncatedIntegral_memLp F R).toLp (actualKLForwardTruncatedIntegral F R) =
      actualKLUnitary (actualKLPhysicalTruncation F R) := by
  apply Lp.ext
  exact (actualKLForwardTruncatedIntegral_memLp F R).coeFn_toLp.trans
    (actualKLForwardTruncatedIntegral_eq_transform_ae F R)

private theorem scalarL2_norm_sq_integral {mu : Measure ℝ} (u : Lp ℂ 2 mu) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  have hL2 : inner ℂ u u = ∫ x, inner ℂ (u x) (u x) ∂mu := L2.inner_def _ _
  simp_rw [inner_self_eq_norm_sq_to_K] at hL2
  rw [integral_ofReal] at hL2
  exact Complex.ofReal_injective hL2

theorem actualKLPhysicalTruncation_tendsto (F : RadialL2) :
    Tendsto (actualKLPhysicalTruncation F) atTop (𝓝 F) := by
  have hi : Integrable (fun r : ℝ => ‖F r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hlim : Tendsto (fun R : ℝ => ∫ r : ℝ,
      ‖physicalCutoffFunction F R r - F r‖ ^ 2) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun r : ℝ => ‖F r‖ ^ 2)
    · exact Eventually.of_forall (fun R =>
        ((((Lp.aestronglyMeasurable F).indicator measurableSet_Icc).sub
          (Lp.aestronglyMeasurable F)).norm.pow 2))
    · exact Eventually.of_forall (fun R => Eventually.of_forall (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        by_cases hr : r ∈ Icc (-R) R
        · simp only [physicalCutoffFunction, indicator_of_mem hr, sub_self, norm_zero,
            zero_pow (by norm_num : 2 ≠ 0)]
          exact sq_nonneg _
        · simp only [physicalCutoffFunction, indicator_of_notMem hr, zero_sub, norm_neg, le_refl]))
    · exact hi
    · exact Eventually.of_forall (fun r : ℝ => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (max r (-r))] with R hR
        have hl : -R ≤ r := by have := (le_max_right r (-r)).trans hR; linarith
        have hu : r ≤ R := (le_max_left r (-r)).trans hR
        simp only [physicalCutoffFunction, indicator_of_mem (show r ∈ Icc (-R) R from ⟨hl, hu⟩),
          sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)])
  have hsq : Tendsto (fun R : ℝ => ‖actualKLPhysicalTruncation F R - F‖ ^ 2) atTop (𝓝 0) := by
    have heq : ∀ R : ℝ, ‖actualKLPhysicalTruncation F R - F‖ ^ 2 =
        ∫ r : ℝ, ‖physicalCutoffFunction F R r - F r‖ ^ 2 := by
      intro R
      rw [scalarL2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (actualKLPhysicalTruncation F R) F,
        actualKLPhysicalTruncation_ae F R] with r hsub hcut
      rw [hsub, hcut]
    simpa only [heq, integral_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hn

/-- Arbitrary physical L2 data: literal finite scalar transforms converge
in the actual raw spectral L2 norm to the original KL unitary. -/
theorem actualKLAllL2_forward_by_truncated_integrals (F : RadialL2) :
    Tendsto (fun R : ℝ =>
      (actualKLForwardTruncatedIntegral_memLp F R).toLp (actualKLForwardTruncatedIntegral F R))
      atTop (𝓝 (actualKLUnitary F)) := by
  have h := actualKLUnitary.continuous.continuousAt.tendsto.comp (actualKLPhysicalTruncation_tendsto F)
  simpa only [actualKLForwardTruncatedIntegral_toLp] using h

theorem actualKLForwardTruncatedIntegral_error_norm (F : RadialL2) (R : ℝ) :
    ‖(actualKLForwardTruncatedIntegral_memLp F R).toLp (actualKLForwardTruncatedIntegral F R) -
      actualKLUnitary F‖ = ‖actualKLPhysicalTruncation F R - F‖ := by
  rw [actualKLForwardTruncatedIntegral_toLp, ← map_sub]
  exact actualKLUnitary.norm_map _

private theorem raw_weighted_square_of_ae (u : RawTauL2) {h : ℝ → ℂ}
    (hae : (u : ℝ → ℂ) =ᵐ[tauMeasure] h) :
    ‖u‖ ^ 2 = ∫ tau in Ioi (0 : ℝ), actualKLWeight tau * ‖h tau‖ ^ 2 := by
  rw [scalarL2_norm_sq_integral]
  calc
    _ = ∫ tau, ‖h tau‖ ^ 2 ∂tauMeasure := by
      apply integral_congr_ae
      filter_upwards [hae] with tau htau
      rw [htau]
    _ = _ := by
      unfold tauMeasure positiveDensityMeasure
      rw [integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) by
          unfold tauDensity
          fun_prop)
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      rw [ENNReal.toReal_ofReal (show 0 ≤ tauDensity tau from actualKLWeight_nonneg htau.le)]
      rfl

/-- The literal weighted error has a genuinely finite integral, so the
exact error formula below does not rely on an undefined Bochner value. -/
theorem actualKLForwardTruncatedIntegral_weighted_error_integrable (F : RadialL2) (R : ℝ) :
    IntegrableOn (fun tau : ℝ => actualKLWeight tau *
      ‖actualKLForwardTruncatedIntegral F R tau - actualKLUnitary F tau‖ ^ 2) (Ioi 0) := by
  have he : MemLp (fun tau : ℝ => actualKLForwardTruncatedIntegral F R tau - actualKLUnitary F tau)
      2 tauMeasure :=
    (actualKLForwardTruncatedIntegral_memLp F R).sub (Lp.memLp (actualKLUnitary F))
  have hi := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  unfold tauMeasure positiveDensityMeasure at hi
  have hw : Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) := by
    unfold tauDensity
    fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hw (by simp)] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  rw [ENNReal.toReal_ofReal (show 0 ≤ tauDensity tau from actualKLWeight_nonneg htau.le)]
  rfl

/-- Exact literal original-weight error identity. This is the actual raw
KL measure, retaining both 2/pi^2 and tau*sinh(pi*tau). -/
theorem actualKLForwardTruncatedIntegral_weighted_error (F : RadialL2) (R : ℝ) :
    (∫ tau in Ioi (0 : ℝ), ((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau)) *
      ‖actualKLForwardTruncatedIntegral F R tau - actualKLUnitary F tau‖ ^ 2) =
      ∫ r : ℝ, ‖physicalCutoffFunction F R r - F r‖ ^ 2 := by
  let u : RawTauL2 := actualKLUnitary (actualKLPhysicalTruncation F R) - actualKLUnitary F
  have hae : (u : ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => actualKLForwardTruncatedIntegral F R tau - actualKLUnitary F tau) := by
    filter_upwards [Lp.coeFn_sub (actualKLUnitary (actualKLPhysicalTruncation F R)) (actualKLUnitary F),
      actualKLForwardTruncatedIntegral_eq_transform_ae F R] with tau hsub hcut
    rw [hsub, hcut]
  have hraw := raw_weighted_square_of_ae u hae
  change ‖u‖ ^ 2 = (∫ tau in Ioi (0 : ℝ), ((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau)) *
      ‖actualKLForwardTruncatedIntegral F R tau - actualKLUnitary F tau‖ ^ 2) at hraw
  rw [← hraw]
  have hnorm : ‖u‖ = ‖actualKLPhysicalTruncation F R - F‖ := by
    dsimp only [u]
    rw [← map_sub]
    exact actualKLUnitary.norm_map _
  rw [hnorm, scalarL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (actualKLPhysicalTruncation F R) F,
    actualKLPhysicalTruncation_ae F R] with r hsub hcut
  rw [hsub, hcut]

end
end ImbalancedChen.Part3.ActualKLAllL2ForwardTruncation20261026a
