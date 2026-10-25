import ImbalancedChen.Part3ActualRadialZeroMode
import ImbalancedChen.Part3ActualRadialShiftGreenBinding
import ImbalancedChen.Part3GenericResolventScalarZeroAtom
import ImbalancedChen.Part3GenericResolventCyclicIntertwining
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual radial scalar endpoint atoms. The scalar measure is the genuinely
constructed generic RMK measure instantiated at the actual radial R1.
Its L2 indicator of t=1 maps through the actual cyclic isometry to a
fixed vector of R1. The independently proved radial zero-mode theorem
forces that vector, then the indicator and its measure, to vanish.

The actual lambda=1/t-1 pushforward therefore has no atom at lambda=0.
Injectivity of R1 separately removes t=0. Positivity and contraction give
the remaining spectrum bounds, so the pushforward has its full physical
norm-squared mass on (0,infinity). No no-atom conclusion is assumed and
no constant cusp-mode or Gamma0 measure is substituted.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventScalarZeroAtom20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a

abbrev RadialBoundedSpectrum := ResolventSpectrum radialUnitShiftResolvent

abbrev radialBoundedScalarMeasure (F : RadialL2) : Measure RadialBoundedSpectrum :=
  scalarMeasure radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F

def radialOneFiber : Set RadialBoundedSpectrum := {t | (t : ℝ) = 1}

/-- A scalar endpoint atom would create an ACTUAL radial R1 fixed vector,
through the already constructed cyclic isometry and intertwining. -/
theorem radialBoundedScalarMeasure_oneFiber (F : RadialL2) :
    radialBoundedScalarMeasure F radialOneFiber = 0 := by
  classical
  let R := radialUnitShiftResolvent
  let hSA := radialUnitShiftResolvent_selfAdjoint
  let mu := radialBoundedScalarMeasure F
  have hB : MeasurableSet radialOneFiber := by
    unfold radialOneFiber
    fun_prop
  let xi : ScalarL2 R hSA F := indicatorConstLp 2 hB (measure_ne_top mu radialOneFiber) (1 : ℂ)
  have hxi : xi =ᵐ[mu] radialOneFiber.indicator (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  have hM : coordinateMultiplier R hSA F xi = xi := by
    apply Lp.ext
    filter_upwards [coordinateMultiplier_coe_ae R hSA F xi, hxi] with t ht htxi
    rw [ht, htxi]
    by_cases hmem : t ∈ radialOneFiber
    · have hone : (t : ℝ) = 1 := hmem
      simp only [Set.indicator_of_mem hmem, hone, Complex.ofReal_one, one_mul]
    · simp only [Set.indicator_of_notMem hmem, mul_zero]
  have hfixed : R (cyclicExtension R hSA F xi) = cyclicExtension R hSA F xi := by
    have h := cyclicExtension_intertwine R hSA F xi
    rw [hM] at h
    exact h.symm
  have hext : cyclicExtension R hSA F xi = 0 :=
    radialUnitShiftResolvent_fixedPoint_zero _ hfixed
  have hxizero : xi = 0 := by
    apply (cyclicIsometry R hSA F).injective
    change cyclicExtension R hSA F xi = cyclicExtension R hSA F 0
    rw [hext, map_zero]
  have hindicator : radialOneFiber.indicator (fun _ => (1 : ℂ)) =ᵐ[mu] (fun _ => 0) := by
    have hz : xi =ᵐ[mu] (fun _ => 0) := by
      rw [hxizero]
      exact Lp.coeFn_zero ℂ 2 mu
    exact hxi.symm.trans hz
  have hnot : ∀ᵐ t ∂mu, t ∉ radialOneFiber := by
    filter_upwards [hindicator] with t ht
    intro hm
    have hone : (1 : ℂ) = 0 := by simpa only [Set.indicator_of_mem hm] using ht
    exact one_ne_zero hone
  simpa only [not_not] using ae_iff.mp hnot

theorem radialBoundedScalarMeasure_ae_strict_unitInterval (F : RadialL2) :
    ∀ᵐ t ∂radialBoundedScalarMeasure F, 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  have hzero := scalarMeasure_ae_coordinate_ne_zero radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_injective F
  have hone : ∀ᵐ t ∂radialBoundedScalarMeasure F, (t : ℝ) ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using radialBoundedScalarMeasure_oneFiber F
  filter_upwards [hzero, hone] with t ht0 ht1
  have hb := spectrum_coordinate_mem_unitInterval radialUnitShiftResolvent
    radialUnitShiftResolvent_nonneg radialUnitShiftResolvent_opNorm_le_one t
  exact ⟨lt_of_le_of_ne hb.1 (Ne.symm ht0), lt_of_le_of_ne hb.2 ht1⟩

def radialSpectralLambda (t : RadialBoundedSpectrum) : ℝ := (t : ℝ)⁻¹ - 1

theorem radialSpectralLambda_measurable : Measurable radialSpectralLambda := by
  unfold radialSpectralLambda
  fun_prop

theorem radialSpectralLambda_eq_zero_iff (t : RadialBoundedSpectrum) :
    radialSpectralLambda t = 0 ↔ (t : ℝ) = 1 := by
  constructor
  · intro h
    have hi : (t : ℝ)⁻¹ = 1 := sub_eq_zero.mp h
    have h' := congrArg (fun x : ℝ => x⁻¹) hi
    simpa only [inv_inv, inv_one] using h'
  · intro h
    simp [radialSpectralLambda, h]

def radialUnboundedScalarMeasure (F : RadialL2) : Measure ℝ :=
  (radialBoundedScalarMeasure F).map radialSpectralLambda

instance radialUnboundedScalarMeasure_finite (F : RadialL2) :
    IsFiniteMeasure (radialUnboundedScalarMeasure F) := by
  unfold radialUnboundedScalarMeasure
  infer_instance

/-- The actual unbounded radial spectral zero atom is absent because
the t=1 atom was eliminated by the true exp-energy kernel argument. -/
theorem radialUnboundedScalarMeasure_singleton_zero (F : RadialL2) :
    radialUnboundedScalarMeasure F ({0} : Set ℝ) = 0 := by
  rw [radialUnboundedScalarMeasure,
    Measure.map_apply radialSpectralLambda_measurable measurableSet_singleton]
  have hpre : radialSpectralLambda ⁻¹' ({0} : Set ℝ) = radialOneFiber := by
    ext t
    exact radialSpectralLambda_eq_zero_iff t
  rw [hpre, radialBoundedScalarMeasure_oneFiber]

theorem radialSpectralLambda_pos_ae (F : RadialL2) :
    ∀ᵐ t ∂radialBoundedScalarMeasure F, 0 < radialSpectralLambda t := by
  filter_upwards [radialBoundedScalarMeasure_ae_strict_unitInterval F] with t ht
  have hi : (1 : ℝ) < 1 / (t : ℝ) := (lt_div_iff₀ ht.1).2 (by simpa using ht.2)
  simpa only [radialSpectralLambda, one_div] using sub_pos.mpr hi

theorem radialUnboundedScalarMeasure_Iic_zero (F : RadialL2) :
    radialUnboundedScalarMeasure F (Iic 0) = 0 := by
  rw [radialUnboundedScalarMeasure,
    Measure.map_apply radialSpectralLambda_measurable measurableSet_Iic]
  have h := ae_iff.mp (radialSpectralLambda_pos_ae F)
  simpa only [not_lt] using h

theorem radialUnboundedScalarMeasure_univ (F : RadialL2) :
    radialUnboundedScalarMeasure F univ = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [radialUnboundedScalarMeasure,
    Measure.map_apply radialSpectralLambda_measurable MeasurableSet.univ, preimage_univ]
  exact scalarMeasure_univ radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F

/-- All physical norm-squared mass lies on positive radial spectral
parameters. No Stone density or KL Plancherel endpoint is inferred here. -/
theorem radialUnboundedScalarMeasure_positive_mass (F : RadialL2) :
    radialUnboundedScalarMeasure F (Ioi 0) = ENNReal.ofReal (‖F‖ ^ 2) := by
  have hsum : radialUnboundedScalarMeasure F (Ioi 0) +
      radialUnboundedScalarMeasure F ((Ioi (0 : ℝ))ᶜ) =
        radialUnboundedScalarMeasure F univ := measure_add_measure_compl measurableSet_Ioi
  have hcompl : (Ioi (0 : ℝ))ᶜ = Iic 0 := by ext x; simp
  rw [hcompl, radialUnboundedScalarMeasure_Iic_zero, add_zero,
    radialUnboundedScalarMeasure_univ] at hsum
  exact hsum

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
