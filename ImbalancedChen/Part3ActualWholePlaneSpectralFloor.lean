import ImbalancedChen.Part3ActualWholePlaneHardyFloor
import ImbalancedChen.Part3ActualResolventZeroAtomPushforward
import Mathlib.MeasureTheory.Measure.Support

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Actual whole-upper-half-plane scalar spectral support and exact Hardy
endpoint equality conditions. The measures are the constructed RMK scalar
measure and its already constructed inverse-resolvent pushforward.
No endpoint no-eigen/no-atom assumption or Gamma quotient claim is made.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualWholePlaneSpectralFloorSourceOnly

open MeasureTheory Set Filter
open MaassWeakOperatorCore20261024zz MaassFiniteCoreL2Graph20261025a
open MaassFiniteCoreL2LinearOperator20261025a MaassFirstGradientWeakLimit20261025a
open MaassFirstGradientClosability20261025a ActualCompletedTensorEnergyForm20261025a
open ActualCompletedEnergyResolvent20261025a ActualWholePlaneHardyFloorSourceOnly
open ActualResolventScalarMeasure20261025a ActualResolventZeroAtomPushforward20261025a

/-- The actual resolvent spectrum lies in [0,4/5], by the proved actual
operator norm bound. This is a pointwise spectral statement. -/
theorem resolventSpectrum_subset_fourFifths :
    spectrum ℝ actualWeakResolvent ⊆ Icc (0 : ℝ) (4 / 5) := by
  intro t ht
  refine ⟨(resolventSpectrum_subset_unitInterval ht).1, ?_⟩
  have hn : ‖t‖ ≤ ‖actualWeakResolvent‖ * ‖(1 : ResolventAlgebra)‖ :=
    spectrum.norm_le_norm_mul_of_mem ht
  have hone : ‖(1 : ResolventAlgebra)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hb : ‖actualWeakResolvent‖ * ‖(1 : ResolventAlgebra)‖ ≤ (4 / 5 : ℝ) := by
    calc
      _ ≤ (4 / 5 : ℝ) * 1 := mul_le_mul actualWeakResolvent_opNorm_le_four_fifths
        hone (norm_nonneg _) (by norm_num)
      _ = _ := mul_one _
  exact (Real.le_norm_self t).trans (hn.trans hb)

theorem spectrumCoordinate_mem_fourFifths (t : ResolventSpectrum) :
    (t : ℝ) ∈ Icc (0 : ℝ) (4 / 5) := resolventSpectrum_subset_fourFifths t.property

/-- Actual scalar RMK measures have no mass above 4/5. -/
theorem scalarMeasure_above_fourFifths (f : HyperbolicL2) :
    scalarMeasure f {t : ResolventSpectrum | (4 / 5 : ℝ) < (t : ℝ)} = 0 := by
  have he : {t : ResolventSpectrum | (4 / 5 : ℝ) < (t : ℝ)} = ∅ := by
    ext t
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (spectrumCoordinate_mem_fourFifths t).2
  rw [he, measure_empty]

theorem scalarMeasure_support_subset_fourFifths (f : HyperbolicL2) :
    (scalarMeasure f).support ⊆
      {t : ResolventSpectrum | (t : ℝ) ∈ Icc (0 : ℝ) (4 / 5)} := by
  intro t ht
  exact spectrumCoordinate_mem_fourFifths t

/-- Zero is removed only almost everywhere, by the previously proved
actual zero-atom theorem. No topological support exclusion at zero is claimed. -/
theorem scalarMeasure_coordinate_mem_positive_fourFifths_ae (f : HyperbolicL2) :
    ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f,
      (t : ℝ) ∈ Ioc (0 : ℝ) (4 / 5) := by
  filter_upwards [scalarMeasure_coordinate_pos_ae f] with t ht
  exact ⟨ht, (spectrumCoordinate_mem_fourFifths t).2⟩

/-- The literal inverse-resolvent coordinate has the actual Hardy floor. -/
theorem spectralLambda_ge_quarter {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    (1 / 4 : ℝ) ≤ spectralLambda t := by
  have hb := (spectrumCoordinate_mem_fourFifths t).2
  have hi : (5 / 4 : ℝ) ≤ 1 / (t : ℝ) :=
    (le_div_iff₀ ht).2 (by nlinarith)
  unfold spectralLambda
  rw [one_div] at hi
  linarith

/-- The genuine lambda pushforward has no mass below 1/4. -/
theorem unboundedScalarMeasure_Iio_quarter (f : HyperbolicL2) :
    unboundedScalarMeasure f (Iio (1 / 4 : ℝ)) = 0 := by
  rw [unboundedScalarMeasure, Measure.map_apply measurable_spectralLambda measurableSet_Iio]
  apply measure_mono_null (t := zeroFiber) ?_ (scalarMeasure_zeroFiber f)
  intro t ht
  change spectralLambda t < (1 / 4 : ℝ) at ht
  by_contra hzero
  change (t : ℝ) ≠ 0 at hzero
  have hpos : 0 < (t : ℝ) :=
    lt_of_le_of_ne (spectrumCoordinate_mem_fourFifths t).1 (Ne.symm hzero)
  exact not_lt_of_ge (spectralLambda_ge_quarter hpos) ht

theorem unboundedScalarMeasure_ge_quarter_ae (f : HyperbolicL2) :
    ∀ᵐ lambda : ℝ ∂unboundedScalarMeasure f, (1 / 4 : ℝ) ≤ lambda := by
  rw [ae_iff]
  simpa only [not_le] using unboundedScalarMeasure_Iio_quarter f

/-- Genuine topological support of the actual lambda measure, not merely
a bound for a separately declared measure. -/
theorem unboundedScalarMeasure_support_subset_quarter (f : HyperbolicL2) :
    (unboundedScalarMeasure f).support ⊆ Ici (1 / 4 : ℝ) :=
  Measure.support_subset_of_isClosed isClosed_Ici (unboundedScalarMeasure_ge_quarter_ae f)

/-- Exact completed Hardy equality: equality forces horizontal gradient
zero and saturation of the vertical bound. It does not assert the vector
vanishes, which requires an additional genuine L2 weak-derivative argument. -/
theorem completedHardy_equality_iff (u : completedEnergy) :
    ‖completedGradient false u‖ ^ 2 + ‖completedGradient true u‖ ^ 2 =
        (1 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 ↔
      completedGradient false u = 0 ∧
        ‖completedGradient true u‖ ^ 2 = (1 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 := by
  constructor
  · intro heq
    have hv := completedEnergy_vertical_hardy u
    have hx : completedGradient false u = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖completedGradient false u‖, norm_nonneg (completedGradient false u)]
    refine ⟨hx, ?_⟩
    simpa only [hx, norm_zero, zero_pow, zero_add] using heq
  · rintro ⟨hx, hy⟩
    simp only [hx, norm_zero, zero_pow, zero_add, hy]

private theorem completedEnergy_norm_sq (u : completedEnergy) :
    ‖u‖ ^ 2 = ‖physicalProjection u‖ ^ 2 +
      ‖completedGradient false u‖ ^ 2 + ‖completedGradient true u‖ ^ 2 := by
  have h := congrArg Complex.re (completedEnergy_inner_coordinates u u)
  simpa only [Complex.add_re, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem completedShiftedHardy_equality_iff (u : completedEnergy) :
    ‖u‖ ^ 2 = (5 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 ↔
      completedGradient false u = 0 ∧
        ‖completedGradient true u‖ ^ 2 = (1 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 := by
  rw [← completedHardy_equality_iff]
  rw [completedEnergy_norm_sq]
  constructor <;> intro h <;> linarith

/-- The precise horizontal distributional consequence of equality, using
the actual closed first-gradient Green formula and actual compact tensors. -/
theorem horizontal_zero_actual_green_tests (u : completedEnergy)
    (hx : completedGradient false u = 0) (T : CompactTensor) :
    inner ℂ (physicalProjection u) (liftedGradientL2 false T) = 0 := by
  have h := closure_finiteGradientGraph_green false
    (completedGradient_mem_closed_graph false u) T
  rw [hx, inner_zero_left] at h
  exact neg_eq_zero.mp h.symm

/-- A putative resolvent endpoint eigenvector saturates the actual
completed shifted Hardy bound. This stops short of an unsupported
endpoint no-eigen or no-atom conclusion. -/
theorem endpoint_eigen_completed_equality {f : HyperbolicL2}
    (heigen : actualWeakResolvent f = (4 / 5 : ℂ) • f) :
    ‖energyRieszSolution f‖ ^ 2 =
      (5 / 4 : ℝ) * ‖physicalProjection (energyRieszSolution f)‖ ^ 2 := by
  have hp : ‖physicalProjection (energyRieszSolution f)‖ ^ 2 =
      (16 / 25 : ℝ) * ‖f‖ ^ 2 := by
    rw [← actualWeakResolvent_apply, heigen, norm_smul, mul_pow]
    norm_num [norm_div] <;> ring
  have hinner : inner ℂ f ((4 / 5 : ℂ) • f) = (((4 / 5 : ℝ) * ‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  have hq := actualWeakResolvent_quadratic f
  rw [heigen, hinner, Complex.ofReal_re] at hq
  rw [hp]
  nlinarith

theorem endpoint_eigen_horizontal_gradient_zero {f : HyperbolicL2}
    (heigen : actualWeakResolvent f = (4 / 5 : ℂ) • f) :
    completedGradient false (energyRieszSolution f) = 0 :=
  ((completedShiftedHardy_equality_iff _).1 (endpoint_eigen_completed_equality heigen)).1

theorem endpoint_eigen_actual_horizontal_tests {f : HyperbolicL2}
    (heigen : actualWeakResolvent f = (4 / 5 : ℂ) • f) (T : CompactTensor) :
    inner ℂ (physicalProjection (energyRieszSolution f)) (liftedGradientL2 false T) = 0 :=
  horizontal_zero_actual_green_tests _ (endpoint_eigen_horizontal_gradient_zero heigen) T

end ImbalancedChen.Part3.ActualWholePlaneSpectralFloorSourceOnly
