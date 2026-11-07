import ImbalancedChen.Part3VerticalHardy
import ImbalancedChen.Part3CanonicalPlanarL2Unitary
import ImbalancedChen.Part3ActualCompletedEnergyResolvent

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Whole-upper-half-plane Hardy floor for arbitrary actual finite tensor sums,
then the actual completed first-gradient energy space. Fixed-x Hardy is
applied to the actual vertical finite sum, followed by genuine Fubini.
The weak resolvent has norm at most 4/5. No Gamma quotient claim is made.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualWholePlaneHardyFloorSourceOnly

open MeasureTheory Filter Set
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeakOperatorCore20261024zz
open MaassFiniteCoreResolventCoercivity20261025a MaassFiniteCoreL2Graph20261025a
open MaassFiniteCoreL2LinearOperator20261025a MaassFirstGradientWeakLimit20261025a
open ActualTensorGradientLinearMaps20261025a VerticalHardy20261024zz
open CanonicalPlanarL2UnitarySourceOnly MaassWeightedCoordinateL220261024zz
open ActualCompletedTensorEnergyForm20261025a ActualCompletedEnergyResolvent20261025a

/-- The actual vertical finite sum at a fixed horizontal coordinate. -/
def verticalSlice {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) (x y : ℝ) : ℂ :=
  finiteChartFunction s T (x, y)

private theorem verticalSlice_contDiff {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (x : ℝ) : ContDiff ℝ 1 (verticalSlice s T x) := by
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul ((T i).vertical_smooth.of_le (by norm_num))

private theorem verticalSlice_compact {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (x : ℝ) : HasCompactSupport (verticalSlice s T x) := by
  simpa only [verticalSlice, finiteChartFunction, Finset.sum_apply] using
    (HasCompactSupport.finset_sum (s := s)
      (fun i _ => (T i).vertical_compact.mul_left
        (f := fun _ : ℝ => (T i).horizontal x)))

/-- Every point below height zero has a common zero neighbourhood for the
finite family. This proves positive support for the sum itself. -/
private theorem verticalSlice_positive {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (x : ℝ) :
    tsupport (verticalSlice s T x) ⊆ Ioi (0 : ℝ) := by
  intro y hy
  by_contra hout
  have hall : ∀ᶠ t in nhds y, ∀ i ∈ s, (T i).vertical t = 0 := by
    apply (Filter.eventually_all_finset s).2
    intro i hi
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hm
    exact hout ((T i).vertical_positive hm)
  have hzero : verticalSlice s T x =ᶠ[nhds y] (fun _ => (0 : ℂ)) := by
    filter_upwards [hall] with t ht
    simp [verticalSlice, finiteChartFunction, ht]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hy

private theorem verticalSlice_deriv {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (x y : ℝ) :
    deriv (verticalSlice s T x) y = finiteGradient true s T (x, y) := by
  simpa only [chartFirstGradient, if_true, verticalSlice] using
    congrFun (chartFirstGradient_finiteChartFunction true s T) (x, y)

/-- Existing one-dimensional Hardy applied to the true vertical finite
sum. No separated-tensor estimate is substituted for this statement. -/
theorem verticalSlice_hardy {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (x : ℝ) :
    (1 / 4 : ℝ) * (∫ y : ℝ,
      ‖finiteChartFunction s T (x, y)‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) ≤
        ∫ y : ℝ, ‖finiteGradient true s T (x, y)‖ ^ 2 := by
  have h := vertical_hardy (verticalSlice s T x)
    (verticalSlice_contDiff s T x) (verticalSlice_compact s T x)
    (verticalSlice_positive s T x)
  simp_rw [verticalSlice_deriv] at h
  simpa only [verticalSlice] using h

def massFunction {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) (p : ℝ × ℝ) : ℝ :=
  ‖finiteChartFunction s T p‖ ^ 2 * (p.2⁻¹ : ℝ) ^ 2

private theorem forwardFunction_finiteCore {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) :
    forwardFunction (finiteCoreFunction s T) =
      fun p : ℝ × ℝ => (p.2⁻¹ : ℝ) • finiteChartFunction s T p := by
  have hpull : chartPullback (finiteCoreFunction s T) = finiteChartFunction s T := by
    change extendUpper (finiteCoreFunction s T) = finiteChartFunction s T
    exact extendUpper_finiteCoreFunction s T
  unfold forwardFunction
  rw [hpull]
  funext p
  by_cases hp : p ∈ upperChart
  · simp [unweightChart, hp]
  · have hzero : finiteChartFunction s T p = 0 := by
      have hv (i : ι) : (T i).vertical p.2 = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hp ((T i).vertical_positive h))
      simp [finiteChartFunction, hv]
    simp [unweightChart, hp, hzero]

private theorem forwardFunction_finiteCore_norm_sq {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (p : ℝ × ℝ) :
    ‖forwardFunction (finiteCoreFunction s T) p‖ ^ 2 = massFunction s T p := by
  rw [forwardFunction_finiteCore]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, massFunction]
  ring

/-- Real integrability is proved before applying Fubini. -/
theorem massFunction_integrable {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Integrable (massFunction s T) (volume : Measure (ℝ × ℝ)) := by
  have hlp := forwardFunction_memLp (finiteCoreFunction_memLp s T)
  exact ((memLp_two_iff_integrable_sq_norm hlp.aestronglyMeasurable).1 hlp).congr
    (Eventually.of_forall (forwardFunction_finiteCore_norm_sq s T))

private theorem integral_norm_sq_lp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- The finite-sum mass is the norm for the actual canonical hyperbolic
volume, with no separated-factor or diagonal-only simplification. -/
theorem finiteCoreL2_norm_sq_eq_mass {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) :
    ‖finiteCoreL2 s T‖ ^ 2 = ∫ p : ℝ × ℝ, massFunction s T p := by
  calc
    _ = ∫ z : UpperHalfPlane, ‖finiteCoreL2 s T z‖ ^ 2 := (integral_norm_sq_lp _ _).symm
    _ = ∫ z : UpperHalfPlane, ‖finiteCoreFunction s T z‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(finiteCoreFunction_memLp s T).coeFn_toLp] with z hz
      rw [hz]
    _ = ∫ p : ℝ × ℝ, ‖forwardFunction (finiteCoreFunction s T) p‖ ^ 2 :=
      canonicalL2_square_eq_unweight (finiteCoreFunction s T)
    _ = _ := integral_congr_ae
      (Eventually.of_forall (forwardFunction_finiteCore_norm_sq s T))

private theorem gradientL2_norm_sq_eq_integral {ι : Type*} (vertical : Bool)
    (s : Finset ι) (T : ι → CompactTensor) :
    ‖gradientL2 vertical s T‖ ^ 2 = ∫ p : ℝ × ℝ, ‖finiteGradient vertical s T p‖ ^ 2 := by
  calc
    _ = ∫ p : ℝ × ℝ, ‖gradientL2 vertical s T p‖ ^ 2 := (integral_norm_sq_lp _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(finiteGradient_memLp vertical s T).coeFn_toLp] with p hp
      rw [hp]

/-- Genuine whole-plane finite-sum Hardy, using Fubini on the actual
weighted mass and on the actual squared vertical finite gradient. -/
theorem finiteCore_vertical_hardy {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    (1 / 4 : ℝ) * ‖finiteCoreL2 s T‖ ^ 2 ≤ ‖gradientL2 true s T‖ ^ 2 := by
  have hm := massFunction_integrable s T
  have hglp := finiteGradient_memLp true s T
  have hg := (memLp_two_iff_integrable_sq_norm hglp.aestronglyMeasurable).1 hglp
  rw [finiteCoreL2_norm_sq_eq_mass, gradientL2_norm_sq_eq_integral]
  calc
    (1 / 4 : ℝ) * (∫ p : ℝ × ℝ, massFunction s T p) =
        ∫ x : ℝ, (1 / 4 : ℝ) * (∫ y : ℝ, massFunction s T (x, y)) := by
      rw [integral_const_mul, ← integral_prod _ hm]
    _ ≤ ∫ x : ℝ, ∫ y : ℝ, ‖finiteGradient true s T (x, y)‖ ^ 2 :=
      integral_mono (hm.integral_prod_left.const_mul (1 / 4 : ℝ))
        hg.integral_prod_left (fun x => verticalSlice_hardy s T x)
    _ = _ := (integral_prod _ hg).symm

theorem finiteCore_energy_hardy {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    (1 / 4 : ℝ) * ‖finiteCoreL2 s T‖ ^ 2 ≤
      ‖gradientL2 false s T‖ ^ 2 + ‖gradientL2 true s T‖ ^ 2 := by
  nlinarith [finiteCore_vertical_hardy s T, sq_nonneg ‖gradientL2 false s T‖]

theorem actualCore_vertical_hardy (u : actualTensorDomain) :
    (1 / 4 : ℝ) * ‖(u : HyperbolicL2)‖ ^ 2 ≤ ‖actualGradient true u‖ ^ 2 := by
  rcases actualTensorLaplacian_mem_graph u with ⟨n, T, hf, hg⟩
  have hu : u = ⟨finiteCoreL2 Finset.univ T, finiteCoreL2_mem_actualTensorDomain Finset.univ T⟩ :=
    Subtype.ext hf
  rw [hu, actualGradient_finiteCore]
  exact finiteCore_vertical_hardy Finset.univ T

/-- The actual completed first-gradient form inherits Hardy by dense core
range and closedness of the continuous norm inequality. -/
theorem completedEnergy_vertical_hardy (u : completedEnergy) :
    (1 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 ≤ ‖completedGradient true u‖ ^ 2 := by
  apply DenseRange.induction_on
    (p := fun v : completedEnergy =>
      (1 / 4 : ℝ) * ‖physicalProjection v‖ ^ 2 ≤ ‖completedGradient true v‖ ^ 2)
    coreEmbedding_denseRange u
  · exact isClosed_le (continuous_const.mul (physicalProjection.continuous.norm.pow 2))
      ((completedGradient true).continuous.norm.pow 2)
  · intro v
    rw [physicalProjection_coreEmbedding, completedGradient_coreEmbedding]
    exact actualCore_vertical_hardy v

theorem completedEnergy_hardy_floor (u : completedEnergy) :
    (1 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 ≤
      ‖completedGradient false u‖ ^ 2 + ‖completedGradient true u‖ ^ 2 := by
  nlinarith [completedEnergy_vertical_hardy u, sq_nonneg ‖completedGradient false u‖]

private theorem completedEnergy_norm_sq (u : completedEnergy) :
    ‖u‖ ^ 2 = ‖physicalProjection u‖ ^ 2 +
      ‖completedGradient false u‖ ^ 2 + ‖completedGradient true u‖ ^ 2 := by
  have h := congrArg Complex.re (completedEnergy_inner_coordinates u u)
  simpa only [Complex.add_re, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

/-- The whole-upper-half-plane energy controls physical mass by 5/4. -/
theorem completedEnergy_shifted_hardy_floor (u : completedEnergy) :
    (5 / 4 : ℝ) * ‖physicalProjection u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [completedEnergy_norm_sq]
  nlinarith [completedEnergy_hardy_floor u]

/-- Genuine improved norm bound for the already constructed whole-plane
Friedrichs weak resolvent R=p*p-adjoint. This is not a quotient bound. -/
theorem actualWeakResolvent_norm_le_four_fifths (f : HyperbolicL2) :
    ‖actualWeakResolvent f‖ ≤ (4 / 5 : ℝ) * ‖f‖ := by
  have hfloor := completedEnergy_shifted_hardy_floor (energyRieszSolution f)
  rw [← actualWeakResolvent_apply] at hfloor
  have hcs : ‖energyRieszSolution f‖ ^ 2 ≤ ‖f‖ * ‖actualWeakResolvent f‖ := by
    rw [← actualWeakResolvent_quadratic]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_cases hz : ‖actualWeakResolvent f‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖actualWeakResolvent f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply le_of_not_gt
    intro hlarge
    have hprod : 0 < ‖actualWeakResolvent f‖ *
        ((5 / 4 : ℝ) * ‖actualWeakResolvent f‖ - ‖f‖) :=
      mul_pos hp (by linarith)
    nlinarith

theorem actualWeakResolvent_opNorm_le_four_fifths :
    ‖actualWeakResolvent‖ ≤ (4 / 5 : ℝ) := by
  apply actualWeakResolvent.opNorm_le_bound (by norm_num)
  exact actualWeakResolvent_norm_le_four_fifths

end ImbalancedChen.Part3.ActualWholePlaneHardyFloorSourceOnly
