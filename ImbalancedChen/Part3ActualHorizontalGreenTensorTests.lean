import ImbalancedChen.Part3ActualWholePlaneSpectralFloor
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Actual horizontal Green tests transported through the true /y unitary.
For a completed input with horizontal gradient zero, its upper-supported
planar image is orthogonal to every actual horizontal compact primitive
derivative times every smooth compact positive-height vertical factor.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualHorizontalGreenTensorTestsSourceOnly

open MeasureTheory Filter Set
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeakOperatorCore20261024zz
open MaassFiniteCoreResolventCoercivity20261025a MaassFiniteCoreL2Graph20261025a
open MaassFirstGradientWeakLimit20261025a ActualCompletedTensorEnergyForm20261025a
open CanonicalPlanarL2UnitarySourceOnly ActualWholePlaneSpectralFloorSourceOnly

/-- The apparent division singularity is removed by actual positive
support. This proves the genuine C2 property needed by CompactTensor. -/
theorem divideHeight_contDiff {v : ℝ → ℂ} (hv : ContDiff ℝ 2 v)
    (hpos : tsupport v ⊆ Ioi (0 : ℝ)) : ContDiff ℝ 2 (divideHeight v) := by
  apply contDiff_iff_contDiffAt.2
  intro y
  by_cases hy : y = 0
  · subst y
    have hout : (0 : ℝ) ∉ tsupport v := fun h => (lt_irrefl (0 : ℝ)) (hpos h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hout
    have hd : divideHeight v =ᶠ[nhds (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [he] with t ht
      simp [divideHeight, ht]
    exact contDiffAt_const.congr_of_eventuallyEq hd
  · have hi : ContDiffAt ℝ 2 (fun t : ℝ => t⁻¹) y := contDiffAt_id.inv hy
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hi).mul hv.contDiffAt

/-- The actual canonical Green tensor uses vertical v/y so that dividing
its lifted derivative by y leaves precisely h'(x)*v(y) in planar L2. -/
def primitiveGreenTensor (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hpos : tsupport v ⊆ Ioi (0 : ℝ)) : CompactTensor where
  horizontal := h
  vertical := divideHeight v
  horizontal_smooth := hh
  vertical_smooth := divideHeight_contDiff hv hpos
  horizontal_compact := hhc
  vertical_compact := hasCompactSupport_divideHeight v hvc
  vertical_positive := tsupport_mul_subset_right.trans hpos

private theorem first_continuous {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) :
    Continuous (deriv h) := by
  have h1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  exact h1.continuous_deriv_one

/-- Actual quotient L2 class of the derivative tensor on the plane. -/
def derivativeTensorL2 (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : Continuous v) (hvc : HasCompactSupport v) : PlaneL2 :=
  (separated_plane_memLp (deriv h) v (first_continuous hh) hv hhc.deriv hvc).toLp
    (tensorFunction (deriv h) v)

theorem derivativeTensorL2_coe_ae (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : Continuous v) (hvc : HasCompactSupport v) :
    (derivativeTensorL2 h v hh hhc hv hvc : ℝ × ℝ → ℂ) =ᵐ[volume]
      tensorFunction (deriv h) v :=
  (separated_plane_memLp (deriv h) v (first_continuous hh) hv hhc.deriv hvc).coeFn_toLp

private theorem forwardFunction_lifted_primitive (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hpos : tsupport v ⊆ Ioi (0 : ℝ)) (p : ℝ × ℝ) :
    forwardFunction (heightSquaredLift (tensorGradient false
      (primitiveGreenTensor h v hh hhc hv hvc hpos))) p = tensorFunction (deriv h) v p := by
  by_cases hp : p ∈ upperChart
  · have hy : p.2 ≠ 0 := ne_of_gt hp
    have hyc : (p.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
    simp only [forwardFunction, unweightChart, chartPullback, dif_pos hp,
      heightSquaredLift, tensorGradient, if_false, tensorDx, primitiveGreenTensor,
      tensorFunction, Complex.measurableEquivRealProd_apply, Complex.real_smul,
      divideHeight, Complex.ofReal_inv]
    field_simp [hyc]
    <;> ring
  · have hvzero : v p.2 = 0 := image_eq_zero_of_notMem_tsupport
      (fun hvp => hp (hpos hvp))
    simp [forwardFunction, unweightChart, hp, tensorFunction, hvzero]

/-- Exact unitary image of the actual canonical density-cancelling Green
vector, with all height powers and the actual /y normalization retained. -/
theorem forwardL2_lifted_primitive (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hpos : tsupport v ⊆ Ioi (0 : ℝ)) :
    forwardL2 (liftedGradientL2 false (primitiveGreenTensor h v hh hhc hv hvc hpos)) =
      derivativeTensorL2 h v hh hhc hv.continuous hvc := by
  apply Lp.ext
  have hlift := (liftedGradient_memLp false
    (primitiveGreenTensor h v hh hhc hv hvc hpos)).coeFn_toLp
  have hc := forwardFunction_congr_ae hlift
  filter_upwards [forwardL2_coe_ae
    (liftedGradientL2 false (primitiveGreenTensor h v hh hhc hv hvc hpos)), hc,
    derivativeTensorL2_coe_ae h v hh hhc hv.continuous hvc] with p hp hc' hd
  rw [hp, hc', hd, forwardFunction_lifted_primitive]

/-- The actual supported planar image annihilates every compact primitive
horizontal derivative tensor. No hypothetical weak-gradient identity or
planar test representation is supplied as a premise. -/
theorem horizontal_zero_derivative_tensor_pairing (u : completedEnergy)
    (hx : completedGradient false u = 0) (h v : ℝ → ℂ) (hh : ContDiff ℝ 2 h)
    (hhc : HasCompactSupport h) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hpos : tsupport v ⊆ Ioi (0 : ℝ)) :
    inner ℂ (forwardL2 (physicalProjection u))
      (derivativeTensorL2 h v hh hhc hv.continuous hvc) = 0 := by
  have hgreen := horizontal_zero_actual_green_tests u hx
    (primitiveGreenTensor h v hh hhc hv hvc hpos)
  have hinner := canonicalPlanarUnitary.inner_map_map (physicalProjection u)
    (liftedGradientL2 false (primitiveGreenTensor h v hh hhc hv hvc hpos))
  change inner ℂ (forwardL2 (physicalProjection u))
    (forwardL2 (liftedGradientL2 false (primitiveGreenTensor h v hh hhc hv hvc hpos))) =
      inner ℂ (physicalProjection u)
        (liftedGradientL2 false (primitiveGreenTensor h v hh hhc hv hvc hpos)) at hinner
  rw [forwardL2_lifted_primitive, hgreen] at hinner
  exact hinner

end ImbalancedChen.Part3.ActualHorizontalGreenTensorTestsSourceOnly
