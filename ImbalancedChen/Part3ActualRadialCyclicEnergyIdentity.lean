import ImbalancedChen.Part3ActualRadialScalarEndpointAtoms
import ImbalancedChen.Part3CyclicCoordinateQuadraticIntegral
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual radial closed-form spectral energy on constructed Riesz lifts.
These are elements of the original PiLp2 energy completion, with the
original physical/derivative/exponential coordinates. The exact t and
t(1-t) spectral energy identities hold for arbitrary scalar L2 vectors.
Riesz lifts have dense range in the actual energy norm. The full maximal
sqrt(lambda) domain equivalence still requires weighted completion and
the reverse physical-range argument; neither is assumed here.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set MeasureTheory
open GenericHilbertAdjointSquare20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventCyclicIntertwining20261025a
open CyclicCoordinateQuadraticIntegral20261025a

abbrev RadialScalarL2 (F : RadialL2) :=
  ScalarL2 radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F

def radialCyclicEnergyLift (F : RadialL2) :
    RadialScalarL2 F →L[ℂ] radialClosedEnergyDomain 1 :=
  (radialFormRieszSolution 1).comp
    (cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F)

theorem radialCyclicEnergyLift_physical (F : RadialL2) (ξ : RadialScalarL2 F) :
    radialPhysicalEmbedding 1 (radialCyclicEnergyLift F ξ) =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F
        (coordinateMultiplier radialUnitShiftResolvent
          radialUnitShiftResolvent_selfAdjoint F ξ) := by
  exact (cyclicExtension_intertwine radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint F ξ).symm

theorem radialCyclicEnergyLift_norm_sq (F : RadialL2) (ξ : RadialScalarL2 F) :
    ‖radialCyclicEnergyLift F ξ‖ ^ 2 =
      ∫ t : RadialBoundedSpectrum, (t : ℝ) * ‖ξ t‖ ^ 2
        ∂radialBoundedScalarMeasure F := by
  let U := cyclicIsometry radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F
  calc
    _ = (inner ℂ (U ξ) (radialUnitShiftResolvent (U ξ))).re :=
      (adjointSquare_quadratic (radialPhysicalEmbedding 1) (U ξ)).symm
    _ = (inner ℂ (U ξ) (U (coordinateMultiplier radialUnitShiftResolvent
        radialUnitShiftResolvent_selfAdjoint F ξ))).re := by
      rw [cyclicExtension_intertwine]
    _ = (inner ℂ ξ (coordinateMultiplier radialUnitShiftResolvent
        radialUnitShiftResolvent_selfAdjoint F ξ)).re := by rw [U.inner_map_map]
    _ = _ := coordinate_quadratic_integral radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint F ξ

theorem radialCyclicEnergyLift_physical_norm_sq (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    ‖radialPhysicalEmbedding 1 (radialCyclicEnergyLift F ξ)‖ ^ 2 =
      ∫ t : RadialBoundedSpectrum, (t : ℝ) ^ 2 * ‖ξ t‖ ^ 2
        ∂radialBoundedScalarMeasure F := by
  rw [radialCyclicEnergyLift_physical, cyclicExtension_norm]
  exact coordinate_square_integral radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint F ξ

/-- Exact unshifted derivative-plus-exponential energy. This is already
lambda times the squared physical coordinate t*xi, before completion. -/
theorem radialCyclicEnergyLift_unshifted_energy (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    ‖radialClosedDerivative 1 (radialCyclicEnergyLift F ξ)‖ ^ 2 +
      ‖radialClosedExponential 1 (radialCyclicEnergyLift F ξ)‖ ^ 2 =
        ∫ t : RadialBoundedSpectrum, ((t : ℝ) - (t : ℝ) ^ 2) * ‖ξ t‖ ^ 2
          ∂radialBoundedScalarMeasure F := by
  have he := congrArg Complex.re (radialClosedEnergy_inner 1 (by norm_num)
    (radialCyclicEnergyLift F ξ) (radialCyclicEnergyLift F ξ))
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    Complex.ofReal_re] at he
  norm_num at he
  have hI := integral_sub
    (coordinate_quadratic_integrable radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint F ξ)
    (coordinate_square_integrable radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint F ξ)
  simp_rw [← sub_mul] at hI
  rw [hI, ← radialCyclicEnergyLift_norm_sq,
    ← radialCyclicEnergyLift_physical_norm_sq]
  linarith

theorem radialCyclicEnergyLift_lambda_energy (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    ‖radialClosedDerivative 1 (radialCyclicEnergyLift F ξ)‖ ^ 2 +
      ‖radialClosedExponential 1 (radialCyclicEnergyLift F ξ)‖ ^ 2 =
        ∫ t : RadialBoundedSpectrum, radialSpectralLambda t *
          ‖((t : ℝ) : ℂ) * ξ t‖ ^ 2 ∂radialBoundedScalarMeasure F := by
  rw [radialCyclicEnergyLift_unshifted_energy]
  apply integral_congr_ae
  filter_upwards [radialBoundedScalarMeasure_ae_strict_unitInterval F] with t ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    radialSpectralLambda]
  field_simp [ne_of_gt ht.1]
  <;> ring

/-- Approximation in the actual CLOSED energy norm, not merely physical L2. -/
theorem radialFormRieszSolution_one_denseRange :
    DenseRange (radialFormRieszSolution 1) :=
  rieszLift_denseRange (radialPhysicalEmbedding 1)
    (radialPhysicalEmbedding_injective 1 (by norm_num))

theorem radialClosedEnergyDomain_approx_by_native_operator_domain
    (e : radialClosedEnergyDomain 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : RadialL2, ‖radialFormRieszSolution 1 F - e‖ < ε ∧
      radialPhysicalEmbedding 1 (radialFormRieszSolution 1 F) ∈
        actualRadialFriedrichs.domain := by
  obtain ⟨F, hF⟩ := radialFormRieszSolution_one_denseRange.exists_dist_lt e hε
  refine ⟨F, ?_, ?_⟩
  · simpa only [dist_eq_norm, norm_sub_rev] using hF
  · exact LinearPMap.mem_domain_of_mem_graph (actualRadialFriedrichs_resolvent_pair F)

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
