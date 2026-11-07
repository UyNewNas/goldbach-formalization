import ImbalancedChen.Part3RadialShiftEnergyEquivalence
import ImbalancedChen.Part3ActualRadialFriedrichsOperator
import ImbalancedChen.Part3ActualGreenL2IntegralInverse
import ImbalancedChen.Part3PositiveContractionResolventCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual kappa-form inverse belongs to the native kappa=1 radial
Friedrichs graph: (R_kappa F,F-kappa² R_kappa F) is a true native graph
pair. The proof transports both solution and test vectors through the
proved coordinate-scaling equivalence of the actual closed form domains.

It follows that R_kappa is exactly the positive-real CFC shifted inverse
constructed from the actual R_1. The literal real I/K Green integral and
its native L2 operator are then bound to this SAME native operator and
CFC family. No form-domain equality, shift relation or inverse is assumed.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
open ImbalancedChen.Part3.ActualGreenL2IntegralInverse20261025a

theorem radialUnitShiftResolvent_nonneg : 0 ≤ radialUnitShiftResolvent :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).2 radialUnitShiftResolvent_positive

/-- The kappa-form solution solves the native (A+kappa²) equation.
Both energy-domain joins are the actual proved coordinate transports. -/
theorem actualRadialFriedrichs_kappa_form_pair (kappa : ℝ) (hkappa : 0 < kappa)
    (F : RadialL2) :
    (radialShiftedVariationalInverse kappa F,
      F - (kappa ^ 2 : ℂ) • radialShiftedVariationalInverse kappa F) ∈
        actualRadialFriedrichs.graph := by
  let e := radialFormRieszSolution kappa F
  let e1 := radialShiftFormTransport kappa 1 hkappa e
  apply (actualRadialFriedrichs_graph_iff_weak_radial_energy _ _).2
  refine ⟨e1, ?_, ?_⟩
  · exact radialShiftFormTransport_physical kappa 1 hkappa (by norm_num) e
  · intro d
    let dk := radialShiftFormTransport 1 kappa (by norm_num) d
    have h := ContinuousLinearMap.adjoint_inner_right
      (radialPhysicalEmbedding kappa) dk F
    change inner ℂ dk e = inner ℂ (radialPhysicalEmbedding kappa dk) F at h
    rw [radialClosedEnergy_inner kappa hkappa] at h
    dsimp only [dk] at h
    rw [radialShiftFormTransport_physical 1 kappa (by norm_num) hkappa d,
      radialShiftFormTransport_derivative 1 kappa (by norm_num) d,
      radialShiftFormTransport_exponential 1 kappa (by norm_num) d] at h
    dsimp only [e1]
    rw [radialShiftFormTransport_derivative kappa 1 hkappa e,
      radialShiftFormTransport_exponential kappa 1 hkappa e,
      inner_sub_right, inner_smul_right]
    change inner ℂ (radialClosedDerivative 1 d) (radialClosedDerivative kappa e) +
      inner ℂ (radialClosedExponential 1 d) (radialClosedExponential kappa e) =
        inner ℂ (radialPhysicalEmbedding 1 d) F -
          (kappa ^ 2 : ℂ) * inner ℂ (radialPhysicalEmbedding 1 d)
            (radialPhysicalEmbedding kappa e)
    linear_combination h

/-- Equality of the independently constructed actual form inverse with
the actual native positive-shift CFC. -/
theorem radialKappaFormInverse_eq_native_shiftedResolvent
    (kappa : ℝ) (hkappa : 0 < kappa) :
    radialShiftedVariationalInverse kappa =
      shiftedResolvent radialUnitShiftResolvent (kappa ^ 2) := by
  ext F
  have hpair := actualRadialFriedrichs_kappa_form_pair kappa hkappa F
  have hg : (radialShiftedVariationalInverse kappa F,
      F - (kappa ^ 2 : ℂ) • radialShiftedVariationalInverse kappa F) ∈
        resolventGraph radialUnitShiftResolvent :=
    (actualRadialFriedrichs_graph_iff _ _).1 hpair
  have h := shiftedResolvent_on_graph radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_nonneg
    radialUnitShiftResolvent_opNorm_le_one (sq_pos_of_pos hkappa) hg
  have he : (kappa ^ 2 : ℂ) • radialShiftedVariationalInverse kappa F +
      (F - (kappa ^ 2 : ℂ) • radialShiftedVariationalInverse kappa F) = F := by abel
  rw [he] at h
  exact h.symm

theorem actualGreenL2Operator_eq_native_shiftedResolvent {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    actualGreenL2Operator kappa hkappa hkappaUpper =
      shiftedResolvent radialUnitShiftResolvent (kappa ^ 2) := by
  rw [actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper,
    radialKappaFormInverse_eq_native_shiftedResolvent kappa hkappa]

/-- The original literal real I/K integral, on arbitrary L2 forcing,
is the actual native radial CFC shifted inverse, almost everywhere. -/
theorem actualL2GreenIntegral_eq_native_shiftedResolvent {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    actualL2GreenIntegral kappa F =ᵐ[(volume : Measure ℝ)]
      (shiftedResolvent radialUnitShiftResolvent (kappa ^ 2) F : ℝ → ℂ) := by
  rw [← radialKappaFormInverse_eq_native_shiftedResolvent kappa hkappa]
  exact actualL2GreenIntegral_eq_form_inverse hkappa hkappaUpper F

theorem actualGreenL2Operator_native_graph_pair {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    (actualGreenL2Operator kappa hkappa hkappaUpper F,
      F - (kappa ^ 2 : ℂ) • actualGreenL2Operator kappa hkappa hkappaUpper F) ∈
        actualRadialFriedrichs.graph := by
  rw [actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper]
  exact actualRadialFriedrichs_kappa_form_pair kappa hkappa F

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
