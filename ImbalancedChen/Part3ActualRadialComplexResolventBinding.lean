import ImbalancedChen.Part3ActualRadialShiftGreenBinding
import ImbalancedChen.Part3ComplexContractionResolvent
import ImbalancedChen.Part3ComplexResolventIdentities
import ImbalancedChen.Part3NegativeRealComplexResolvent

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The complex CFC resolvent is bound to the SAME actual native radial
Friedrichs operator constructed from the genuine radial energy completion.
Its two nonreal inverse directions, norm bound, adjoint relation and
resolvent identity are consumed at the actual radial R1.

At negative real spectral points, the independent generic real/complex
CFC bridge and the actual form-domain shift equivalence identify this
same complex resolvent with the literal real I/K Green integral on every
L2 forcing. This is the real anchor for subsequent order holomorphy;
no complex-order kernel continuation or Stone boundary limit is assumed.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
open ImbalancedChen.Part3.ComplexContractionResolvent20261025a
open ImbalancedChen.Part3.ComplexResolventIdentities20261025a
open ImbalancedChen.Part3.NegativeRealComplexResolvent20261025a
open ImbalancedChen.Part3.ActualGreenL2IntegralInverse20261025a

def actualRadialComplexResolvent (z : ℂ) : RadialL2 →L[ℂ] RadialL2 :=
  complexResolvent radialUnitShiftResolvent z

def actualRadialOrderResolvent (nu : ℂ) : RadialL2 →L[ℂ] RadialL2 :=
  actualRadialComplexResolvent (-(nu ^ 2))

theorem actualRadialComplexResolvent_native_graph_pair {z : ℂ} (hz : z.im ≠ 0)
    (F : RadialL2) :
    (actualRadialComplexResolvent z F, F + z • actualRadialComplexResolvent z F) ∈
      actualRadialFriedrichs.graph := by
  apply (actualRadialFriedrichs_graph_iff _ _).2
  exact complexResolvent_graph_pair radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint hz F

theorem actualRadialComplexResolvent_on_native_graph {z : ℂ} (hz : z.im ≠ 0)
    {u v : RadialL2} (huv : (u, v) ∈ actualRadialFriedrichs.graph) :
    actualRadialComplexResolvent z (v - z • u) = u :=
  complexResolvent_on_graph radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint hz
    ((actualRadialFriedrichs_graph_iff u v).1 huv)

theorem actualRadialComplexResolvent_norm_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖actualRadialComplexResolvent z‖ ≤ 1 / |z.im| :=
  complexResolvent_norm_le radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint hz

theorem actualRadialComplexResolvent_star (z : ℂ) :
    star (actualRadialComplexResolvent z) = actualRadialComplexResolvent (star z) :=
  complexResolvent_star radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint z

theorem actualRadialComplexResolvent_first_identity {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    actualRadialComplexResolvent z - actualRadialComplexResolvent w =
      (z - w) • (actualRadialComplexResolvent z * actualRadialComplexResolvent w) :=
  complexResolvent_first_identity radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint hz hw

/-- Actual negative-real spectral binding, requiring the proved genuine
kappa-to-one form-domain equivalence rather than a shift premise. -/
theorem actualRadialComplexResolvent_neg_kappa_sq (kappa : ℝ) (hkappa : 0 < kappa) :
    actualRadialComplexResolvent (-(kappa ^ 2 : ℂ)) =
      radialShiftedVariationalInverse kappa := by
  rw [actualRadialComplexResolvent,
    complexResolvent_neg_real radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint
      (kappa ^ 2), ← radialKappaFormInverse_eq_native_shiftedResolvent kappa hkappa]

theorem actualGreenL2Operator_eq_same_native_complex_resolvent {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    actualGreenL2Operator kappa hkappa hkappaUpper =
      actualRadialComplexResolvent (-(kappa ^ 2 : ℂ)) := by
  rw [actualRadialComplexResolvent_neg_kappa_sq kappa hkappa,
    actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper]

/-- Literal arbitrary-L2 I/K kernel integral = native (A+kappa²) inverse
in the same complex CFC family used away from the real spectrum. -/
theorem actualL2GreenIntegral_eq_same_native_complex_resolvent {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    actualL2GreenIntegral kappa F =ᵐ[(volume : Measure ℝ)]
      (actualRadialComplexResolvent (-(kappa ^ 2 : ℂ)) F : ℝ → ℂ) := by
  rw [actualRadialComplexResolvent_neg_kappa_sq kappa hkappa]
  exact actualL2GreenIntegral_eq_form_inverse hkappa hkappaUpper F

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
