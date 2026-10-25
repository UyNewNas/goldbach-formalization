import ImbalancedChen.Part3ActualRadialScalarEndpointAtoms
import ImbalancedChen.Part3ActualRadialComplexResolventBinding
import ImbalancedChen.Part3GenericComplexResolventStone
import ImbalancedChen.Part3ActualGreenResolventContinuation

/-!
# Actual radial compact-test scalar measure and half-endpoint Stone caller

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every operator and measure is the native radial one already constructed
from the actual energy form. Stone's half-atoms remain present. No KL
density, boundary exchange, positive atomlessness or Plancherel identity
is assumed. These are supplied only by later actual boundary/measure work.
-/

namespace ImbalancedChen.Part3.ActualRadialCompactScalarStone20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a
open GenericResolventUnboundedScalarMeasure20261025a
open GenericComplexResolventStone20261025a ScalarCauchyResolventInversion20261025a

def compactRadialScalarMeasure (F : RadialTest) : Measure ℝ :=
  radialUnboundedScalarMeasure (radialCoreL2 F)

instance compactRadialScalarMeasure_finite (F : RadialTest) :
    IsFiniteMeasure (compactRadialScalarMeasure F) := by
  unfold compactRadialScalarMeasure
  infer_instance

theorem actual_radial_unbounded_measure_eq_generic (F : RadialL2) :
    radialUnboundedScalarMeasure F =
      unboundedScalarMeasure radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F := rfl

def radialDiagonalMoment (F : RadialL2) (z : ℂ) : ℂ :=
  inner ℂ F (actualRadialComplexResolvent z F)

def radialCompactStoneInterval (F : RadialTest) (a b epsilon : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ x in a..b,
    (radialDiagonalMoment (radialCoreL2 F) ((x : ℂ) + (epsilon : ℂ) * Complex.I)).im

theorem radialDiagonalMoment_conjugate (F : RadialL2) (z : ℂ) :
    radialDiagonalMoment F (star z) = star (radialDiagonalMoment F z) := by
  unfold radialDiagonalMoment
  rw [← actualRadialComplexResolvent_star z, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (actualRadialComplexResolvent z F) F).symm

theorem radialDiagonalMoment_cauchy (F : RadialL2) {z : ℂ} (hz : z.im ≠ 0) :
    radialDiagonalMoment F z = cauchyResolvent (radialUnboundedScalarMeasure F) z := by
  rw [actual_radial_unbounded_measure_eq_generic]
  exact complexResolvent_scalarCoefficient_cauchy radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_nonneg
    radialUnitShiftResolvent_opNorm_le_one radialUnitShiftResolvent_injective F hz

/-- Half-atoms at positive interval endpoints have not been discarded. -/
theorem compactRadialScalarMeasure_Stone_interval (F : RadialTest)
    {a b : ℝ} (hab : a < b) :
    Tendsto (radialCompactStoneInterval F a b) (nhdsWithin 0 (Ioi 0))
      (nhds ((compactRadialScalarMeasure F).real (Ioo a b) +
        ((compactRadialScalarMeasure F).real {a} +
          (compactRadialScalarMeasure F).real {b}) / 2)) := by
  simpa only [radialCompactStoneInterval, radialDiagonalMoment, actualRadialComplexResolvent,
    diagonalResolventIntervalMass, compactRadialScalarMeasure,
    actual_radial_unbounded_measure_eq_generic] using
      diagonalResolvent_Stone_interval radialUnitShiftResolvent
        radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_nonneg
        radialUnitShiftResolvent_opNorm_le_one radialUnitShiftResolvent_injective
        (radialCoreL2 F) hab

theorem compactRadialScalarMeasure_nonpositive_mass (F : RadialTest) :
    compactRadialScalarMeasure F (Iic 0) = 0 :=
  radialUnboundedScalarMeasure_Iic_zero (radialCoreL2 F)

theorem compactRadialScalarMeasure_zero_atom (F : RadialTest) :
    compactRadialScalarMeasure F ({0} : Set ℝ) = 0 :=
  radialUnboundedScalarMeasure_singleton_zero (radialCoreL2 F)

/-- The full native physical norm already lies on the positive lambda axis;
the KL density of that actual positive measure is not inferred here. -/
theorem compactRadialScalarMeasure_positive_mass (F : RadialTest) :
    compactRadialScalarMeasure F (Ioi 0) = ENNReal.ofReal (‖radialCoreL2 F‖ ^ 2) :=
  radialUnboundedScalarMeasure_positive_mass (radialCoreL2 F)

end
end ImbalancedChen.Part3.ActualRadialCompactScalarStone20261025a
