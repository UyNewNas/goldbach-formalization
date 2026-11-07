import ImbalancedChen.Part3ActualKLCoordinateMeasures
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
CODE_ONLY / SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual available radial Green normalization permits kappa=1/2.
Its real KL resolvent coordinate is (1/4+tau^2)^(-1), bounded by four
and injective on the actual positive support of tauMeasure. The explicit
measurable inverse sqrt(t^(-1)-1/4) proves that EVERY measurable raw-tau
set is a coordinate pullback modulo the actual measure. No spectrum,
operator intertwining, indicator invariance or surjectivity is assumed.
-/

namespace ImbalancedChen.Part3.ActualKLResolventCoordinate20261025a

noncomputable section
open Set MeasureTheory
open ActualKLCoordinateMeasures20261025a

def klResolventCoordinate (tau : ℝ) : ℝ := ((1 / 4 : ℝ) + tau ^ 2)⁻¹

def klInverseCoordinate (t : ℝ) : ℝ := Real.sqrt (t⁻¹ - (1 / 4 : ℝ))

theorem klDenominator_pos (tau : ℝ) : 0 < (1 / 4 : ℝ) + tau ^ 2 := by
  nlinarith [sq_nonneg tau]

theorem klResolventCoordinate_continuous : Continuous klResolventCoordinate :=
  (continuous_const.add (continuous_id.pow 2)).inv₀ (fun tau => (klDenominator_pos tau).ne')

theorem klInverseCoordinate_measurable : Measurable klInverseCoordinate := by
  unfold klInverseCoordinate
  fun_prop

theorem klResolventCoordinate_pos (tau : ℝ) : 0 < klResolventCoordinate tau :=
  inv_pos.mpr (klDenominator_pos tau)

theorem klResolventCoordinate_le_four (tau : ℝ) : klResolventCoordinate tau ≤ 4 := by
  have h : (1 : ℝ) * ((1 / 4 : ℝ) + tau ^ 2)⁻¹ ≤ 4 :=
    (mul_inv_le_iff₀ (klDenominator_pos tau)).mpr (by nlinarith [sq_nonneg tau])
  simpa only [one_mul, klResolventCoordinate] using h

theorem klResolventCoordinate_lt_four {tau : ℝ} (htau : 0 < tau) :
    klResolventCoordinate tau < 4 := by
  have h : (1 : ℝ) * ((1 / 4 : ℝ) + tau ^ 2)⁻¹ < 4 :=
    (mul_inv_lt_iff₀ (klDenominator_pos tau)).mpr (by nlinarith [sq_pos_of_pos htau])
  simpa only [one_mul, klResolventCoordinate] using h

theorem klInverseCoordinate_leftInverse {tau : ℝ} (htau : 0 ≤ tau) :
    klInverseCoordinate (klResolventCoordinate tau) = tau := by
  unfold klInverseCoordinate klResolventCoordinate
  rw [inv_inv, show ((1 / 4 : ℝ) + tau ^ 2) - 1 / 4 = tau ^ 2 by ring]
  exact Real.sqrt_sq htau

theorem klResolventCoordinate_injOn_positive :
    Set.InjOn klResolventCoordinate (Ioi (0 : ℝ)) := by
  intro tau htau sigma hsigma heq
  calc
    tau = klInverseCoordinate (klResolventCoordinate tau) :=
      (klInverseCoordinate_leftInverse htau.le).symm
    _ = klInverseCoordinate (klResolventCoordinate sigma) := congrArg klInverseCoordinate heq
    _ = sigma := klInverseCoordinate_leftInverse hsigma.le

/-- The support condition comes from the literal withDensity/restrict
definition of the actual raw measure, rather than an extra hypothesis. -/
theorem tauMeasure_positive_ae : ∀ᵐ tau : ℝ ∂tauMeasure, 0 < tau := by
  change ∀ᵐ tau : ℝ ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun tau => ENNReal.ofReal (tauDensity tau))), 0 < tau
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)

theorem klResolventCoordinate_mem_Ioo_ae :
    ∀ᵐ tau : ℝ ∂tauMeasure, klResolventCoordinate tau ∈ Ioo (0 : ℝ) 4 :=
  tauMeasure_positive_ae.mono (fun tau htau =>
    ⟨klResolventCoordinate_pos tau, klResolventCoordinate_lt_four htau⟩)

/-- Actual coordinate valued in a fixed compact real set, including its
null boundary. This total map needs no support assumption to be defined. -/
def klCompactCoordinate (tau : ℝ) : Icc (0 : ℝ) 4 :=
  ⟨klResolventCoordinate tau,
    (klResolventCoordinate_pos tau).le, klResolventCoordinate_le_four tau⟩

theorem klCompactCoordinate_continuous : Continuous klCompactCoordinate :=
  klResolventCoordinate_continuous.subtype_mk _

theorem klCompactCoordinate_measurable : Measurable klCompactCoordinate :=
  klCompactCoordinate_continuous.measurable

def klCompactInverse (t : Icc (0 : ℝ) 4) : ℝ := klInverseCoordinate (t : ℝ)

theorem klCompactInverse_measurable : Measurable klCompactInverse :=
  klInverseCoordinate_measurable.comp measurable_subtype_coe

/-- The inverse law is derived on the literal actual measure; it is not
an input to the subsequent coordinate transport theorem. -/
theorem klCompactInverse_comp_ae :
    (fun tau : ℝ => klCompactInverse (klCompactCoordinate tau)) =ᵐ[tauMeasure] id :=
  tauMeasure_positive_ae.mono (fun _ htau => klInverseCoordinate_leftInverse htau.le)

/-- An explicit set in coordinate space representing any raw-tau set. -/
def coordinateBorelSet (B : Set ℝ) : Set ℝ := klInverseCoordinate ⁻¹' B

theorem coordinateBorelSet_measurable {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (coordinateBorelSet B) :=
  hB.preimage klInverseCoordinate_measurable

theorem coordinateBorelSet_pullback_ae (B : Set ℝ) :
    ∀ᵐ tau : ℝ ∂tauMeasure,
      klResolventCoordinate tau ∈ coordinateBorelSet B ↔ tau ∈ B := by
  filter_upwards [tauMeasure_positive_ae] with tau htau
  change klInverseCoordinate (klResolventCoordinate tau) ∈ B ↔ tau ∈ B
  rw [klInverseCoordinate_leftInverse htau.le]

/-- Literal indicator equality on every actual L² representative follows
from the proved support and inverse, with no indicator-invariance premise. -/
theorem indicator_coordinate_pullback_ae (B : Set ℝ) (f : ℝ → ℂ) :
    B.indicator f =ᵐ[tauMeasure]
      (klResolventCoordinate ⁻¹' coordinateBorelSet B).indicator f := by
  filter_upwards [coordinateBorelSet_pullback_ae B] with tau htau
  by_cases hB : tau ∈ B
  · rw [Set.indicator_of_mem hB, Set.indicator_of_mem (htau.mpr hB)]
  · rw [Set.indicator_of_notMem hB,
      Set.indicator_of_notMem (fun h => hB (htau.mp h))]

end
end ImbalancedChen.Part3.ActualKLResolventCoordinate20261025a
