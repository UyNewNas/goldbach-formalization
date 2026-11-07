import ImbalancedChen.Part3ActualKLCoordinateMeasures
import ImbalancedChen.Part3ActualKLCoreTransform
import ImbalancedChen.Part3ActualKLResolventCoordinate
import ImbalancedChen.Part3MeasurableCoordinateIndicatorTransport

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
The actual raw KL space is kept with its original tauMeasure. The compact
unit-shift coordinate (1+tau^2)^(-1) and its actual measurable inverse
reuse the existing compact-coordinate multiplication construction. The
intermediate pushforward is only a coordinate presentation; the output
operators and representative identities remain on the original RawTauL2.
-/

namespace ImbalancedChen.Part3.ActualKLCompactMultiplier20261026a

noncomputable section
open Set MeasureTheory Filter Topology
open ActualKLCoordinateMeasures20261025a ActualKLCoreTransform20261025a
open ActualKLResolventCoordinate20261025a
open MeasurableCoordinateIndicatorTransport20261025a
open CompactCoordinateIndicatorInvariance20261025a

abbrev UnitCoordinateSpace := Icc (0 : ℝ) 1

def rawUnitCoordinate (tau : ℝ) : UnitCoordinateSpace :=
  ⟨(1+tau^2)⁻¹, (inv_pos.mpr (by positivity : 0 < 1+tau^2)).le,
    by
      have h : (1 : ℝ) ≤ 1+tau^2 := le_add_of_nonneg_right (sq_nonneg tau)
      simpa only [one_div, inv_one] using (one_div_le_one_div_of_le zero_lt_one h)⟩

theorem rawUnitCoordinate_pos (tau : ℝ) : 0 < (rawUnitCoordinate tau : ℝ) :=
  inv_pos.mpr (by positivity)

theorem rawUnitCoordinate_continuous : Continuous rawUnitCoordinate :=
  ((continuous_const.add (continuous_id.pow 2)).inv₀
    (fun tau => ne_of_gt (by positivity : 0 < 1+tau^2))).subtype_mk _

def rawUnitInverse (x : UnitCoordinateSpace) : ℝ := Real.sqrt ((x : ℝ)⁻¹-1)

theorem rawUnitInverse_measurable : Measurable rawUnitInverse := by
  unfold rawUnitInverse
  fun_prop

theorem rawUnitInverse_comp_ae :
    (fun tau => rawUnitInverse (rawUnitCoordinate tau)) =ᵐ[tauMeasure] id := by
  filter_upwards [tauMeasure_positive_ae] with tau htau
  change Real.sqrt (((1+tau^2)⁻¹)⁻¹-1) = tau
  rw [inv_inv, show (1+tau^2)-1 = tau^2 by ring, Real.sqrt_sq htau.le]

abbrev compactTauMeasure : Measure UnitCoordinateSpace := tauMeasure.map rawUnitCoordinate
abbrev CompactTauL2 := Lp ℂ 2 compactTauMeasure

/-- This unitary is just the explicit coordinate change of the fixed raw
measure, not a replacement for the actual KL transform. -/
def compactRawUnitary : CompactTauL2 ≃ₗᵢ[ℂ] RawTauL2 :=
  LinearIsometryEquiv.ofSurjective
    (coordinatePullback tauMeasure rawUnitCoordinate rawUnitCoordinate_continuous.measurable)
    (coordinatePullback_surjective tauMeasure rawUnitCoordinate rawUnitCoordinate_continuous.measurable
      rawUnitInverse rawUnitInverse_measurable rawUnitInverse_comp_ae)

theorem compactRawUnitary_coe_ae (u : CompactTauL2) :
    compactRawUnitary u =ᵐ[tauMeasure] (fun tau => u (rawUnitCoordinate tau)) :=
  coordinatePullback_coe_ae tauMeasure rawUnitCoordinate rawUnitCoordinate_continuous.measurable u

theorem compactRawUnitary_symm_coe_ae (u : RawTauL2) :
    (fun tau => (compactRawUnitary.symm u) (rawUnitCoordinate tau)) =ᵐ[tauMeasure] u := by
  have h := compactRawUnitary_coe_ae (compactRawUnitary.symm u)
  rw [compactRawUnitary.apply_symm_apply] at h
  exact h.symm

def rawCompactMultiply (φ : C(UnitCoordinateSpace, ℝ)) (u : RawTauL2) : RawTauL2 :=
  compactRawUnitary (continuousMultiply compactTauMeasure φ (compactRawUnitary.symm u))

theorem rawCompactMultiply_coe_ae (φ : C(UnitCoordinateSpace, ℝ)) (u : RawTauL2) :
    rawCompactMultiply φ u =ᵐ[tauMeasure] (fun tau => φ (rawUnitCoordinate tau) • u tau) := by
  have hlocal := ae_of_ae_map rawUnitCoordinate_continuous.measurable.aemeasurable
    (continuousMultiply_coe_ae compactTauMeasure φ (compactRawUnitary.symm u))
  filter_upwards [compactRawUnitary_coe_ae
    (continuousMultiply compactTauMeasure φ (compactRawUnitary.symm u)),
    hlocal, compactRawUnitary_symm_coe_ae u] with tau hleft hmiddle hright
  exact hleft.trans (hmiddle.trans (congrArg (fun v : ℂ => φ (rawUnitCoordinate tau) • v) hright))

theorem rawCompactMultiply_norm_le (φ : C(UnitCoordinateSpace, ℝ)) (u : RawTauL2) :
    ‖rawCompactMultiply φ u‖ ≤ ‖φ‖ * ‖u‖ := by
  rw [rawCompactMultiply, compactRawUnitary.norm_map]
  exact (continuousMultiply_norm_le compactTauMeasure φ _).trans_eq
    (congrArg (fun r : ℝ => ‖φ‖*r) (compactRawUnitary.symm.norm_map u))

theorem rawCompactMultiply_const (c : ℝ) (u : RawTauL2) :
    rawCompactMultiply (ContinuousMap.const UnitCoordinateSpace c) u = c • u := by
  unfold rawCompactMultiply
  simp only [continuousMultiply_const, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, compactRawUnitary.apply_symm_apply]

theorem rawCompactMultiply_add (φ ψ : C(UnitCoordinateSpace, ℝ)) (u : RawTauL2) :
    rawCompactMultiply (φ+ψ) u = rawCompactMultiply φ u + rawCompactMultiply ψ u := by
  unfold rawCompactMultiply
  rw [continuousMultiply_add, map_add]

theorem rawCompactMultiply_mul (φ ψ : C(UnitCoordinateSpace, ℝ)) (u : RawTauL2) :
    rawCompactMultiply (φ*ψ) u = rawCompactMultiply φ (rawCompactMultiply ψ u) := by
  unfold rawCompactMultiply
  rw [compactRawUnitary.symm_apply_apply, continuousMultiply_mul]

theorem rawCompactMultiply_continuous (u : RawTauL2) :
    Continuous (fun φ : C(UnitCoordinateSpace, ℝ) => rawCompactMultiply φ u) :=
  compactRawUnitary.continuous.comp (continuousOrbit compactTauMeasure (compactRawUnitary.symm u)).continuous

end
end ImbalancedChen.Part3.ActualKLCompactMultiplier20261026a

