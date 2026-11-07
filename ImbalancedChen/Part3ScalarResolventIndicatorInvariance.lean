import ImbalancedChen.Part3CompactCoordinateIndicatorInvariance
import ImbalancedChen.Part3GenericResolventCyclicIntertwining

/-!
The compact-coordinate theorem is connected to the previously constructed
actual scalar spectral measure and its actual coordinate-multiplier CLM.
Invariance under this one CLM implies every Borel indicator invariance.
Together with the independently proved single-vector criterion, one
almost-everywhere nonzero vector then forces the closed submodule to be
the whole scalar L2 space. No raw KL range or norm identity is asserted.
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ScalarResolventIndicatorInvariance20261025a

noncomputable section

open MeasureTheory Set
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a
open ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (f : H)

theorem compactCoordinate_eq_actual (u : Lp ℂ 2 (scalarMeasure R hSA f)) :
    CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply (scalarMeasure R hSA f) u =
      coordinateMultiplier R hSA f u := by
  apply Lp.ext
  filter_upwards
    [CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply_coe_ae (scalarMeasure R hSA f) u,
      coordinateMultiplier_coe_ae R hSA f u] with t hleft hright
  rw [hleft, hright, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]

theorem indicatorMultiplier_mem_of_coordinate_invariant
    (S : Submodule ℂ (Lp ℂ 2 (scalarMeasure R hSA f)))
    (hclosed : IsClosed (S : Set (Lp ℂ 2 (scalarMeasure R hSA f))))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiplier R hSA f u ∈ S)
    (B : Set (ResolventSpectrum R)) (hB : MeasurableSet B)
    (u : Lp ℂ 2 (scalarMeasure R hSA f)) (hu : u ∈ S) :
    indicatorMultiplier (scalarMeasure R hSA f) B hB u ∈ S := by
  apply CompactCoordinateIndicatorInvariance20261025a.indicatorMultiplier_mem
    (scalarMeasure R hSA f) S hclosed ?_ B hB u hu
  intro v hv
  rw [compactCoordinate_eq_actual]
  exact hcoordinate v hv

theorem orthogonal_coordinate_invariant
    (S : Submodule ℂ (Lp ℂ 2 (scalarMeasure R hSA f)))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiplier R hSA f u ∈ S)
    {v : Lp ℂ 2 (scalarMeasure R hSA f)} (hv : v ∈ Sᗮ) :
    coordinateMultiplier R hSA f v ∈ Sᗮ := by
  rw [← compactCoordinate_eq_actual]
  apply CompactCoordinateIndicatorInvariance20261025a.orthogonal_coordinate_invariant
    (scalarMeasure R hSA f) S ?_ hv
  intro u hu
  rw [compactCoordinate_eq_actual]
  exact hcoordinate u hu

theorem closed_coordinate_invariant_eq_top
    (S : Submodule ℂ (Lp ℂ 2 (scalarMeasure R hSA f)))
    (hclosed : IsClosed (S : Set (Lp ℂ 2 (scalarMeasure R hSA f))))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiplier R hSA f u ∈ S)
    (u : Lp ℂ 2 (scalarMeasure R hSA f)) (hu : u ∈ S)
    (hnonzero : ∀ᵐ t ∂scalarMeasure R hSA f, u t ≠ 0) : S = ⊤ :=
  closed_indicator_invariant_eq_top (scalarMeasure R hSA f) S hclosed
    (fun B hB v hv => indicatorMultiplier_mem_of_coordinate_invariant R hSA f
      S hclosed hcoordinate B hB v hv) u hu hnonzero

end

end ImbalancedChen.Part3.ScalarResolventIndicatorInvariance20261025a
