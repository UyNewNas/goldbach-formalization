import ImbalancedChen.Part3MeasurableCoordinateIndicatorTransport
import ImbalancedChen.Part3ActualKLResolventMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The genuine existing raw KL coordinate CLM and its true support-derived
inverse instantiate indicator transport. Its self-adjointness and reducing
subspace implication are proved from its literal real coefficient.
No KL norm identity, transform extension or invariant transform range is
assumed or asserted. SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLCoordinateIndicatorBridge20261025a

noncomputable section

open MeasureTheory Set
open ImbalancedChen.Part3.ActualKLCoordinateMeasures20261025a
open ImbalancedChen.Part3.ActualKLCoreTransform20261025a
open ImbalancedChen.Part3.ActualKLResolventCoordinate20261025a
open ImbalancedChen.Part3.ActualKLResolventMultiplier20261025a
open ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a

theorem rawKLResolventMultiplier_symmetric (u v : RawTauL2) :
    inner ℂ (rawKLResolventMultiplier u) v = inner ℂ u (rawKLResolventMultiplier v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rawKLResolventMultiplier_smul_ae u, rawKLResolventMultiplier_smul_ae v]
    with tau hu hv
  rw [hu, hv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

theorem rawKLResolventMultiplier_selfAdjoint : IsSelfAdjoint rawKLResolventMultiplier :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr rawKLResolventMultiplier_symmetric

theorem rawTau_orthogonal_coordinate_invariant (S : Submodule ℂ RawTauL2)
    (hcoordinate : ∀ u, u ∈ S → rawKLResolventMultiplier u ∈ S)
    {v : RawTauL2} (hv : v ∈ Sᗮ) : rawKLResolventMultiplier v ∈ Sᗮ := by
  apply (S.mem_orthogonal _).2
  intro u hu
  rw [← rawKLResolventMultiplier_symmetric]
  exact (S.mem_orthogonal v).mp hv _ (hcoordinate u hu)

/-- No indicator-invariance hypothesis is present: the actual one-coordinate
CLM invariance and closedness supply all raw Borel truncations. -/
theorem rawTau_indicatorMultiplier_mem
    (S : Submodule ℂ RawTauL2) (hclosed : IsClosed (S : Set RawTauL2))
    (hcoordinate : ∀ u, u ∈ S → rawKLResolventMultiplier u ∈ S)
    (B : Set ℝ) (hB : MeasurableSet B) (u : RawTauL2) (hu : u ∈ S) :
    indicatorMultiplier tauMeasure B hB u ∈ S :=
  MeasurableCoordinateIndicatorTransport20261025a.indicatorMultiplier_mem
    tauMeasure klCompactCoordinate klCompactCoordinate_measurable
    klCompactInverse klCompactInverse_measurable klCompactInverse_comp_ae
    rawKLResolventMultiplier rawKLResolventMultiplier_smul_ae S hclosed hcoordinate B hB u hu

end

end ImbalancedChen.Part3.ActualKLCoordinateIndicatorBridge20261025a
