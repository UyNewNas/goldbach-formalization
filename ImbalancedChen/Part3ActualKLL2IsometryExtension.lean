import ImbalancedChen.Part3ActualKLCompactPlancherel
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.Isometry

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual raw compact KL integral map extends to a linear isometry from
the native physical L²(dr) space to the literal positive tau-density L²
space. Its norm preservation is the actual compact Plancherel theorem,
and its dense domain is the actual compact smooth physical core. Neither
norm preservation nor density is an input premise. The extension agrees
with the same raw K_{i tau} integral on every compact smooth RadialTest.

The range is proved closed. Surjectivity, a unitary equivalence, and an
automorphic spectral normalization are not asserted here.
-/

namespace ImbalancedChen.Part3.ActualKLL2IsometryExtension20261025a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open ActualKLCoordinateMeasures20261025a ActualKLCoreTransform20261025a
open ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactPlancherel20261025a

private theorem physicalCoreSubtype_dense :
    DenseRange (compactPhysicalCore.subtype : compactPhysicalCore → RadialL2) := by
  have he : Set.range (compactPhysicalCore.subtype : compactPhysicalCore → RadialL2) =
      (compactPhysicalCore : Set RadialL2) := by
    ext F
    constructor
    · rintro ⟨U, rfl⟩
      exact U.property
    · intro hF
      exact ⟨⟨F, hF⟩, rfl⟩
  change Dense (Set.range (compactPhysicalCore.subtype : compactPhysicalCore → RadialL2))
  rw [he]
  exact compactPhysicalCore_dense

private theorem actual_core_bound (F : compactPhysicalCore) :
    ‖actualCoreKLTransform F‖ ≤ (1 : ℝ) * ‖compactPhysicalCore.subtype F‖ := by
  rw [actualCoreKLTransform_norm]
  simpa only [one_mul] using (le_refl ‖(F : RadialL2)‖)

/-- Concrete extension of the pre-existing raw integral linear map.
The only bound used below is proved by actual compact Plancherel. -/
def actualKLContinuous : RadialL2 →L[ℂ] RawTauL2 :=
  actualCoreKLTransform.extendOfNorm compactPhysicalCore.subtype

theorem actualKLContinuous_on_core (F : compactPhysicalCore) :
    actualKLContinuous (F : RadialL2) = actualCoreKLTransform F := by
  change actualCoreKLTransform.extendOfNorm compactPhysicalCore.subtype
    (compactPhysicalCore.subtype F) = actualCoreKLTransform F
  exact LinearMap.extendOfNorm_eq physicalCoreSubtype_dense ⟨1, actual_core_bound⟩ F

/-- Norm equality propagates from the actual dense core through the
continuous extension; no global norm theorem is postulated. -/
theorem actualKLContinuous_norm (F : RadialL2) : ‖actualKLContinuous F‖ = ‖F‖ := by
  apply physicalCoreSubtype_dense.induction_on F
    (isClosed_eq actualKLContinuous.continuous.norm continuous_norm)
  intro U
  rw [actualKLContinuous_on_core, actualCoreKLTransform_norm]

/-- The actual native raw KL L² isometry. It has no chosen inverse. -/
def actualKLIsometry : RadialL2 →ₗᵢ[ℂ] RawTauL2 where
  toLinearMap := actualKLContinuous.toLinearMap
  norm_map' := actualKLContinuous_norm

theorem actualKLIsometry_on_core (F : compactPhysicalCore) :
    actualKLIsometry (F : RadialL2) = actualCoreKLTransform F :=
  actualKLContinuous_on_core F

theorem actualKLIsometry_norm (F : RadialL2) : ‖actualKLIsometry F‖ = ‖F‖ :=
  actualKLIsometry.norm_map F

/-- The same actual compact K integral is retained after extending the
physical domain, independently of the compact representative choice. -/
theorem actualKLIsometry_on_test (T : RadialTest) :
    actualKLIsometry (radialCoreL2 T) = rawKLTestTransform T := by
  exact (actualKLIsometry_on_core (physicalCoreVector T)).trans
    (actualCoreKLTransform_on_test T)

theorem actualKLIsometry_on_test_ae (T : RadialTest) :
    (actualKLIsometry (radialCoreL2 T) : ℝ → ℂ) =ᵐ[tauMeasure]
      actualKtransform T.function := by
  rw [actualKLIsometry_on_test]
  exact rawKLTestTransform_ae T

/-- Completeness of the actual physical L² space makes this isometric
range closed. This statement does not assert that the range is all RawTauL2. -/
theorem actualKLRange_closed : IsClosed (Set.range actualKLIsometry) :=
  actualKLIsometry.isometry.isClosedEmbedding.isClosed_range

theorem actualKLIsometry_injective : Function.Injective actualKLIsometry :=
  actualKLIsometry.injective

/-- Any continuous linear map with the same concrete compact-test values
coincides with this actual extension, by the actual dense compact core. -/
theorem actualKLContinuous_unique (U : RadialL2 →L[ℂ] RawTauL2)
    (hU : ∀ T : RadialTest, U (radialCoreL2 T) = rawKLTestTransform T) :
    U = actualKLContinuous := by
  apply ContinuousLinearMap.ext
  intro F
  apply physicalCoreSubtype_dense.induction_on F
    (isClosed_eq U.continuous actualKLContinuous.continuous)
  intro V
  obtain ⟨T, hT⟩ := V.property
  change U (V : RadialL2) = actualKLContinuous (V : RadialL2)
  rw [← hT, hU]
  exact (actualKLIsometry_on_test T).symm

end
end ImbalancedChen.Part3.ActualKLL2IsometryExtension20261025a
