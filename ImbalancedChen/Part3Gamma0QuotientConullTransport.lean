import ImbalancedChen.Part3Gamma0CarrierMeasurableInverse
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The image of the actual reduced Gamma0 carrier is conull for the actual
carrier pushforward of canonical hyperbolic volume. The canonical subtype
measure on the carrier, and the quotient measure restricted to this image,
are transported in both directions by the previously constructed section.
No conullness, measure-preserving inverse, or Hilbert isometry is assumed.
This is spatial transport; no spectral dt normalization is changed.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a

/-- Canonical hyperbolic volume on the actual reduced-carrier subtype. -/
def reducedCarrierMeasure (N : ℕ) [NeZero N] : Measure (reducedCarrier N) :=
  (volume : Measure UpperHalfPlane).comap
    (Subtype.val : reducedCarrier N → UpperHalfPlane)

/-- The measurable image inherits the actual quotient measure. -/
def reducedImageMeasure (N : ℕ) [NeZero N] :
    Measure (range (reducedProjection N)) :=
  (carrierPushforward N).comap
    (Subtype.val : range (reducedProjection N) → Gamma0OrbitSpace N)

/-- Removing the null boundary and then projecting gives the SAME quotient
measure, with the original spatial volume normalization. -/
theorem reducedProjection_map_measure (N : ℕ) [NeZero N] :
    (reducedCarrierMeasure N).map (reducedProjection N) = carrierPushforward N := by
  change ((volume : Measure UpperHalfPlane).comap
    (Subtype.val : reducedCarrier N → UpperHalfPlane)).map
      (orbitProjection N ∘ Subtype.val) = _
  rw [← Measure.map_map (orbitProjection_measurable N) measurable_subtype_coe,
    Measure.map_comap_subtype_coe (reducedCarrier_measurable N)]
  exact reducedCarrier_pushforward_eq N

/-- The exceptional quotient orbits have zero actual pushforward measure. -/
theorem reducedProjection_range_compl_null (N : ℕ) [NeZero N] :
    carrierPushforward N (range (reducedProjection N))ᶜ = 0 := by
  rw [← reducedProjection_map_measure N,
    Measure.map_apply (reducedProjection_measurableEmbedding N).measurable
      (reducedProjection_range_measurable N).compl]
  have hempty : reducedProjection N ⁻¹' (range (reducedProjection N))ᶜ = ∅ := by
    ext z
    simp
  rw [hempty, measure_empty]

theorem reducedProjection_range_ae (N : ℕ) [NeZero N] :
    ∀ᵐ q ∂carrierPushforward N, q ∈ range (reducedProjection N) := by
  apply ae_iff.mpr
  exact reducedProjection_range_compl_null N

/-- The explicit representative map, now landing in its measurable image. -/
def reducedProjectionToImage (N : ℕ) [NeZero N] :
    reducedCarrier N → range (reducedProjection N) :=
  fun z => ⟨reducedProjection N z, ⟨z, rfl⟩⟩

theorem reducedProjectionToImage_measurable (N : ℕ) [NeZero N] :
    Measurable (reducedProjectionToImage N) :=
  (reducedProjection_measurableEmbedding N).measurable.subtype_mk

/-- Both concrete inverse identities are retained, not replaced by an
abstract isomorphism supplied as a premise. -/
def reducedCarrierImageEquiv (N : ℕ) [NeZero N] :
    reducedCarrier N ≃ᵐ range (reducedProjection N) where
  toFun := reducedProjectionToImage N
  invFun := reducedOrbitSection N
  left_inv := reducedOrbitSection_projection N
  right_inv := by
    intro q
    apply Subtype.ext
    exact reducedProjection_section N q
  measurable_toFun := reducedProjectionToImage_measurable N
  measurable_invFun := reducedOrbitSection_measurable N

/-- The quotient-image inclusion is measure preserving because its
complement was proved null for this particular quotient measure. -/
theorem reducedImage_inclusion_map (N : ℕ) [NeZero N] :
    (reducedImageMeasure N).map
      (Subtype.val : range (reducedProjection N) → Gamma0OrbitSpace N) =
        carrierPushforward N := by
  rw [reducedImageMeasure,
    Measure.map_comap_subtype_coe (reducedProjection_range_measurable N),
    Measure.restrict_eq_self_of_ae_mem (reducedProjection_range_ae N)]

theorem reducedProjectionToImage_map_measure (N : ℕ) [NeZero N] :
    (reducedCarrierMeasure N).map (reducedProjectionToImage N) =
      reducedImageMeasure N := by
  apply (MeasurableEmbedding.subtype_coe
    (reducedProjection_range_measurable N)).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (reducedProjectionToImage_measurable N), reducedImage_inclusion_map N]
  exact reducedProjection_map_measure N

/-- The actual rangeSplitting inverse preserves the original canonical
carrier measure. This is equality of measures, not only equality of mass. -/
theorem reducedOrbitSection_map_measure (N : ℕ) [NeZero N] :
    (reducedImageMeasure N).map (reducedOrbitSection N) =
      reducedCarrierMeasure N := by
  rw [← reducedProjectionToImage_map_measure N,
    Measure.map_map (reducedOrbitSection_measurable N)
      (reducedProjectionToImage_measurable N)]
  have hinv : reducedOrbitSection N ∘ reducedProjectionToImage N = id := by
    funext z
    exact reducedOrbitSection_projection N z
  rw [hinv, Measure.map_id]

theorem reducedProjection_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (reducedProjection N)
      (reducedCarrierMeasure N) (carrierPushforward N) :=
  ⟨(reducedProjection_measurableEmbedding N).measurable,
    reducedProjection_map_measure N⟩

theorem reducedProjectionToImage_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (reducedProjectionToImage N)
      (reducedCarrierMeasure N) (reducedImageMeasure N) :=
  ⟨reducedProjectionToImage_measurable N, reducedProjectionToImage_map_measure N⟩

theorem reducedOrbitSection_measurePreserving (N : ℕ) [NeZero N] :
    MeasurePreserving (reducedOrbitSection N)
      (reducedImageMeasure N) (reducedCarrierMeasure N) :=
  ⟨reducedOrbitSection_measurable N, reducedOrbitSection_map_measure N⟩

/-- Pullback from the actual quotient into canonical carrier L2 is a
complex linear isometry. No spectral Hilbert space is substituted here. -/
def quotientL2ToReducedCarrier (N : ℕ) [NeZero N] :
    Lp ℂ 2 (carrierPushforward N) →ₗᵢ[ℂ] Lp ℂ 2 (reducedCarrierMeasure N) :=
  Lp.compMeasurePreservingₗᵢ ℂ (reducedProjection N)
    (reducedProjection_measurePreserving N)

/-- Transport in the other direction is explicit on the conull image. -/
def reducedCarrierL2ToImage (N : ℕ) [NeZero N] :
    Lp ℂ 2 (reducedCarrierMeasure N) →ₗᵢ[ℂ] Lp ℂ 2 (reducedImageMeasure N) :=
  Lp.compMeasurePreservingₗᵢ ℂ (reducedOrbitSection N)
    (reducedOrbitSection_measurePreserving N)

end
end ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
