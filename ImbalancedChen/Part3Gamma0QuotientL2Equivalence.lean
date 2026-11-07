import ImbalancedChen.Part3Gamma0QuotientConullTransport

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Surjectivity of the actual quotient L2 pullback. A canonical-carrier L2
representative is transported through the actual reduced orbit section
on the measurable conull image, and is zero off that image. The embedding
map theorem proves MemLp for precisely the actual quotient measure.
Consequently the existing complex linear isometry is an equivalence.
No spectral measure or spectral decomposition is introduced.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientL2Equivalence20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a

/-- Actual inverse transport on the image, with zero elsewhere. -/
def quotientZeroExtension (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) : Gamma0OrbitSpace N → ℂ :=
  Function.extend (reducedProjection N) g (fun _ => 0)

theorem quotientZeroExtension_projection (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (z : reducedCarrier N) :
    quotientZeroExtension N g (reducedProjection N z) = g z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply g (fun _ => 0) z

/-- The extension uses the SAME previously constructed measurable section. -/
theorem quotientZeroExtension_on_image (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) (q : range (reducedProjection N)) :
    quotientZeroExtension N g q = g (reducedOrbitSection N q) := by
  rw [← reducedProjection_section N q]
  exact quotientZeroExtension_projection N g (reducedOrbitSection N q)

theorem quotientZeroExtension_off_image (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) {q : Gamma0OrbitSpace N}
    (hq : q ∉ range (reducedProjection N)) :
    quotientZeroExtension N g q = 0 :=
  Function.extend_apply' g (fun _ => 0) q hq

theorem quotientZeroExtension_comp_projection (N : ℕ) [NeZero N]
    (g : reducedCarrier N → ℂ) :
    quotientZeroExtension N g ∘ reducedProjection N = g := by
  funext z
  exact quotientZeroExtension_projection N g z

/-- Both AE strong measurability and the finite square norm are transported
by the genuine embedding; neither is an additional premise. -/
theorem quotientZeroExtension_memLp (N : ℕ) [NeZero N]
    (g : Lp ℂ 2 (reducedCarrierMeasure N)) :
    MemLp (quotientZeroExtension N g) 2 (carrierPushforward N) := by
  rw [← reducedProjection_map_measure N]
  apply (reducedProjection_measurableEmbedding N).memLp_map_measure_iff.mpr
  rw [quotientZeroExtension_comp_projection]
  exact g.memLp

/-- An actual preimage in quotient L2 for every canonical-carrier L2 vector. -/
def quotientL2Extension (N : ℕ) [NeZero N]
    (g : Lp ℂ 2 (reducedCarrierMeasure N)) : Lp ℂ 2 (carrierPushforward N) :=
  (quotientZeroExtension_memLp N g).toLp (quotientZeroExtension N g)

theorem quotientL2_pullback_extension (N : ℕ) [NeZero N]
    (g : Lp ℂ 2 (reducedCarrierMeasure N)) :
    quotientL2ToReducedCarrier N (quotientL2Extension N g) = g := by
  change Lp.compMeasurePreserving (reducedProjection N)
      (reducedProjection_measurePreserving N)
      ((quotientZeroExtension_memLp N g).toLp (quotientZeroExtension N g)) = g
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  exact ((quotientZeroExtension_memLp N g).comp_measurePreserving
    (reducedProjection_measurePreserving N)).coeFn_toLp.trans
      (Filter.Eventually.of_forall (quotientZeroExtension_projection N g))

theorem quotientL2ToReducedCarrier_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (quotientL2ToReducedCarrier N) := by
  intro g
  exact ⟨quotientL2Extension N g, quotientL2_pullback_extension N g⟩

/-- The actual quotient and actual reduced carrier have canonically
isometric complex L2 spaces, with no hOnto or hIso input. -/
def quotientL2ReducedCarrierEquiv (N : ℕ) [NeZero N] :
    Lp ℂ 2 (carrierPushforward N) ≃ₗᵢ[ℂ] Lp ℂ 2 (reducedCarrierMeasure N) :=
  LinearIsometryEquiv.ofSurjective (quotientL2ToReducedCarrier N)
    (quotientL2ToReducedCarrier_surjective N)

/-- Its inverse is the explicit zero extension, as an L2 equivalence class. -/
theorem quotientL2ReducedCarrierEquiv_symm_apply (N : ℕ) [NeZero N]
    (g : Lp ℂ 2 (reducedCarrierMeasure N)) :
    (quotientL2ReducedCarrierEquiv N).symm g = quotientL2Extension N g := by
  apply (quotientL2ReducedCarrierEquiv N).injective
  rw [(quotientL2ReducedCarrierEquiv N).apply_symm_apply]
  exact (quotientL2_pullback_extension N g).symm

end
end ImbalancedChen.Part3.Gamma0QuotientL2Equivalence20261025a
