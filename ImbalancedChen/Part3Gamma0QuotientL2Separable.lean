import ImbalancedChen.Part3Gamma0QuotientL2Equivalence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Second countability and separability of the ACTUAL Gamma0 quotient L2
space for its canonical carrier pushforward measure. The proof first
uses the countably generated Borel measurable structure on the actual
reduced upper-half-plane carrier and its actual finite subtype measure,
then transports through the existing quotient/reduced-carrier isometry.
No quotient-orbit topology/Borel identification or hSeparable is assumed.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientL2Separable20261025a
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0QuotientL2Equivalence20261025a

/-- The original invariant-volume carrier has the same finite mass as
its genuine actual quotient pushforward; normalization is unchanged. -/
theorem reducedCarrierMeasure_mass (N : ℕ) [NeZero N] :
    reducedCarrierMeasure N univ = carrierPushforward N univ := by
  rw [← reducedProjection_map_measure N,
    Measure.map_apply (reducedProjection_measurableEmbedding N).measurable measurableSet_univ]
  simp

instance reducedCarrierMeasure_finite (N : ℕ) [NeZero N] :
    IsFiniteMeasure (reducedCarrierMeasure N) where
  measure_univ_lt_top := by
    rw [reducedCarrierMeasure_mass N]
    exact carrierPushforward_finite N

/-- The actual carrier is a subtype of the second-countable upper half
plane. This does not assert second countability of the orbit quotient. -/
theorem reducedCarrier_secondCountable (N : ℕ) [NeZero N] :
    SecondCountableTopology (reducedCarrier N) := inferInstance

/-- Upper-half-plane Borel countable generation, inherited by the actual
carrier's existing subtype measurable structure. -/
theorem reducedCarrier_countablyGenerated (N : ℕ) [NeZero N] :
    MeasurableSpace.CountablyGenerated (reducedCarrier N) := inferInstance

theorem reducedCarrierMeasure_isSeparable (N : ℕ) [NeZero N] :
    MeasureTheory.IsSeparable (reducedCarrierMeasure N) := inferInstance

/-- Pinned Lp separability applies to the actual finite carrier measure. -/
instance reducedCarrierL2_secondCountable (N : ℕ) [NeZero N] :
    SecondCountableTopology (Lp ℂ 2 (reducedCarrierMeasure N)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

/-- The true quotient Hilbert space, not whole-plane L2, is transported
through the already constructed exact linear-isometric equivalence. -/
instance quotientL2_secondCountable (N : ℕ) [NeZero N] :
    SecondCountableTopology (Lp ℂ 2 (carrierPushforward N)) :=
  (quotientL2ReducedCarrierEquiv N).toHomeomorph.secondCountableTopology

instance quotientL2_separable (N : ℕ) [NeZero N] :
    TopologicalSpace.SeparableSpace (Lp ℂ 2 (carrierPushforward N)) := by
  infer_instance

end
end ImbalancedChen.Part3.Gamma0QuotientL2Separable20261025a
