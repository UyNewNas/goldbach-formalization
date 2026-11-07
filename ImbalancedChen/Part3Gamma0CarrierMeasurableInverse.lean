import ImbalancedChen.Part3Gamma0CarrierAESection
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The Gamma0 orbit projection takes measurable sets to measurable quotient
sets: the full preimage of an image is the countable union of the actual
Gamma0 translates. Restriction to the true reduced carrier is consequently
a measurable embedding. Mathlib's rangeSplitting supplies its actual
measurable inverse on its image, with both inverse identities proved.
No hypothetical measurable inverse or fundamental-domain field is used.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a

/-- The exact saturation identity for the actual congruence subgroup. -/
theorem orbitProjection_preimage_image_eq_iUnion (N : ℕ) (s : Set UpperHalfPlane) :
    orbitProjection N ⁻¹' (orbitProjection N '' s) =
      ⋃ γ : CongruenceSubgroup.Gamma0 N, γ • s := by
  ext z
  constructor
  · rintro ⟨w, hw, hq⟩
    have horbit :
        MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) UpperHalfPlane w z :=
      Quotient.exact hq
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp horbit
    refine mem_iUnion.mpr ⟨γ⁻¹, ?_⟩
    refine ⟨w, hw, ?_⟩
    rw [← hγ]
    exact inv_smul_smul γ z
  · intro hz
    obtain ⟨γ, hγ⟩ := mem_iUnion.mp hz
    obtain ⟨w, hw, rfl⟩ := hγ
    exact ⟨w, hw, (orbitProjection_smul N γ w).symm⟩

/-- Countability comes from the actual integral matrix group. Each
translate is measurable via the pinned real GL action on H. -/
theorem gamma0_saturation_measurable (N : ℕ) {s : Set UpperHalfPlane}
    (hs : MeasurableSet s) :
    MeasurableSet (⋃ γ : CongruenceSubgroup.Gamma0 N, γ • s) := by
  letI : Countable (CongruenceSubgroup.Gamma0 N) := inferInstance
  apply MeasurableSet.iUnion
  intro γ
  change MeasurableSet
    ((SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) • s)
  exact hs.const_smul _

/-- This is genuine image measurability in the quotient sigma algebra,
not a standard-Borel or measurable-section assumption. -/
theorem orbitProjection_image_measurable (N : ℕ) {s : Set UpperHalfPlane}
    (hs : MeasurableSet s) :
    MeasurableSet (orbitProjection N '' s) := by
  apply measurableSet_quotient.mpr
  change MeasurableSet (orbitProjection N ⁻¹' (orbitProjection N '' s))
  rw [orbitProjection_preimage_image_eq_iUnion]
  exact gamma0_saturation_measurable N hs

/-- The actual projection on the explicit reduced carrier. -/
def reducedProjection (N : ℕ) [NeZero N] :
    reducedCarrier N → Gamma0OrbitSpace N :=
  fun z => orbitProjection N z

/-- A measurable embedding with no hypothetical inverse as input. -/
theorem reducedProjection_measurableEmbedding (N : ℕ) [NeZero N] :
    MeasurableEmbedding (reducedProjection N) where
  injective := by
    intro z w h
    apply Subtype.ext
    exact orbitProjection_injOn_reducedCarrier N z.property w.property h
  measurable := (orbitProjection_measurable N).comp measurable_subtype_coe
  measurableSet_image' := by
    intro s hs
    change MeasurableSet
      ((orbitProjection N ∘ (Subtype.val : reducedCarrier N → UpperHalfPlane)) '' s)
    rw [Set.image_comp]
    apply orbitProjection_image_measurable N
    exact (MeasurableEmbedding.subtype_coe
      (reducedCarrier_measurable N)).measurableSet_image.mpr hs

/-- Its true quotient image is measurable. -/
theorem reducedProjection_range_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (range (reducedProjection N)) :=
  (reducedProjection_measurableEmbedding N).measurableSet_range

/-- A genuine measurable inverse on the image, chosen by Mathlib's
rangeSplitting and proved measurable from the embedding just constructed. -/
def reducedOrbitSection (N : ℕ) [NeZero N] :
    range (reducedProjection N) → reducedCarrier N :=
  rangeSplitting (reducedProjection N)

theorem reducedOrbitSection_measurable (N : ℕ) [NeZero N] :
    Measurable (reducedOrbitSection N) :=
  (reducedProjection_measurableEmbedding N).measurable_rangeSplitting

/-- Projecting the actual section recovers the original quotient point. -/
theorem reducedProjection_section (N : ℕ) [NeZero N]
    (q : range (reducedProjection N)) :
    reducedProjection N (reducedOrbitSection N q) = (q : Gamma0OrbitSpace N) :=
  apply_rangeSplitting (reducedProjection N) q

/-- The chosen section also recovers every reduced-carrier representative. -/
theorem reducedOrbitSection_projection (N : ℕ) [NeZero N]
    (z : reducedCarrier N) :
    reducedOrbitSection N ⟨reducedProjection N z, ⟨z, rfl⟩⟩ = z := by
  apply (reducedProjection_measurableEmbedding N).injective
  exact reducedProjection_section N ⟨reducedProjection N z, ⟨z, rfl⟩⟩

end
end ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
