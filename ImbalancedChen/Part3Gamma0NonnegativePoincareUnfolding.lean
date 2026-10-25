import ImbalancedChen.Part3Gamma0EffectiveFiniteUnfolding
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual effective Gamma0 translates of the concrete reduced carrier
form a disjoint CONULL tiling of the upper half-plane. The omitted points
are proved to lie in the countable Gamma0 saturation of the explicit null
modular boundary. Canonical hyperbolic invariance makes that saturation
null. Thus the full nonnegative Poincare unfolding follows by countable
additivity and Tonelli, without a local-finiteness or convergence premise.

The quotient observable is constructed through the existing actual
measurable orbit section. Its sum is indexed by Gamma0/actionKernel, so
+I and -I are counted only once. This is an extended-real nonnegative
spatial identity, not a spectral or Kuznetsov decomposition.
-/

namespace ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a

/-- Countably many actual integral Gamma0 translates of the known null
boundary. This is a concrete exceptional set, not a supplied null set. -/
def boundarySaturation (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ γ : CongruenceSubgroup.Gamma0 N, γ • gamma0BoundaryCarrier N

theorem boundarySaturation_null (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (boundarySaturation N) = 0 := by
  letI : Countable (CongruenceSubgroup.Gamma0 N) := inferInstance
  unfold boundarySaturation
  apply measure_iUnion_null
  intro γ
  change (volume : Measure UpperHalfPlane)
    ((SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) • gamma0BoundaryCarrier N) = 0
  rw [measure_smul]
  exact gamma0BoundaryCarrier_null N

/-- The entire family of actual effective matrix translates. -/
def allEffectiveCells (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ q : effectiveGamma0 N, effectiveCell N q

/-- Actual carrier coverage forces every omitted orbit into the explicit
boundary saturation. This supplies conullness without an FD hypothesis. -/
theorem allEffectiveCells_compl_subset_boundarySaturation (N : ℕ) [NeZero N] :
    (allEffectiveCells N)ᶜ ⊆ boundarySaturation N := by
  intro z hz
  obtain ⟨γ, hγ⟩ := exists_gamma0_smul_mem_carrier N z
  have hboundary : γ • z ∈ gamma0BoundaryCarrier N := by
    by_contra hnot
    apply hz
    let q : effectiveGamma0 N := QuotientGroup.mk γ⁻¹
    change z ∈ ⋃ q : effectiveGamma0 N, effectiveCell N q
    refine mem_iUnion.mpr ⟨q, ?_⟩
    refine ⟨γ • z, ⟨hγ, hnot⟩, ?_⟩
    change effectiveRepresentative N q • (γ • z) = z
    calc
      effectiveRepresentative N q • (γ • z) = γ⁻¹ • (γ • z) :=
        same_effective_class_action N (effectiveRepresentative N q) γ⁻¹
          (effectiveRepresentative_class N q) (γ • z)
      _ = z := inv_smul_smul γ z
  change z ∈ ⋃ δ : CongruenceSubgroup.Gamma0 N, δ • gamma0BoundaryCarrier N
  exact mem_iUnion.mpr ⟨γ⁻¹, ⟨γ • z, hboundary, inv_smul_smul γ z⟩⟩

theorem allEffectiveCells_compl_null (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (allEffectiveCells N)ᶜ = 0 :=
  measure_mono_null (allEffectiveCells_compl_subset_boundarySaturation N)
    (boundarySaturation_null N)

theorem allEffectiveCells_ae (N : ℕ) [NeZero N] :
    ∀ᵐ z ∂(volume : Measure UpperHalfPlane), z ∈ allEffectiveCells N := by
  apply ae_iff.mpr
  exact allEffectiveCells_compl_null N

theorem allEffectiveCells_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (allEffectiveCells N) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  exact MeasurableSet.iUnion (effectiveCell_measurable N)

/-- Every nonexceptional point belongs to exactly one effective translate,
so the scalar action kernel introduces no factor two. -/
theorem allEffectiveCells_unique_label (N : ℕ) [NeZero N]
    {z : UpperHalfPlane} (hz : z ∈ allEffectiveCells N) :
    ∃! q : effectiveGamma0 N, z ∈ effectiveCell N q := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  refine ⟨q, hq, ?_⟩
  intro r hr
  by_contra hrq
  exact (Set.disjoint_left.mp (effectiveCell_disjoint N hrq)) hr hq

/-- The full nonnegative seed trace over ACTUAL effective Gamma0 labels.
No finiteness of the sum is asserted or needed for its definition. -/
def fullSeedTrace (N : ℕ) (f : UpperHalfPlane → ℝ≥0∞)
    (z : UpperHalfPlane) : ℝ≥0∞ :=
  ∑' q : effectiveGamma0 N, f (effectiveMatrixAction N q z)

theorem fullSeedTrace_measurable (N : ℕ)
    (f : UpperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fullSeedTrace N f) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  exact Measurable.ennreal_tsum
    (fun q => hf.comp (effectiveMatrixAction_measurable N q))

/-- Nonnegative unfolding on the actual representative carrier. Every
partition, nullity and measure-change premise was proved for these cells. -/
theorem lintegral_fullSeedTrace (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂(volume : Measure UpperHalfPlane)) =
      ∫⁻ z in reducedCarrier N, fullSeedTrace N f z := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hdisj : Pairwise (Disjoint on effectiveCell N) := by
    intro q r hqr
    exact effectiveCell_disjoint N hqr
  calc
    (∫⁻ z, f z ∂(volume : Measure UpperHalfPlane)) =
        ∫⁻ z in allEffectiveCells N, f z := by
      rw [Measure.restrict_eq_self_of_ae_mem (allEffectiveCells_ae N)]
    _ = ∑' q : effectiveGamma0 N, ∫⁻ z in effectiveCell N q, f z :=
      lintegral_iUnion (effectiveCell_measurable N) hdisj f
    _ = ∑' q : effectiveGamma0 N,
        ∫⁻ z in reducedCarrier N, f (effectiveMatrixAction N q z) := by
      apply tsum_congr
      intro q
      exact lintegral_effectiveCell N q f
    _ = ∫⁻ z in reducedCarrier N, fullSeedTrace N f z :=
      (lintegral_tsum
        (fun q => (hf.comp (effectiveMatrixAction_measurable N q)).aemeasurable)).symm

/-- The full Poincare trace expressed on the actual orbit quotient through
its actual reduced-carrier section, with zero off the conull image. -/
def nonnegativePoincare (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) : Gamma0OrbitSpace N → ℝ≥0∞ :=
  Function.extend (reducedProjection N)
    (fun z : reducedCarrier N => fullSeedTrace N f z) (fun _ => 0)

theorem nonnegativePoincare_projection (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) (z : reducedCarrier N) :
    nonnegativePoincare N f (reducedProjection N z) = fullSeedTrace N f z :=
  (reducedProjection_measurableEmbedding N).injective.extend_apply _ _ z

/-- The quotient observable uses precisely the pre-existing concrete
rangeSplitting section, without a hypothetical choice or inverse field. -/
theorem nonnegativePoincare_on_image (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) (q : range (reducedProjection N)) :
    nonnegativePoincare N f q = fullSeedTrace N f (reducedOrbitSection N q) := by
  rw [← reducedProjection_section N q]
  exact nonnegativePoincare_projection N f (reducedOrbitSection N q)

theorem nonnegativePoincare_measurable (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    Measurable (nonnegativePoincare N f) :=
  (reducedProjection_measurableEmbedding N).measurable_extend
    ((fullSeedTrace_measurable N f hf).comp measurable_subtype_coe) measurable_const

theorem lintegral_nonnegativePoincare_carrier (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) :
    (∫⁻ q, nonnegativePoincare N f q ∂carrierPushforward N) =
      ∫⁻ z in reducedCarrier N, fullSeedTrace N f z := by
  calc
    _ = ∫⁻ z : reducedCarrier N, fullSeedTrace N f z
        ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).lintegral_map]
      apply lintegral_congr
      intro z
      exact nonnegativePoincare_projection N f z
    _ = _ := lintegral_subtype_comap (reducedCarrier_measurable N) _

/-- Actual Gamma0 nonnegative Poincare unfolding with the canonical
hyperbolic spatial measure and the full scalar kernel counted once. -/
theorem nonnegative_poincare_unfolding (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q, nonnegativePoincare N f q ∂carrierPushforward N) =
      ∫⁻ z, f z ∂(volume : Measure UpperHalfPlane) :=
  (lintegral_nonnegativePoincare_carrier N f).trans (lintegral_fullSeedTrace N f hf).symm

end
end ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a