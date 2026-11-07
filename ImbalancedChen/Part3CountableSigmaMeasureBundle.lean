import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A genuine countable scalar-measure bundle, on the measurable Sigma space.
The measure is the sum of the pushforwards of the fiber measures along
the literal Sigma inclusions. Fiber inclusions are proved measurable
embeddings; AE statements, strong measurability and lower integrals are
proved fiberwise. Every finite fiber has its original exact total mass,
and a countable family of finite fibers gives a sigma-finite bundle.

No norm-matching, Lp unitary, spectral or automorphic premise occurs here.
-/

namespace ImbalancedChen.Part3.CountableSigmaMeasureBundle20261025a

noncomputable section
open Set MeasureTheory Filter

variable {I : Type*} {X : I→Type*} [∀ i,MeasurableSpace (X i)]

theorem sigmaMk_measurable (i : I) : Measurable (Sigma.mk i : X i→Sigma X) := by
  apply measurable_iff_le_map.mpr
  exact iInf_le (fun j => (inferInstance : MeasurableSpace (X j)).map (Sigma.mk j)) i

theorem sigmaMk_injective (i : I) : Function.Injective (Sigma.mk i : X i→Sigma X) := by
  intro x y hxy
  simpa using hxy

theorem sigmaMk_measurableEmbedding (i : I) :
    MeasurableEmbedding (Sigma.mk i : X i→Sigma X) where
  injective := sigmaMk_injective i
  measurable := sigmaMk_measurable i
  measurableSet_image' := by
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro j
    change MeasurableSet ((Sigma.mk j) ⁻¹' ((Sigma.mk i) '' s))
    by_cases hji : j=i
    · subst j
      simpa only [preimage_image_eq _ (sigmaMk_injective i)] using hs
    · have heq : (Sigma.mk j) ⁻¹' ((Sigma.mk i) '' s)=∅ := by
        ext x
        constructor
        · rintro ⟨y,hy,hxy⟩
          exact (hji (congrArg Sigma.fst hxy).symm).elim
        · simp
      rw [heq]
      exact MeasurableSet.empty

def bundleMeasure (mu : ∀ i,Measure (X i)) : Measure (Sigma X) :=
  Measure.sum (fun i => (mu i).map (Sigma.mk i))

theorem bundle_lintegral (mu : ∀ i,Measure (X i)) (f : Sigma X→ℝ≥0∞) :
    (∫⁻ s,f s∂bundleMeasure mu)=∑' i,∫⁻ x,f ⟨i,x⟩∂mu i := by
  rw [bundleMeasure,lintegral_sum_measure]
  apply tsum_congr
  intro i
  exact (sigmaMk_measurableEmbedding i).lintegral_map f

theorem bundle_norm_square_lintegral (mu : ∀ i,Measure (X i)) (f : Sigma X→ℂ) :
    (∫⁻ s,‖f s‖ₑ^2∂bundleMeasure mu)=∑' i,∫⁻ x,‖f ⟨i,x⟩‖ₑ^2∂mu i :=
  bundle_lintegral mu (fun s => ‖f s‖ₑ^2)

theorem bundle_ae_iff [Countable I] (mu : ∀ i,Measure (X i)) (P : Sigma X→Prop) :
    (∀ᵐ s∂bundleMeasure mu,P s) ↔ ∀ i,∀ᵐ x∂mu i,P ⟨i,x⟩ := by
  rw [bundleMeasure,Measure.ae_sum_iff]
  apply forall_congr'
  intro i
  exact (sigmaMk_measurableEmbedding i).ae_map_iff

theorem bundle_aestronglyMeasurable_iff [Countable I]
    (mu : ∀ i,Measure (X i)) (f : Sigma X→ℂ) :
    AEStronglyMeasurable f (bundleMeasure mu) ↔
      ∀ i,AEStronglyMeasurable (fun x => f ⟨i,x⟩) (mu i) := by
  rw [bundleMeasure,aestronglyMeasurable_sum_measure_iff]
  apply forall_congr'
  intro i
  exact (sigmaMk_measurableEmbedding i).aestronglyMeasurable_map_iff

theorem bundle_fiber_mass (mu : ∀ i,Measure (X i)) (i : I) :
    bundleMeasure mu (range (Sigma.mk i))=mu i univ := by
  classical
  have hmeas : MeasurableSet (range (Sigma.mk i : X i→Sigma X)) :=
    (sigmaMk_measurableEmbedding i).measurableSet_range
  rw [bundleMeasure,Measure.sum_apply _ hmeas]
  have hterm : ∀ j,(mu j).map (Sigma.mk j) (range (Sigma.mk i))=
      if j=i then mu i univ else 0 := by
    intro j
    rw [Measure.map_apply (sigmaMk_measurable j) hmeas]
    by_cases hji : j=i
    · subst j
      have heq : (Sigma.mk i) ⁻¹' range (Sigma.mk i : X i→Sigma X)=univ := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          exact ⟨x,rfl⟩
      rw [heq,if_pos rfl]
    · have heq : (Sigma.mk j) ⁻¹' range (Sigma.mk i)=∅ := by
        ext x
        constructor
        · rintro ⟨y,hxy⟩
          exact (hji (congrArg Sigma.fst hxy).symm).elim
        · simp
      rw [heq,measure_empty,if_neg hji]
  simp only [hterm]
  simp

/-- The true countable family of literal fibers is a finite-mass cover.
The whole bundle need not have finite mass. -/
theorem bundleMeasure_sigmaFinite [Countable I] (mu : ∀ i,Measure (X i))
    [∀ i,IsFiniteMeasure (mu i)] : SigmaFinite (bundleMeasure mu) := by
  apply sigmaFinite_of_countable (Set.countable_range
    (fun i : I => range (Sigma.mk i : X i→Sigma X)))
  · intro s hs
    obtain ⟨i,rfl⟩ := hs
    rw [bundle_fiber_mass]
    exact measure_lt_top _ _
  · ext s
    constructor
    · intro _
      exact mem_univ s
    · intro _
      exact mem_sUnion.mpr ⟨range (Sigma.mk s.1),⟨s.1,rfl⟩,⟨s.2,rfl⟩⟩

end
end ImbalancedChen.Part3.CountableSigmaMeasureBundle20261025a
