import ImbalancedChen.Part3EvenFourierHilbert

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Even L1-intersect-L2 representatives are dense in the actual reflection-fixed
L2 subspace. The approximants are explicit symmetrizations of Schwartz
functions. Inputs are Mathlib's Schwartz density and measure-preserving
reflection; no Fourier, Plancherel, or K-profile totality premise is used.
-/

noncomputable section

namespace ImbalancedChen.Part3.EvenL1L2DensitySourceOnly

open MeasureTheory SchwartzMap
open scoped SchwartzMap
open EvenFourierHilbertSourceOnly

private theorem negPreserving :
    MeasurePreserving (fun x : ℝ => -x) volume volume := by
  exact (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving

/-- Explicit continuous symmetrization on the actual L2 quotient. -/
def evenProjection : ComplexL2 →L[ℂ] ComplexL2 :=
  (1 / 2 : ℂ) •
    (ContinuousLinearMap.id ℂ ComplexL2 + reflection.toContinuousLinearMap)

theorem evenProjection_apply (f : ComplexL2) :
    evenProjection f = (1 / 2 : ℂ) • (f + reflection f) := by
  rfl

theorem evenProjection_mem (f : ComplexL2) : evenProjection f ∈ evenL2 := by
  change reflection (evenProjection f) = evenProjection f
  rw [evenProjection_apply, map_smul, map_add, reflection_involutive,
    add_comm (reflection f) f]

theorem evenProjection_eq_self {f : ComplexL2} (hf : f ∈ evenL2) :
    evenProjection f = f := by
  rw [evenProjection_apply, (mem_evenL2_iff f).1 hf,
    ← two_smul ℂ f, smul_smul]
  norm_num

/-- The projection with codomain the closed even subspace. -/
def evenProjectionSubspace (f : ComplexL2) : evenL2 :=
  ⟨evenProjection f, evenProjection_mem f⟩

theorem continuous_evenProjectionSubspace : Continuous evenProjectionSubspace := by
  exact evenProjection.continuous.subtype_mk evenProjection_mem

theorem evenProjectionSubspace_surjective :
    Function.Surjective evenProjectionSubspace := by
  intro f
  refine ⟨(f : ComplexL2), ?_⟩
  apply Subtype.ext
  exact evenProjection_eq_self f.property

/-- A dense family in even L2 obtained by projecting actual Schwartz classes. -/
def evenSchwartzEmbedding (g : 𝓢(ℝ, ℂ)) : evenL2 :=
  evenProjectionSubspace (SchwartzMap.toLpCLM ℝ ℂ 2 volume g)

theorem denseRange_evenSchwartzEmbedding : DenseRange evenSchwartzEmbedding := by
  exact evenProjectionSubspace_surjective.denseRange.comp
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top) continuous_evenProjectionSubspace

/-- The concrete representative of the projected Schwartz class. -/
def evenSchwartzProfile (g : 𝓢(ℝ, ℂ)) : ℝ → ℂ :=
  (1 / 2 : ℂ) • ((g : ℝ → ℂ) + fun x : ℝ => g (-x))

theorem evenSchwartzProfile_even (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    evenSchwartzProfile g (-x) = evenSchwartzProfile g x := by
  simp [evenSchwartzProfile, add_comm]

theorem evenSchwartzProfile_integrable (g : 𝓢(ℝ, ℂ)) :
    Integrable (evenSchwartzProfile g) := by
  exact Integrable.smul (1 / 2 : ℂ) (g.integrable.add g.integrable.comp_neg)

theorem evenSchwartzProfile_memLp (g : 𝓢(ℝ, ℂ)) :
    MemLp (evenSchwartzProfile g) 2 := by
  exact ((g.memLp 2).add
    ((g.memLp 2).comp_measurePreserving negPreserving)).const_smul (1 / 2 : ℂ)

/-- Identification of the quotient construction with the explicit even
L1-intersect-L2 function. This also tracks the factor one half. -/
theorem evenSchwartzEmbedding_coe (g : 𝓢(ℝ, ℂ)) :
    (evenSchwartzEmbedding g : ComplexL2) =
      (evenSchwartzProfile_memLp g).toLp (evenSchwartzProfile g) := by
  change (1 / 2 : ℂ) •
    ((g.memLp 2).toLp (g : ℝ → ℂ) +
      reflection ((g.memLp 2).toLp (g : ℝ → ℂ))) = _
  rw [reflection_toLp]
  change (1 / 2 : ℂ) •
    ((g.memLp 2).toLp (g : ℝ → ℂ) +
      ((g.memLp 2).comp_measurePreserving negPreserving).toLp
        (fun x : ℝ => g (-x))) =
    ((((g.memLp 2).add
      ((g.memLp 2).comp_measurePreserving negPreserving)).const_smul
        (1 / 2 : ℂ)).toLp
      ((1 / 2 : ℂ) • ((g : ℝ → ℂ) + fun x : ℝ => g (-x))))
  rw [MemLp.toLp_const_smul, MemLp.toLp_add]

/-- Every even L2 class has actual pointwise-even L1-intersect-L2
approximants, in the ambient L2 norm and with arbitrary positive error. -/
theorem exists_even_integrable_memLp_approx (f : evenL2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ∃ hg : MemLp g 2,
      Integrable g ∧ (∀ x : ℝ, g (-x) = g x) ∧
        ‖hg.toLp g - (f : ComplexL2)‖ < ε := by
  obtain ⟨g, hg⟩ := denseRange_evenSchwartzEmbedding.exists_dist_lt f hε
  refine ⟨evenSchwartzProfile g, evenSchwartzProfile_memLp g,
    evenSchwartzProfile_integrable g, evenSchwartzProfile_even g, ?_⟩
  change dist (f : ComplexL2) (evenSchwartzEmbedding g : ComplexL2) < ε at hg
  rw [dist_eq_norm, norm_sub_rev, evenSchwartzEmbedding_coe] at hg
  exact hg

end ImbalancedChen.Part3.EvenL1L2DensitySourceOnly
