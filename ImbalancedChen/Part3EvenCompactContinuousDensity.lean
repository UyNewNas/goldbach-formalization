import ImbalancedChen.Part3EvenL1L2Density
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Compactly supported continuous pointwise-even representatives are dense in
the actual even L2 subspace. Uses Mathlib's actual compact smooth Lp density,
then symmetrizes and verifies compact support of the explicit representative.
-/

noncomputable section

namespace ImbalancedChen.Part3.EvenCompactContinuousDensitySourceOnly

open MeasureTheory SchwartzMap Set
open scoped SchwartzMap
open EvenFourierHilbertSourceOnly EvenL1L2DensitySourceOnly

/-- Actual L2 classes having smooth compactly supported representatives. -/
def compactSmoothClasses : Set ComplexL2 :=
  {v | ∃ g : ℝ → ℂ, (v : ℝ → ℂ) =ᵐ[volume] g ∧
    HasCompactSupport g ∧ ContDiff ℝ ∞ g}

private theorem denseRange_compactSmoothClasses :
    DenseRange (fun v : compactSmoothClasses => (v : ComplexL2)) := by
  have hr : Set.range (fun v : compactSmoothClasses => (v : ComplexL2)) =
      compactSmoothClasses := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  intro f
  rw [hr]
  exact Lp.dense_hasCompactSupport_contDiff (p := 2) ENNReal.ofNat_ne_top f

/-- Symmetrize compact smooth L2 classes in the actual even subspace. -/
def evenCompactEmbedding (v : compactSmoothClasses) : evenL2 :=
  evenProjectionSubspace (v : ComplexL2)

theorem denseRange_evenCompactEmbedding : DenseRange evenCompactEmbedding := by
  exact evenProjectionSubspace_surjective.denseRange.comp
    denseRange_compactSmoothClasses continuous_evenProjectionSubspace

private theorem evenSchwartzProfile_continuous (g : 𝓢(ℝ, ℂ)) :
    Continuous (evenSchwartzProfile g) := by
  change Continuous (fun x : ℝ => (1 / 2 : ℂ) • (g x + g (-x)))
  exact continuous_const.smul (g.continuous.add (g.continuous.comp continuous_neg))

private theorem evenSchwartzProfile_hasCompactSupport (g : 𝓢(ℝ, ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    HasCompactSupport (evenSchwartzProfile g) := by
  have hn : HasCompactSupport (fun x : ℝ => g (-x)) :=
    hg.comp_isClosedEmbedding
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toHomeomorph.isClosedEmbedding
  exact (hg.add hn).smul_left (f := fun _ : ℝ => (1 / 2 : ℂ))

/-- Every actual even L2 class admits an actual compactly supported
continuous pointwise-even approximation in any positive L2 error. -/
theorem exists_even_compact_continuous_approx (f : evenL2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ∃ hg : MemLp g 2,
      Continuous g ∧ HasCompactSupport g ∧
        (∀ x : ℝ, g (-x) = g x) ∧ ‖hg.toLp g - (f : ComplexL2)‖ < ε := by
  obtain ⟨v, hv⟩ := denseRange_evenCompactEmbedding.exists_dist_lt f hε
  obtain ⟨g, hvg, hgc, hgd⟩ := v.property
  let G : 𝓢(ℝ, ℂ) := hgc.toSchwartzMap hgd
  have hG : HasCompactSupport (G : ℝ → ℂ) := hgc
  have hvG : (v : ComplexL2) = G.toLp 2 volume := by
    apply Lp.ext
    exact hvg.trans (G.coeFn_toLp 2 volume).symm
  have hvG' : evenCompactEmbedding v = evenSchwartzEmbedding G := by
    change evenProjectionSubspace (v : ComplexL2) =
      evenProjectionSubspace (G.toLp 2 volume)
    exact congrArg evenProjectionSubspace hvG
  rw [hvG'] at hv
  refine ⟨evenSchwartzProfile G, evenSchwartzProfile_memLp G,
    evenSchwartzProfile_continuous G,
    evenSchwartzProfile_hasCompactSupport G hG, evenSchwartzProfile_even G, ?_⟩
  change dist (f : ComplexL2) (evenSchwartzEmbedding G : ComplexL2) < ε at hv
  rw [dist_eq_norm, norm_sub_rev, evenSchwartzEmbedding_coe] at hv
  exact hv

end ImbalancedChen.Part3.EvenCompactContinuousDensitySourceOnly
