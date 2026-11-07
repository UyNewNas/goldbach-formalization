import ImbalancedChen.Part3ActualHeckeCanonicalCarrierMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Genuine complex L1 integration over the actual finite Hecke cover. Each
translated-cell integrability premise is derived from the original cover
integrability, and actual canonical-volume substitution pays every term.
The proved canonical carrier bridge then gives the actual prime-level
quotient integral as the p+1 physical cover-branch integral. No divergent
Bochner equality or supplied absolute-branch-integrability premise.
-/

namespace ImbalancedChen.Part3.ActualHeckeComplexCoverIntegral20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualHeckeCorrespondenceCarrier20261026b
open ActualHeckeCanonicalCarrierMeasure20261026b Gamma0CarrierAESection20261025a
open Gamma0QuotientCellPushforward20261025a

theorem coverProjection_measurePreserving (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    MeasurePreserving (orbitProjection (N*p))
      ((volume : Measure UpperHalfPlane).restrict (correspondenceCarrier N p hp hpN))
      (carrierPushforward (N*p)) :=
  ⟨orbitProjection_measurable (N*p), correspondenceCarrier_pushforward_eq N p hp hpN⟩

theorem correspondenceCarrier_integral (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : UpperHalfPlane → ℂ) (hi : IntegrableOn f (correspondenceCarrier N p hp hpN)) :
    (∫ z in correspondenceCarrier N p hp hpN, f z) =
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∫ z in reducedCarrier N, ∑ j : Branch p, f (coverAction N p hp hpN j z) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hcell (j : Branch p) : IntegrableOn f (coverCell N p hp hpN j) :=
    hi.mono_set (fun z hz => mem_iUnion.mpr ⟨j,hz⟩)
  have hmp (j : Branch p) := (coverAction_measurePreserving N p hp hpN j).restrict_image_emb
    (coverAction_measurableEmbedding N p hp hpN j) (reducedCarrier N)
  have hcomp (j : Branch p) : IntegrableOn (f ∘ coverAction N p hp hpN j) (reducedCarrier N) :=
    (hmp j).integrable_comp_of_integrable (hcell j)
  have heq (j : Branch p) : (∫ z in coverCell N p hp hpN j, f z) =
      ∫ z in reducedCarrier N, f (coverAction N p hp hpN j z) :=
    ((hmp j).integral_comp (coverAction_measurableEmbedding N p hp hpN j) f).symm
  rw [correspondenceCarrier, integral_iUnion_fintype (coverCell_measurable N p hp hpN)
    (fun j k hjk => coverCell_disjoint N p hp hpN hjk) hcell]
  simp_rw [heq]
  exact (integral_finsetSum Finset.univ (fun j hj => hcomp j)).symm

theorem canonical_cover_integrable (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (F : Gamma0OrbitSpace (N*p) → ℂ)
    (hF : Integrable F (carrierPushforward (N*p))) :
    IntegrableOn (F ∘ orbitProjection (N*p)) (correspondenceCarrier N p hp hpN) :=
  (coverProjection_measurePreserving N p hp hpN).integrable_comp_of_integrable hF

/-- True quotient complex L1 integral unfolded over the actual relative
cover. Integrability is supplied only for the original quotient observable. -/
theorem canonical_cover_integral (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (F : Gamma0OrbitSpace (N*p) → ℂ)
    (hF : Integrable F (carrierPushforward (N*p))) :
    (∫ q, F q ∂carrierPushforward (N*p)) =
      letI : NeZero p := ⟨hp.ne_zero⟩
      ∫ z in reducedCarrier N, ∑ j : Branch p,
        F (orbitProjection (N*p) (coverAction N p hp hpN j z)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hm : AEStronglyMeasurable F
      (((volume : Measure UpperHalfPlane).restrict (correspondenceCarrier N p hp hpN)).map
        (orbitProjection (N*p))) := by
    change AEStronglyMeasurable F (cellPushforward (N*p) (correspondenceCarrier N p hp hpN))
    rw [correspondenceCarrier_pushforward_eq N p hp hpN]
    exact hF.aestronglyMeasurable
  have hmap := integral_map (orbitProjection_measurable (N*p)).aemeasurable hm
  change (∫ q, F q ∂cellPushforward (N*p) (correspondenceCarrier N p hp hpN)) =
    ∫ z in correspondenceCarrier N p hp hpN, F (orbitProjection (N*p) z) at hmap
  rw [correspondenceCarrier_pushforward_eq N p hp hpN] at hmap
  exact hmap.trans (correspondenceCarrier_integral N p hp hpN _
    (canonical_cover_integrable N p hp hpN F hF))

end
end ImbalancedChen.Part3.ActualHeckeComplexCoverIntegral20261026b
