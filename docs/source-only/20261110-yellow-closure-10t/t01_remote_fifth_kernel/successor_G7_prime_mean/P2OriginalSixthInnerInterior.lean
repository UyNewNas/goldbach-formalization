import ImbalancedChen.P2OriginalSixthCompactTrim
import Mathlib.Analysis.Convex.Measure

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The original physical simplexes are convex images in SIX dimensions.
The existing Haar theorem makes their frontiers null. Hence almost every
point of the exact original finite union is an INTERIOR point of that
same union. No guessed face ledger or numerical volume is used here.
-/
namespace ImbalancedChen.P2OriginalSixthInnerInterior
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (archive)
open P2OriginalSixthSimplexFloorIntegral (support)
open P2OriginalSixthPullingUnion (originalInnerUnion)

theorem canonical_convex : Convex ℝ P2OriginalSixthSimplexMoments.canonical := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_,?_⟩
  · intro j
    change 0≤a*x j+b*y j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · change (∑ j : Fin 6,a*x j+b*y j)≤1
    calc
      _ = a*(∑ j : Fin 6,x j)+b*(∑ j : Fin 6,y j) := by
        simp only [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by linarith

theorem physical_support_convex (L : Point ≃L[ℝ] Point) (b : Point) :
    Convex ℝ (P2OriginalSixthSimplexMoments.support L b) := by
  have h := (canonical_convex.linear_image L.toContinuousLinearMap.toLinearMap).translate b
  simpa only [Set.image_image,Function.comp_def] using h

theorem original_support_frontier_null (i : Fin 11) (s : Fin (archive i).simplices.size) :
    volume (frontier (support i s))=0 :=
  (physical_support_convex _ _).addHaar_frontier volume

def originalSimplexFrontiers (i : Fin 11) : Set Point :=
  ⋃ s : Fin (archive i).simplices.size, frontier (support i s)

theorem original_simplex_frontiers_null (i : Fin 11) : volume (originalSimplexFrontiers i)=0 :=
  measure_iUnion_null (original_support_frontier_null i)

theorem original_union_off_frontiers_interior (i : Fin 11) :
    originalInnerUnion i \ originalSimplexFrontiers i ⊆ interior (originalInnerUnion i) := by
  rintro t ⟨ht,hf⟩
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  have hi : t∈interior (support i s) := by
    by_contra hni
    apply hf
    refine mem_iUnion.mpr ⟨s,?_⟩
    rw [frontier,(P2OriginalSixthSimplexMoments.support_compact _ _).isClosed.closure_eq]
    exact ⟨hs,hni⟩
  exact interior_mono (fun x hx => mem_iUnion.mpr ⟨s,hx⟩) hi

theorem original_union_ae_interior (i : Fin 11) :
    ∀ᵐ t : Point ∂volume, t∈originalInnerUnion i → t∈interior (originalInnerUnion i) := by
  have hf : ∀ᵐ t : Point ∂volume, t∉originalSimplexFrontiers i := by
    rw [ae_iff]
    simpa only [not_not] using original_simplex_frontiers_null i
  filter_upwards [hf] with t ht hs
  exact original_union_off_frontiers_interior i ⟨hs,ht⟩

end
end ImbalancedChen.P2OriginalSixthInnerInterior
