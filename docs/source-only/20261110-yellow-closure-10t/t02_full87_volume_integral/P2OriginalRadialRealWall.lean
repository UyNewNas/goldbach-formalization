import ImbalancedChen.P2OriginalSaving15RadialProfile

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Necessary real affine separator for the original radial staircase.
The null-wall fact is the existing affinePrimeWall_volume_zero theorem.
No integral lower bound or simplex disjointness is assumed here.
-/
namespace ImbalancedChen.P2OriginalRadialRealWall
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSaving16OriginalArchive (castPoint)
open P2OriginalPhysicalSimplexMomentRow (Point Row rowMap rowBase rowSupport row_vertices)
namespace Bary
export P2OriginalSaving19SimplexMoments
  (interpolate bary bary_sum bary_nonneg pointInterpolate vertices_interpolate)
end Bary

structure Wall where
  linear : Point →L[ℝ] ℝ
  constant : ℝ
def Wall.eval (w : Wall) (t : Point) : ℝ := w.constant+w.linear t

theorem Wall.proper_of_linear_ne_zero (w : Wall) (hL : w.linear ≠ 0) :
    ∃ t : Point, w.eval t ≠ 0 := by
  by_contra h
  push_neg at h
  have hc : w.constant = 0 := by simpa [Wall.eval] using h 0
  apply hL
  ext t
  simpa [Wall.eval,hc] using h t

theorem Wall.eval_interpolate (w : Wall) (v : Fin 9 → Point) (x : Point) :
    w.eval (Bary.pointInterpolate v x) = Bary.interpolate (fun i => w.eval (v i)) x := by
  unfold Wall.eval Bary.pointInterpolate Bary.interpolate
  simp only [map_sum,map_smul,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,Bary.bary_sum,one_mul]

theorem Wall.zero_null (w : Wall) (hw : ∃ t : Point, w.eval t ≠ 0) :
    (volume : Measure Point) {t | w.eval t = 0} = 0 := by
  by_cases hL : w.linear = 0
  · obtain ⟨t,ht⟩ := hw
    have hc : w.constant ≠ 0 := by simpa [Wall.eval,hL] using ht
    have he : {t : Point | w.eval t = 0} = ∅ := by ext t; simp [Wall.eval,hL,hc]
    rw [he,measure_empty]
  · have he : {t : Point | w.eval t = 0} = {t | w.linear t = -w.constant} := by
      ext t
      simp only [mem_setOf_eq,Wall.eval]
      constructor <;> intro h <;> linarith
    rw [he]
    exact affinePrimeWall_volume_zero w.linear hL _

theorem Wall.nonneg_on_support (w : Wall) (r : Row)
    (hv : ∀ i, 0 ≤ w.eval (castPoint (r.verticesQ i)))
    {t : Point} (ht : t ∈ rowSupport r) : 0 ≤ w.eval t := by
  obtain ⟨x,hx,rfl⟩ := ht
  rw [← Bary.vertices_interpolate,Wall.eval_interpolate,row_vertices]
  change 0 ≤ ∑ i, Bary.bary i x * w.eval (castPoint (r.verticesQ i))
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Bary.bary_nonneg hx i) (hv i))

theorem Wall.nonpos_on_support (w : Wall) (r : Row)
    (hv : ∀ i, w.eval (castPoint (r.verticesQ i)) ≤ 0)
    {t : Point} (ht : t ∈ rowSupport r) : w.eval t ≤ 0 := by
  obtain ⟨x,hx,rfl⟩ := ht
  rw [← Bary.vertices_interpolate,Wall.eval_interpolate,row_vertices]
  change (∑ i, Bary.bary i x * w.eval (castPoint (r.verticesQ i))) ≤ 0
  exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (Bary.bary_nonneg hx i) (hv i))

theorem Wall.separated_supports_null (w : Wall) (r s : Row)
    (hr : ∀ i, w.eval (castPoint (r.verticesQ i)) ≤ 0)
    (hs : ∀ i, 0 ≤ w.eval (castPoint (s.verticesQ i)))
    (hw : ∃ t : Point, w.eval t ≠ 0) :
    (volume : Measure Point) (rowSupport r ∩ rowSupport s) = 0 := by
  apply measure_mono_null (t := {t : Point | w.eval t = 0})
  · rintro t ⟨htr,hts⟩
    exact le_antisymm (w.nonpos_on_support r hr htr) (w.nonneg_on_support s hs hts)
  · exact w.zero_null hw

def fromQ (a : Fin 9 → ℚ) : Wall where
  linear := P2OriginalSaving19OwnedSource.linearPart a
  constant := (a 0 : ℝ)
theorem fromQ_eval (a : Fin 9 → ℚ) (t : Point) :
    (fromQ a).eval t = P2OriginalSaving19OwnedSource.eval a t :=
  (P2OriginalSaving19OwnedSource.eval_eq_affine a t).symm
theorem fromQ_cast (a : Fin 9 → ℚ) (t : Fin 8 → ℚ) :
    (fromQ a).eval (castPoint t) = (P2OriginalSaving16OriginalArchive.evalQ a t : ℝ) := by
  rw [fromQ_eval]
  exact P2OriginalSaving19OwnedSource.eval_cast a t

def Wall.neg (w : Wall) : Wall where
  linear := -w.linear
  constant := -w.constant
theorem Wall.neg_eval (w : Wall) (t : Point) : w.neg.eval t = -w.eval t := by
  simp [Wall.neg,Wall.eval]

end
end ImbalancedChen.P2OriginalRadialRealWall
