import ImbalancedChen.P1OriginalFourthAllRowsAdmission

/-! SOURCE_ONLY / UNCOMPILED.
One positive margin for ALL original fourth rows, selected before any
target or prime tuple. It uses the existing actual correlated endpoint
tests. It does not replace them by independent interval subtraction.
-/
namespace ImbalancedChen.P1OriginalFourthUniformRowMargins
noncomputable section
open scoped Classical BigOperators
open Set
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthPackedTable
open P1OriginalFourthAllRowsAdmission
open P2OriginalFourthCapProducerInterface

abbrev MarginIndex := (Fin 2) ⊕ (Bool ⊕ ((Bool × Fin 4) ⊕ (Bool × Fin 4)))

def rowMargin (r : ProducerRow) : MarginIndex → ℝ
  | .inl i => if i = 0 then gapLower r.selected r.lower r.upper else oldCubeLower r.lower r.upper
  | .inr (.inl side) => (((tentPlane r.selected side).sub halfGate).lower r.lower r.upper : ℝ)
  | .inr (.inr (.inl (side,j))) =>
      (((tentPlane r.selected side).sub (fullGate j)).lower r.lower r.upper : ℝ)
  | .inr (.inr (.inr (side,j))) => if j ∈ r.selected then 1 else
      (((tentPlane r.selected side).sub (selectedGate r.selected j)).lower r.lower r.upper : ℝ)

theorem rowMargin_pos (r : ProducerRow) (hr : r ∈ originalRows4) (i : MarginIndex) :
    0 < rowMargin r i := by
  rcases originalRows4_geometry r hr with
    ⟨_,_,_,_,_,_,hgap,hcube,hgates,_,_⟩
  rcases i with i | i
  · fin_cases i
    · simpa only [rowMargin,if_pos rfl] using hgap
    · simpa only [rowMargin,show (1 : Fin 2) ≠ 0 by decide,if_false] using hcube
  · rcases i with side | i
    · exact hgates.1 side
    · rcases i with ⟨side,j⟩ | ⟨side,j⟩
      · exact hgates.2.1 side j
      · by_cases hj : j ∈ r.selected
        · simp only [rowMargin,if_pos hj]; norm_num
        · simpa only [rowMargin,if_neg hj] using hgates.2.2 side j hj

def marginValues : Finset ℝ :=
  insert 1 ((originalRows4.product (Finset.univ : Finset MarginIndex)).image
    (fun x => rowMargin x.1 x.2))
def commonMargin : ℝ := marginValues.inf'
  (show marginValues.Nonempty from ⟨1,Finset.mem_insert_self _ _⟩) id

theorem commonMargin_pos : 0 < commonMargin := by
  unfold commonMargin
  apply (Finset.lt_inf'_iff _).mpr
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · norm_num
  · obtain ⟨⟨r,i⟩,hri,rfl⟩ := Finset.mem_image.mp hv
    exact rowMargin_pos r (Finset.mem_product.mp hri).1 i

theorem commonMargin_le_row (r : ProducerRow) (hr : r ∈ originalRows4) (i : MarginIndex) :
    commonMargin ≤ rowMargin r i := by
  apply Finset.inf'_le id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(r,i),Finset.mem_product.mpr ⟨hr,Finset.mem_univ _⟩,rfl⟩

theorem cube_gap (r : ProducerRow) (hr : r ∈ originalRows4) (t : Point) (ht : t ∈ r.box) :
    oldCube.eval t + commonMargin ≤ oldCap t := by
  have hm : commonMargin ≤ oldCubeLower r.lower r.upper := by
    simpa only [rowMargin,show (1 : Fin 2) ≠ 0 by decide,if_false] using
      commonMargin_le_row r hr (.inl 1)
  have hb := oldCubeLower_le r.lower r.upper t ht.1 ht.2
  linarith

private theorem gate_margin (r : ProducerRow) (g : Affine)
    (hg : ∀ side : Bool, commonMargin ≤ ((tentPlane r.selected side).sub g).lower r.lower r.upper)
    (t : Point) (ht : t ∈ r.box) :
    g.eval t + commonMargin ≤ r.candidate t := by
  apply le_min
  · have hl := ((tentPlane r.selected false).sub g).lower_le_eval r.lower r.upper t ht.1 ht.2
    rw [Affine.eval_sub] at hl
    have hm := hg false
    linarith
  · have hl := ((tentPlane r.selected true).sub g).lower_le_eval r.lower r.upper t ht.1 ht.2
    rw [Affine.eval_sub] at hl
    have hm := hg true
    linarith

/-- Every original row passes all ACTUAL buffered gates simultaneously
when the one common e satisfies 2e<commonMargin. The old cube margin is
kept separate; a positive average gap is never a pointwise licence. -/
theorem buffered_row_gates (r : ProducerRow) (hr : r ∈ originalRows4)
    (e : ℝ) (he : 2*e < commonMargin) (t : Point) (ht : t ∈ r.box) :
    oldCap t < r.bufferedCandidate e t ∧
      (1/2 : ℝ) < r.bufferedCandidate e t ∧
      (∀ j, prefixSquareExpr t j < r.bufferedCandidate e t) ∧
      (∀ j ∉ r.selected, selectedSquareExpr r.selected t j < r.bufferedCandidate e t) := by
  have hgap : commonMargin ≤ gapLower r.selected r.lower r.upper := by
    simpa only [rowMargin,if_pos rfl] using commonMargin_le_row r hr (.inl 0)
  have hpoint := gapLower_le_actual_gap r.selected r.lower r.upper t ht.1 ht.2
  change gapLower r.selected r.lower r.upper ≤ r.candidate t-oldCap t at hpoint
  have hhalf := gate_margin r halfGate
    (fun side => commonMargin_le_row r hr (.inr (.inl side))) t ht
  rw [halfGate_eval] at hhalf
  refine ⟨?_,?_,?_,?_⟩
  · change oldCap t < r.candidate t-2*e
    linarith
  · change (1/2 : ℝ) < r.candidate t-2*e
    linarith
  · intro j
    have h := gate_margin r (fullGate j)
      (fun side => commonMargin_le_row r hr (.inr (.inr (.inl (side,j))))) t ht
    rw [fullGate_eval] at h
    change prefixSquareExpr t j < r.candidate t-2*e
    linarith
  · intro j hj
    have h := gate_margin r (selectedGate r.selected j) (fun side => by
      have hm := commonMargin_le_row r hr (.inr (.inr (.inr (side,j))))
      simpa only [rowMargin,if_neg hj] using hm) t ht
    rw [selectedGate_eval] at h
    change selectedSquareExpr r.selected t j < r.candidate t-2*e
    linarith

end
end ImbalancedChen.P1OriginalFourthUniformRowMargins
