import ImbalancedChen.P2OriginalSixthPhysicalGateRows

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Every actual original simplex lies inside its TRUE PhysicalCell after
removing finitely many proper strict source walls. The only finite inputs
are checks of rational affine evaluations at ORIGINAL physical vertices;
membership, nullness, geometric cover and integral bounds are not inputs.
-/
namespace ImbalancedChen.P2OriginalSixthInnerPhysicalCell
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthLogArchive
open P2OriginalSixthSimplexFloorIntegral (support)
open P2OriginalSixthPullingUnion (Affine eval evalQ eval_cast eval_interpolate affine_zero_volume originalInnerUnion)
open P2OriginalSixthSimplexBinding (castPoint)
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthSimplexMoments (interpolate bary_nonneg)
open P2OriginalSixthPhysicalGateRows (Gate row)
/-- Closed original-vertex arithmetic; UNEVALUATED. This uses all source
conditions, not only the proposed original supporting facets. -/
theorem original_vertices_closed_rows : ∀ (i : Fin 11) (v : Fin (archive i).vertices.size) (g : Gate),
    0 ≤ evalQ (row (sourceCell i) g) (vertex i v) := by decide

/-- A nonzero witness for every STRICT source wall; UNEVALUATED. Weak
zero licence identities are not incorrectly turned into strict walls. -/
theorem original_strict_rows_proper : ∀ (i : Fin 11) (g : Gate), g.strict=true →
    ∃ v : Fin (archive i).vertices.size, 0 < evalQ (row (sourceCell i) g) (vertex i v) := by decide

def walls (i : Fin 11) : Set Point :=
  ⋃ g : Gate, if g.strict then {t | eval (row (sourceCell i) g) t=0} else ∅

theorem walls_null (i : Fin 11) : volume (walls i)=0 := by
  apply measure_iUnion_null
  intro g
  cases hg : g.strict
  · simp [hg]
  · simp only [hg,if_true]
    obtain ⟨v,hv⟩ := original_strict_rows_proper i g hg
    apply affine_zero_volume
    refine ⟨castPoint (vertex i v),?_⟩
    rw [eval_cast]
    have hp : (0:ℝ) < (evalQ (row (sourceCell i) g) (vertex i v):ℝ) := by exact_mod_cast hv
    exact hp.ne'

theorem eval_nonneg_on_original_support (i : Fin 11) (s : Fin (archive i).simplices.size)
    (g : Gate) {t : Point} (ht : t ∈ support i s) : 0 ≤ eval (row (sourceCell i) g) t := by
  obtain ⟨x,hx,rfl⟩ := ht
  rw [← P2OriginalSixthSimplexMoments.vertices_interpolate,
    P2OriginalSixthSimplexBinding.edge_vertices,eval_interpolate]
  unfold interpolate
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (bary_nonneg hx k)
  rw [eval_cast]
  have hk := (original_primitive_rows i s).2.2.1 k
  exact_mod_cast original_vertices_closed_rows i
    ⟨(archive i).simplices[s].vertexIds.getD k.val 0,hk⟩ g

theorem support_off_walls_physicalCell (i : Fin 11) (s : Fin (archive i).simplices.size) :
    support i s \ walls i ⊆ {t | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t} := by
  rintro t ⟨ht,hw⟩
  apply (P2OriginalSixthPhysicalGateRows.physicalCell_iff_rows (sourceCell i) t).mpr
  intro g
  have hnonneg := eval_nonneg_on_original_support i s g ht
  cases hg : g.strict
  · simpa only [hg,if_false] using hnonneg
  · have hne : eval (row (sourceCell i) g) t ≠ 0 := by
      intro he
      apply hw
      exact mem_iUnion.mpr ⟨g,by simp only [hg,if_true,mem_setOf_eq]; exact he⟩
    simpa only [hg,if_true] using lt_of_le_of_ne hnonneg hne.symm

theorem innerUnion_off_walls_physicalCell (i : Fin 11) :
    originalInnerUnion i \ walls i ⊆ {t | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t} := by
  rintro t ⟨ht,hw⟩
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  exact support_off_walls_physicalCell i s ⟨hs,hw⟩

/-- The requested original inner-union inclusion, with its actual null
boundary exposed. There is no caller-supplied source-membership port. -/
theorem original_inner_union_ae_physicalCell (i : Fin 11) :
    ∀ᵐ t : Point ∂volume, t ∈ originalInnerUnion i → ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t := by
  have hw : ∀ᵐ t : Point ∂volume, t ∉ walls i := by
    rw [ae_iff]
    simpa only [not_not] using walls_null i
  filter_upwards [hw] with t ht hmem
  exact innerUnion_off_walls_physicalCell i ⟨hmem,ht⟩

theorem original_inner_union_outside_source_null (i : Fin 11) :
    volume (originalInnerUnion i \ {t | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t})=0 := by
  apply measure_mono_null _ (walls_null i)
  rintro t ⟨ht,hs⟩
  by_contra hw
  exact hs (innerUnion_off_walls_physicalCell i ⟨ht,hw⟩)

end
end ImbalancedChen.P2OriginalSixthInnerPhysicalCell
