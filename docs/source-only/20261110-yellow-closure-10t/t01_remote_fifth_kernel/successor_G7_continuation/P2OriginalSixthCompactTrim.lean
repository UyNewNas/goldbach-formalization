import ImbalancedChen.P2OriginalSixthOwnedPhysicalIntegral

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Compact trims of the ACTUAL original inner unions, using only a uniform
positive margin on the original strict source rows. Weak licence identities
remain weak. These are not substitute cells or new geometric coverage.
-/
namespace ImbalancedChen.P2OriginalSixthCompactTrim
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (archive sourceCell)
open P2OriginalSixthPullingUnion (eval originalInnerUnion)
def margins (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (delta : ℝ) : Set Point :=
  {t | ∀ g : ImbalancedChen.P2OriginalSixthPhysicalGateRows.Gate, if g.strict then delta ≤ eval (ImbalancedChen.P2OriginalSixthPhysicalGateRows.row c g) t else 0 ≤ eval (ImbalancedChen.P2OriginalSixthPhysicalGateRows.row c g) t}
def trim (i : Fin 11) (delta : ℝ) : Set Point := originalInnerUnion i ∩ margins (sourceCell i) delta

theorem eval_continuous (a : P2OriginalSixthPullingUnion.Affine) : Continuous (eval a) := by
  simp only [P2OriginalSixthPullingUnion.eval_eq_affine]
  fun_prop

theorem margins_closed (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (delta : ℝ) : IsClosed (margins c delta) := by
  have he : margins c delta=⋂ g : ImbalancedChen.P2OriginalSixthPhysicalGateRows.Gate,
      {t | if g.strict then delta ≤ eval (ImbalancedChen.P2OriginalSixthPhysicalGateRows.row c g) t else 0 ≤ eval (ImbalancedChen.P2OriginalSixthPhysicalGateRows.row c g) t} := by
    ext t
    simp [margins]
  rw [he]
  apply isClosed_iInter
  intro g
  cases hg : g.strict <;> simp only [hg,if_false,if_true]
  all_goals exact isClosed_le continuous_const (eval_continuous _)

private theorem compact_finite_union {ι : Type*} (s : Finset ι) (A : ι → Set Point)
    (h : ∀ i ∈ s, IsCompact (A i)) : IsCompact (⋃ i ∈ s,A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have he : (⋃ j ∈ insert i s,A j)=A i ∪ ⋃ j ∈ s,A j := by ext t; simp
      rw [he]
      exact (h i (Finset.mem_insert_self _ _)).union hs

theorem inner_compact (i : Fin 11) : IsCompact (originalInnerUnion i) := by
  have h := compact_finite_union (Finset.univ : Finset (Fin (archive i).simplices.size))
    (P2OriginalSixthSimplexFloorIntegral.support i)
    (fun s _ => P2OriginalSixthSimplexMoments.support_compact _ _)
  simpa [originalInnerUnion] using h

theorem trim_compact (i : Fin 11) (delta : ℝ) : IsCompact (trim i delta) :=
  (inner_compact i).inter_right (margins_closed (sourceCell i) delta)

theorem trim_subset_source (i : Fin 11) {delta : ℝ} (hdelta : 0<delta) :
    trim i delta ⊆ {t | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t} := by
  rintro t ⟨_,ht⟩
  apply (ImbalancedChen.P2OriginalSixthPhysicalGateRows.physicalCell_iff_rows (sourceCell i) t).mpr
  intro g
  have hh := ht g
  cases hg : g.strict
  · simpa only [hg,if_false] using hh
  · simp only [hg,if_true] at hh ⊢
    exact hdelta.trans_le hh

theorem strict_margin {i : Fin 11} {delta : ℝ} {t : Point} (ht : t ∈ trim i delta)
    (g : ImbalancedChen.P2OriginalSixthPhysicalGateRows.Gate) (hg : g.strict=true) : delta ≤ ImbalancedChen.P2OriginalSixthPhysicalGateRows.value (sourceCell i) g t := by
  have h := ht.2 g
  rw [hg,if_true,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_row] at h
  exact h

theorem trim_margins {i : Fin 11} {delta : ℝ} {t : Point} (ht : t∈trim i delta) :
    delta ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu-t 0 ∧ delta ≤ t 0-t 1 ∧ delta ≤ t 1-t 2 ∧
    delta ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H3 t ∧ delta ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.H5 t ∧ delta ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0 t-ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.S6 t-t 5 := by
  exact ⟨strict_margin ht .largest rfl,strict_margin ht (.order 0) rfl,
    strict_margin ht (.order 1) rfl,strict_margin ht .history3 rfl,
    strict_margin ht .history5 rfl,strict_margin ht .oldArgument rfl⟩

theorem trim_antitone (i : Fin 11) : Antitone (trim i) := by
  intro a b hab t ht
  refine ⟨ht.1,?_⟩
  intro g
  have hh := ht.2 g
  cases hg : g.strict <;> simp only [hg,if_true,if_false] at hh ⊢
  · exact hh
  · exact hab.trans hh

end
end ImbalancedChen.P2OriginalSixthCompactTrim
