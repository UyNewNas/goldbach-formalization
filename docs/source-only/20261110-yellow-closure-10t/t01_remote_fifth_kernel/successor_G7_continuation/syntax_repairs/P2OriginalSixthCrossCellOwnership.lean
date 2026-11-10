import ImbalancedChen.P2OriginalSixthInnerPhysicalCell

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The ORIGINAL eleven cells have pairwise null overlap. Opposite old
branches are incompatible below the true tent peak. The same-comparison
residual cases are separated by the original mask/tent priorities. Distinct
comparison formulas can meet only on their explicit proper affine tie wall.
No pairwise-disjointness field or archived PASS claim is an input.
-/
namespace ImbalancedChen.P2OriginalSixthCrossCellOwnership
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthPullingUnion (Affine eval evalQ affine_zero_volume originalInnerUnion)
open P2OriginalSixthPhysicalGateRows (old)
open P2OriginalSixthLogArchive (sourceCell)
def comparisonKind (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Fin 3 := match c.family with
  | .singleton | .tent33 => 0 | .pair17 => 1 | .pair12 => 2

theorem oldCap_lt_peak {c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point} (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t < 153/256 := by
  have hw := hc.winner
  have hl := hc.largest
  cases hf : c.family <;>
    simp only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,hf,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0] at hw ⊢
  all_goals dsimp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.mu] at hl hw
  all_goals linarith

/-- Both caps are the maximum of the very same original first-five
subset tents and W. This uses the original attained winner, not an
assumed equality between the inherited buffered parent and raw cap. -/
theorem comparison_eq {c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point}
    (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) (hd : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell d t) : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap d t := by
  obtain ⟨m,hm,he⟩ := hc.raw_envelope.2.2
  obtain ⟨n,hn,hf⟩ := hd.raw_envelope.2.2
  exact le_antisymm (he ▸ hd.raw_envelope.2.1 m hm) (hf ▸ hc.raw_envelope.2.1 n hn)

theorem opposite_branches_false {c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point}
    (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) (hd : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell d t) (m : ℕ)
    (hm : m ∈ Finset.Icc 1 31) (hb : c.descending m ≠ d.descending m) : False := by
  have hR := comparison_eq hc hd
  have hp := oldCap_lt_peak hc
  have hleft := hc.oldBranches m hm
  have hright := hd.oldBranches m hm
  rw [← hR] at hright
  cases hl : c.descending m <;> cases hr : d.descending m <;>
    simp only [hl,hr,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.branchLicense,if_true,if_false] at hleft hright hb
  all_goals first | exact hb rfl | linarith

def residual (c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Prop :=
  c.family=.singleton ∧
    ((c.selectedMask=33 ∧ d.family=.singleton ∧ (d.selectedMask=34 ∨ d.selectedMask=50)) ∨
     ((c.selectedMask=33 ∨ c.selectedMask=34) ∧ d.family=.tent33))
instance (c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) : Decidable (residual c d) := by unfold residual; infer_instance

/-- A closed eleven-by-eleven LABEL/BRANCH identity, UNEVALUATED.
It does not inspect real points or assert geometric non-overlap. -/
theorem same_comparison_label_cases (c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (hk : comparisonKind c=comparisonKind d) (hne : c ≠ d) :
    (∃ m ∈ Finset.Icc 1 31, c.descending m ≠ d.descending m) ∨ residual c d ∨ residual d c := by
  cases c <;> cases d <;>
    simp_all [comparisonKind,residual,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask]
  all_goals decide

theorem selected_sum33 (t : Point) : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum 33 t=t 0+t 5 := by
  norm_num [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit,Fin.sum_univ_succ]
theorem selected_sum34 (t : Point) : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum 34 t=t 1+t 5 := by
  norm_num [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.bit,Fin.sum_univ_succ]

theorem residual_false {c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} {t : Point}
    (hc : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) (hd : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell d t) (hr : residual c d) : False := by
  rcases hr with ⟨hcf,hres⟩
  have hcnew : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap c t=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap t := by simp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,hcf]
  rcases hres with ⟨hcm,hdf,hdm⟩ | ⟨hcm,hdf⟩
  · have hdnew : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap d t=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap t := by simp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap,hdf]
    have hprior : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.descending33 t < ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.newCap d t := by
      have hh := hd.priority
      cases d <;> simp_all [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.priority]
    have hsel := hc.selectedDescending
    rw [hcm,selected_sum33,hcnew] at hsel
    rw [hdnew] at hprior
    dsimp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.descending33] at hprior
    linarith
  · have hprior : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33 t < ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.clippedCap t := by
      have hh := hd.priority
      cases d <;> simp_all [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.priority]
    have hsel := hc.selectedAscending
    rw [hcnew] at hsel
    rcases hcm with hcm | hcm
    · rw [hcm,selected_sum33] at hsel
      dsimp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33] at hprior
      linarith
    · rw [hcm,selected_sum34] at hsel
      have ho := hc.order.2.2.2.2
      dsimp [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.ascending33] at hprior
      linarith

theorem same_comparison_disjoint {c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (hk : comparisonKind c=comparisonKind d) (hne : c ≠ d) :
    Disjoint {t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t} {t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell d t} := by
  apply Set.disjoint_left.mpr
  intro t hc hd
  rcases same_comparison_label_cases c d hk hne with ⟨m,hm,hb⟩ | hr | hr
  · exact opposite_branches_false hc hd m hm hb
  · exact residual_false hc hd hr
  · exact residual_false hd hc hr

theorem eval_old (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : Point) : eval (old c) t=ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  cases c <;> simp [old,ImbalancedChen.P2OriginalSixthPhysicalGateRows.r0,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_add,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_sub,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_smul,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_constant,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_coord,
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.oldCap,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.R0]
  all_goals ring

/-- Distinct comparison TYPES have genuinely different rational affine
coefficients. This finite algebraic identity is UNEVALUATED. -/
theorem distinct_comparison_coefficients (c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (hk : comparisonKind c ≠ comparisonKind d) :
    ∃ j : Fin 7, (old c-old d) j ≠ 0 := by
  cases c <;> cases d <;> simp_all [comparisonKind,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell.family]
  all_goals decide

theorem affine_nonzero_of_coefficient {a : Affine} (h : ∃ j, a j ≠ 0) : ∃ t : Point, eval a t ≠ 0 := by
  by_cases h0 : a 0=0
  · obtain ⟨j,hj⟩ := h
    revert hj
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj
      exact False.elim (hj h0)
    · intro hj
      refine ⟨Pi.single k 1,?_⟩
      have hh : (a k.succ:ℝ) ≠ 0 := by exact_mod_cast hj
      simpa [eval,h0,Pi.single_apply,mul_ite] using hh
  · refine ⟨0,?_⟩
    have hh : (a 0:ℝ) ≠ 0 := by exact_mod_cast h0
    simpa [eval] using hh

theorem physical_cells_pairwise_null {c d : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell} (hne : c ≠ d) :
    volume ({t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t} ∩ {t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell d t})=0 := by
  by_cases hk : comparisonKind c=comparisonKind d
  · rw [(same_comparison_disjoint hk hne).inter_eq,measure_empty]
  · apply measure_mono_null _ (affine_zero_volume (old c-old d)
      (affine_nonzero_of_coefficient (distinct_comparison_coefficients c d hk)))
    rintro t ⟨hc,hd⟩
    simp only [mem_setOf_eq,ImbalancedChen.P2OriginalSixthPhysicalGateRows.eval_sub,eval_old,comparison_eq hc hd,sub_self]

theorem sourceCell_injective : Function.Injective sourceCell := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sourceCell]

/-- Cross-cell null overlap of the ACTUAL original inner unions. Both
directions of source inclusion are proved above from original vertices. -/
theorem original_inner_unions_pairwise_null {i j : Fin 11} (hij : i ≠ j) :
    volume (originalInnerUnion i ∩ originalInnerUnion j)=0 := by
  have hsource : sourceCell i ≠ sourceCell j := fun h => hij (sourceCell_injective h)
  let E := P2OriginalSixthInnerPhysicalCell.walls i ∪ P2OriginalSixthInnerPhysicalCell.walls j ∪
    ({t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell i) t} ∩ {t : Point | ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell (sourceCell j) t})
  have hE : volume E=0 := measure_union_null
    (measure_union_null (P2OriginalSixthInnerPhysicalCell.walls_null i)
      (P2OriginalSixthInnerPhysicalCell.walls_null j)) (physical_cells_pairwise_null hsource)
  apply measure_mono_null _ hE
  rintro t ⟨hi,hj⟩
  by_cases hwi : t ∈ P2OriginalSixthInnerPhysicalCell.walls i
  · exact Or.inl (Or.inl hwi)
  by_cases hwj : t ∈ P2OriginalSixthInnerPhysicalCell.walls j
  · exact Or.inl (Or.inr hwj)
  exact Or.inr ⟨P2OriginalSixthInnerPhysicalCell.innerUnion_off_walls_physicalCell i ⟨hi,hwi⟩,
    P2OriginalSixthInnerPhysicalCell.innerUnion_off_walls_physicalCell j ⟨hj,hwj⟩⟩

end
end ImbalancedChen.P2OriginalSixthCrossCellOwnership
