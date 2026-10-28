import ImbalancedChen.P2N48RetainedPriorityRemainder

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original priority-subdivision source maps each n48 parent index i to
n96 index 2*i+bit. High t is never permuted with the three low slots.
These are actual half-open physical children with the adopted mask.
No numerical row, parent/child list or saved-floor check is evaluated.
-/
namespace ImbalancedChen.P2N48PriorityHalfGridDictionary
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48OriginalStrictLogMassAndOmegaPorts
open P5Z.U11Canonical P5Z.U1011OriginalSixteenU10Geometry

abbrev HalfBits := Fin 4→Fin 2

def rowIndex (r : SourceRow) (j : Fin 4) : Fin 48 :=
  if j=0 then r.ix else if j=1 then r.iy else if j=2 then r.iz else r.iw

def childIndex (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℕ :=
  2*(rowIndex r j).val+(b j).val

theorem childIndex_lt96 (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    childIndex r b j<96 := by
  have h := (rowIndex r j).isLt
  have hb := (b j).isLt
  unfold childIndex
  omega

def wireLeft96 (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℕ :=
  if j=0 ∧ r.term.val=1 then 760*96+420*childIndex r b j
  else 417*96+343*childIndex r b j

def wireRight96 (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℕ :=
  wireLeft96 r b j+width r j

/-- Actual source integer dictionary, before real normalization. -/
theorem original_child_endpoint_dictionary (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    wireLeft96 r b j=2*leftEnd r j+(b j).val*width r j ∧
      wireRight96 r b j=2*leftEnd r j+((b j).val+1)*width r j := by
  have ht := r.term.isLt
  by_cases hzero : r.term.val=0
  · fin_cases j <;>
      simp [wireLeft96,wireRight96,childIndex,rowIndex,leftEnd,width,lowLo,highLo,hzero] <;> ring
  · have hone : r.term.val=1 := by omega
    fin_cases j <;>
      simp [wireLeft96,wireRight96,childIndex,rowIndex,leftEnd,width,lowLo,highLo,hzero,hone] <;> ring

def rowMid (r : SourceRow) (j : Fin 4) : ℝ := (rowLower r j+rowUpper r j)/2

def childLower (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℝ :=
  if b j=0 then rowLower r j else rowMid r j

def childUpper (r : SourceRow) (b : HalfBits) (j : Fin 4) : ℝ :=
  if b j=0 then rowMid r j else rowUpper r j

/-- The rational n96 endpoints are precisely the original half intervals. -/
theorem original_child_real_endpoint_dictionary (r : SourceRow) (b : HalfBits) (j : Fin 4) :
    childLower r b j=(wireLeft96 r b j : ℝ)/480000 ∧
      childUpper r b j=(wireRight96 r b j : ℝ)/480000 := by
  obtain ⟨hl,hu⟩ := original_child_endpoint_dictionary r b j
  have hb := (b j).isLt
  by_cases hz : b j=0
  · simp [childLower,childUpper,hz,rowMid,rowLower,rowUpper,hl,hu,rightEnd]
    <;> push_cast <;> ring
  · have ho : b j=1 := by
      apply Fin.ext
      have hn : (b j).val≠0 := fun h => hz (Fin.ext h)
      omega
    simp [childLower,childUpper,hz,ho,rowMid,rowLower,rowUpper,hl,hu,rightEnd]
    <;> push_cast <;> ring

def childBox (r : SourceRow) (b : HalfBits) : Set LogFour :=
  logPrimeBox (childLower r b) (childUpper r b)

def childSelectedParent (r : SourceRow) (b : HalfBits) : Set LogFour :=
  childBox r b ∩ (if r.term.val=0 then domain10 else originalDomain actualMask)

theorem measurableSet_childBox (r : SourceRow) (b : HalfBits) : MeasurableSet (childBox r b) :=
  measurableSet_logPrimeBox _ _

theorem measurableSet_childSelectedParent (r : SourceRow) (b : HalfBits) :
    MeasurableSet (childSelectedParent r b) := by
  by_cases ht : r.term.val=0
  · simpa [childSelectedParent,ht] using (measurableSet_childBox r b).inter measurableSet_domain10
  · have hD : MeasurableSet (originalDomain actualMask) := by
      exact measurableSet_originalDomain _ (by
        change MeasurableSet Certificates.PairedV2.FullMask.P1E0E1.pairRegion
        rw [←P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_all]
        exact Finset.measurableSet_biUnion _ (fun _ _ =>
          (measurableSet_le measurable_const measurable_fst).inter
            ((measurableSet_lt measurable_fst measurable_const).inter
              ((measurableSet_le measurable_const measurable_snd).inter
                (measurableSet_lt measurable_snd measurable_const)))))
    simpa [childSelectedParent,ht] using (measurableSet_childBox r b).inter hD

theorem childSelectedParent_subset_parent (r : SourceRow) (b : HalfBits) :
    childSelectedParent r b⊆selectedParent r actualMask := by
  intro v hv
  refine ⟨mem_logPrimeBox.mpr ?_,hv.2⟩
  intro j
  have h := mem_logPrimeBox.mp hv.1 j
  have hm0 : rowLower r j≤rowMid r j := by dsimp [rowMid]; linarith [rowLower_le_upper r j]
  have hm1 : rowMid r j≤rowUpper r j := by dsimp [rowMid]; linarith [rowLower_le_upper r j]
  by_cases hb : b j=0
  · have hl : rowLower r j≤v j := by simpa [childLower,hb] using h.1
    have hu : v j<rowMid r j := by simpa [childUpper,hb] using h.2
    simpa only [rowLower,rowUpper] using And.intro hl (hu.trans_le hm1)
  · have hl : rowLower r j≤v j := hm0.trans (by simpa [childLower,hb] using h.1)
    have hu : v j<rowUpper r j := by simpa [childUpper,hb] using h.2
    simpa only [rowLower,rowUpper] using And.intro hl hu

theorem parent_eq_all_half_children (r : SourceRow) :
    selectedParent r actualMask=⋃ b : HalfBits,childSelectedParent r b := by
  ext v
  constructor
  · intro hv
    let b : HalfBits := fun j => if v j<rowMid r j then 0 else 1
    refine mem_iUnion.mpr ⟨b,⟨mem_logPrimeBox.mpr ?_,hv.2⟩⟩
    intro j
    have h := mem_logPrimeBox.mp hv.1 j
    by_cases hm : v j<rowMid r j
    · have hh : rowLower r j≤v j ∧ v j<rowMid r j :=
        ⟨by simpa only [rowLower] using h.1,hm⟩
      simpa [b,childLower,childUpper,hm] using hh
    · have hh : rowMid r j≤v j ∧ v j<rowUpper r j :=
        ⟨le_of_not_gt hm,by simpa only [rowUpper] using h.2⟩
      simpa [b,childLower,childUpper,hm] using hh
  · intro hv
    obtain ⟨b,hb⟩ := mem_iUnion.mp hv
    exact childSelectedParent_subset_parent r b hb

theorem half_children_disjoint (r : SourceRow) {b c : HalfBits} (hbc : b≠c) :
    Disjoint (childSelectedParent r b) (childSelectedParent r c) := by
  have hn : ∃ j,b j≠c j := by
    by_contra hn
    apply hbc
    funext j
    exact not_not.mp (not_exists.mp hn j)
  obtain ⟨j,hj⟩ := hn
  apply Set.disjoint_left.mpr
  intro v hvb hvc
  have hb := mem_logPrimeBox.mp hvb.1 j
  have hc := mem_logPrimeBox.mp hvc.1 j
  by_cases hb0 : b j=0
  · have hc0 : c j≠0 := fun h => hj (hb0.trans h.symm)
    have hlt : v j<rowMid r j := by simpa [childUpper,hb0] using hb.2
    have hle : rowMid r j≤v j := by simpa [childLower,hc0] using hc.1
    exact (not_lt_of_ge hle) hlt
  · have hc0 : c j=0 := by
      apply Fin.ext
      have hbN := (b j).isLt
      have hcN := (c j).isLt
      have hbNZ : (b j).val≠0 := fun h => hb0 (Fin.ext h)
      have hne : (b j).val≠(c j).val := fun h => hj (Fin.ext h)
      omega
    have hlt : v j<rowMid r j := by simpa [childUpper,hc0] using hc.2
    have hle : rowMid r j≤v j := by simpa [childLower,hb0] using hb.1
    exact (not_lt_of_ge hle) hlt

def originalHighAllowed (r : SourceRow) (b : HalfBits) : Prop :=
  childIndex r b 2≤childIndex r b 1 ∧ childIndex r b 3≤childIndex r b 2

instance (r : SourceRow) (b : HalfBits) : Decidable (originalHighAllowed r b) := by
  unfold originalHighAllowed
  infer_instance

def originalHighChildren (r : SourceRow) : Finset HalfBits :=
  Finset.univ.filter (originalHighAllowed r)

/-- This is the source's weak-order filter on the three LOW child indices.
The first high coordinate does not enter it. -/
theorem actual_high_child_allowed (r : SourceRow) (ht : r.term.val=1)
    (b : HalfBits) {v : LogFour} (hv : v∈childSelectedParent r b) : originalHighAllowed r b := by
  have hD : v∈originalDomain actualMask := by simpa [childSelectedParent,ht] using hv.2
  have hb := mem_logPrimeBox.mp hv.1
  have hE := original_child_real_endpoint_dictionary r b
  have h12 : childIndex r b 2≤childIndex r b 1 := by
    by_contra hbad
    have hidx : childIndex r b 1+1≤childIndex r b 2 := by omega
    have hwire : wireRight96 r b 1≤wireLeft96 r b 2 := by
      simp [wireRight96,wireLeft96,width]
      omega
    have hsep : childUpper r b 1≤childLower r b 2 := by
      rw [(hE 1).2,(hE 2).1]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hwire) (by norm_num)
    linarith only [(hb 1).2,(hb 2).1,hsep,hD.2.2.1]
  have h23 : childIndex r b 3≤childIndex r b 2 := by
    by_contra hbad
    have hidx : childIndex r b 2+1≤childIndex r b 3 := by omega
    have hwire : wireRight96 r b 2≤wireLeft96 r b 3 := by
      simp [wireRight96,wireLeft96,width]
      omega
    have hsep : childUpper r b 2≤childLower r b 3 := by
      rw [(hE 2).2,(hE 3).1]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hwire) (by norm_num)
    linarith only [(hb 2).2,(hb 3).1,hsep,hD.2.1]
  exact ⟨h12,h23⟩

theorem high_parent_eq_original_children (r : SourceRow) (ht : r.term.val=1) :
    selectedParent r actualMask=⋃ b∈originalHighChildren r,childSelectedParent r b := by
  rw [parent_eq_all_half_children]
  ext v
  constructor
  · intro hv
    obtain ⟨b,hb⟩ := mem_iUnion.mp hv
    refine mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨?_,hb⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,actual_high_child_allowed r ht b hb⟩
  · intro hv
    obtain ⟨b,hb⟩ := mem_iUnion.mp hv
    obtain ⟨_,hbv⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨b,hbv⟩

end
end ImbalancedChen.P2N48PriorityHalfGridDictionary
