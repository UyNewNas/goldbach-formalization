import ImbalancedChen.P2OriginalSixthSimplexFloorIntegral
import ImbalancedChen.P2OriginalSaving16PullingFaceInduction
import ImbalancedChen.AffinePrimeGates

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Original seven-vertex pulling rows in genuine6D. The old8D pulling
induction is used only to construct separating affine rows, after a6→8
zero embedding. Every determinant, support and volume remains6D.
This proves an integral over the actual original inner union, without
assuming disjointness or silently asserting complete-cell membership.
-/
namespace ImbalancedChen.P2OriginalSixthPullingUnion
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalSixthLogArchive
open P2OriginalSixthSimplexFloorIntegral (support cellSimplexIntegral)
open P2OriginalSixthSimplexBinding (QPoint castPoint)
open P2OriginalSixthMomentRow (Point rowMeasure rowDensity row_reciprocal_integrable)
open P2OriginalSixthSimplexMoments (interpolate pointInterpolate pointInterpolate_apply
  interpolate_add interpolate_const interpolate_sum bary_nonneg support_measurable)
open P2OriginalSaving16PullingFaceInduction (Shape pull pull_pair_separated)
abbrev Affine := Fin 7 → ℚ
def evalQ (a : Affine) (x : QPoint) : ℚ := a 0+∑ j, a j.succ*x j
def eval (a : Affine) (x : Point) : ℝ := (a 0:ℝ)+∑ j, (a j.succ:ℝ)*x j
theorem eval_cast (a : Affine) (x : QPoint) : eval a (castPoint x) = (evalQ a x:ℝ) := by
  simp [eval,evalQ,castPoint]

/-- Compose an original chart-coordinate affine gate with the inverse
physical chart. Pair12 source coordinates already are physical. -/
def physicalGate (c : ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell) (a : Affine) : Affine :=
  if c.family = .pair12 then a else
    ![a 0+(a 4+a 5)/2,a 1-(a 4+a 5)/2,a 2-a 4-a 5,
      a 3-a 4-a 5,-a 4-a 5,-a 4-3*a 5,a 6]

def gate (i : Fin 11) (g : Fin (archive i).rawGates.size) : Affine :=
  physicalGate (sourceCell i) (fun j => (archive i).rawGates[g].getD j.val 0)
def facet (i : Fin 11) (f : Fin (archive i).facets.size) := (archive i).facets[f].toList
def faceRecord (i : Fin 11) (face : List Nat) : Face :=
  ((archive i).faces.toList.find? (fun f => f.vertices.toList == face)).getD default
def pivot (i : Fin 11) (face : List Nat) := (faceRecord i face).pivot
def children (i : Fin 11) (face : List Nat) : List (List Nat) :=
  ((faceRecord i face).facetSets.toList.map Array.toList).filter
    (fun child => !(child.contains (pivot i face)))
def whole (i : Fin 11) := List.range (archive i).vertices.size
def rows (i : Fin 11) := (archive i).simplices.toList.map (fun s => s.vertexIds.toList)

def Checks (i : Fin 11) : Prop :=
  (∀ g : Fin (archive i).rawGates.size, (archive i).rawGates[g].size = 7 ∧
    ∀ v : Fin (archive i).vertices.size, 0 ≤ evalQ (gate i g) (vertex i v)) ∧
  (∀ f : Fin (archive i).facets.size, ∃ g : Fin (archive i).rawGates.size,
    ∀ v : Fin (archive i).vertices.size, v.val ∈ facet i f ↔ evalQ (gate i g) (vertex i v) = 0) ∧
  Shape (facet i) (pivot i) (children i) 7 (whole i) ∧
  pull (pivot i) (children i) 7 (whole i) = rows i ∧ (rows i).Nodup
instance (i : Fin 11) : Decidable (Checks i) := by unfold Checks; infer_instance

/-- Closed primitive incidence/recursion checks on the ORIGINAL face and
simplex lists. They have not been executed in this authoring session. -/
theorem original_pulling_checks : ∀ i, Checks i := by decide

def embed (x : QPoint) : P2OriginalSaving16OriginalArchive.QPoint :=
  ![x 0,x 1,x 2,x 3,x 4,x 5,0,0]
def lift (a : Affine) : Fin 9 → ℚ := ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,0,0]
def restrict (a : Fin 9 → ℚ) : Affine := fun j => a j.castSucc.castSucc
theorem restrict_lift (a : Affine) : restrict (lift a) = a := by
  funext j
  fin_cases j <;> rfl
theorem eval_embed (a : Fin 9 → ℚ) (x : QPoint) :
    P2OriginalSaving16OriginalArchive.evalQ a (embed x) = evalQ (restrict a) x := by
  norm_num [P2OriginalSaving16OriginalArchive.evalQ,embed,evalQ,restrict,Fin.sum_univ_succ]

private theorem id_mem (i : Fin 11) (s : Fin (archive i).simplices.size) (k : Fin 7) :
    (archive i).simplices[s].vertexIds.getD k.val 0 ∈ (archive i).simplices[s].vertexIds.toList := by
  have hk : k.val < (archive i).simplices[s].vertexIds.size :=
    (original_primitive_rows i s).2.1.symm ▸ k.isLt
  rw [← Array.getElem_eq_getD (h := hk) 0]
  exact Array.getElem_mem_toList hk
private theorem row_mem (i : Fin 11) (s : Fin (archive i).simplices.size) :
    (archive i).simplices[s].vertexIds.toList ∈ pull (pivot i) (children i) 7 (whole i) := by
  rw [(original_pulling_checks i).2.2.2.1]
  exact List.mem_map.mpr ⟨_,Array.getElem_mem_toList s.isLt,rfl⟩
private theorem row_ne (i : Fin 11) (s t : Fin (archive i).simplices.size) (hst : s ≠ t) :
    (archive i).simplices[s].vertexIds.toList ≠ (archive i).simplices[t].vertexIds.toList := by
  intro he
  have hs : s.val < (rows i).length := by simpa [rows] using s.isLt
  have ht : t.val < (rows i).length := by simpa [rows] using t.isLt
  have he' : (rows i)[s.val] = (rows i)[t.val] := by simpa [rows] using he
  exact hst (Fin.ext ((List.getElem_inj (h₀ := hs) (h₁ := ht)
    (original_pulling_checks i).2.2.2.2).mp he'))

theorem original_rows_separated (i : Fin 11) (s t : Fin (archive i).simplices.size) (hst : s ≠ t) :
    ∃ a : Affine, (∀ k, evalQ a (rowVertices i s k) ≤ 0) ∧
      (∀ k, 0 ≤ evalQ a (rowVertices i t k)) ∧ ∃ x : Point, eval a x ≠ 0 := by
  let h := original_pulling_checks i
  choose g hg using h.2.1
  let V := fun v : Nat => embed (vertex i v)
  let G := fun f : Fin (archive i).facets.size => lift (gate i (g f))
  have he f v : P2OriginalSaving16OriginalArchive.evalQ (G f) (V v) =
      evalQ (gate i (g f)) (vertex i v) := by
    rw [show G f = lift (gate i (g f)) from rfl,show V v = embed (vertex i v) from rfl,
      eval_embed,restrict_lift]
  have hp f v (hv : v ∈ whole i) : 0 ≤ P2OriginalSaving16OriginalArchive.evalQ (G f) (V v) := by
    rw [he]
    exact (h.1 (g f)).2 ⟨v,by simpa [whole] using hv⟩
  have hf f v (hv : v ∈ whole i) : v ∈ facet i f ↔
      P2OriginalSaving16OriginalArchive.evalQ (G f) (V v) = 0 := by
    rw [he]
    exact hg f ⟨v,by simpa [whole] using hv⟩
  obtain ⟨a,hs,ht,v,_,hav⟩ := pull_pair_separated V G (facet i) (whole i)
    (pivot i) (children i) hp hf (fun _ hz => hz) h.2.2.1
    (row_mem i s) (row_mem i t) (row_ne i s t hst)
  refine ⟨restrict a,?_,?_,castPoint (vertex i v),?_⟩
  · intro k
    simpa only [V,eval_embed,rowVertices] using hs _ (id_mem i s k)
  · intro k
    simpa only [V,eval_embed,rowVertices] using ht _ (id_mem i t k)
  · rw [eval_cast]
    have hh : evalQ (restrict a) (vertex i v) ≠ 0 := by simpa only [V,eval_embed] using hav
    exact_mod_cast hh

theorem eval_interpolate (a : Affine) (v : Fin 7 → Point) (x : Point) :
    eval a (pointInterpolate v x) = interpolate (fun k => eval a (v k)) x := by
  simp only [eval,pointInterpolate_apply]
  rw [interpolate_add,interpolate_const,interpolate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [interpolate,Finset.mul_sum,mul_assoc,mul_left_comm]
private theorem eval_on (i : Fin 11) (s : Fin (archive i).simplices.size) (a : Affine)
    {x : Point} (hx : x ∈ support i s) :
    ∃ y ∈ P2OriginalSixthSimplexMoments.canonical,
      eval a x = interpolate (fun k => (evalQ a (rowVertices i s k):ℝ)) y := by
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y,hy,?_⟩
  rw [← P2OriginalSixthSimplexMoments.vertices_interpolate,
    P2OriginalSixthSimplexBinding.edge_vertices,eval_interpolate]
  simp only [eval_cast]
private theorem nonneg_on (i : Fin 11) (s : Fin (archive i).simplices.size) (a : Affine)
    (h : ∀ k, 0 ≤ evalQ a (rowVertices i s k)) {x : Point} (hx : x ∈ support i s) : 0 ≤ eval a x := by
  obtain ⟨y,hy,he⟩ := eval_on i s a hx
  rw [he]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (bary_nonneg hy k) (by exact_mod_cast h k)
private theorem nonpos_on (i : Fin 11) (s : Fin (archive i).simplices.size) (a : Affine)
    (h : ∀ k, evalQ a (rowVertices i s k) ≤ 0) {x : Point} (hx : x ∈ support i s) : eval a x ≤ 0 := by
  obtain ⟨y,hy,he⟩ := eval_on i s a hx
  rw [he]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos
    (bary_nonneg hy k) (by exact_mod_cast h k)

def linearPart (a : Affine) : Point →L[ℝ] ℝ := ∑ j : Fin 6, (a j.succ:ℝ) • ContinuousLinearMap.proj j
theorem eval_eq_affine (a : Affine) (x : Point) : eval a x = (a 0:ℝ)+linearPart a x := by
  simp [eval,linearPart]
theorem affine_zero_volume (a : Affine) (h : ∃ x : Point, eval a x ≠ 0) : volume {x | eval a x = 0} = 0 := by
  by_cases hL : linearPart a = 0
  · obtain ⟨x,hx⟩ := h
    have hc : (a 0:ℝ) ≠ 0 := by simpa [eval_eq_affine,hL] using hx
    have he : {x : Point | eval a x = 0} = ∅ := by ext y; simp [eval_eq_affine,hL,hc]
    rw [he,measure_empty]
  · have he : {x : Point | eval a x = 0} = {x | linearPart a x = -(a 0:ℝ)} := by
      ext x
      simp only [mem_setOf_eq,eval_eq_affine]
      constructor <;> intro hx <;> linarith
    rw [he]
    exact affinePrimeWall_volume_zero (linearPart a) hL _

theorem within_cell_null (i : Fin 11) {s t : Fin (archive i).simplices.size} (hst : s ≠ t) :
    volume (support i s ∩ support i t) = 0 := by
  obtain ⟨a,hs,ht,ha⟩ := original_rows_separated i s t hst
  exact measure_mono_null (fun _ hx => le_antisymm
    (nonpos_on i s a hs hx.1) (nonneg_on i t a ht hx.2)) (affine_zero_volume a ha)

def originalInnerUnion (i : Fin 11) : Set Point := ⋃ s : Fin (archive i).simplices.size, support i s

theorem kernel_integrable_on_row (i : Fin 11) (s : Fin (archive i).simplices.size) :
    IntegrableOn (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i)) (support i s) := by
  let r := (physicalRow i s).toRow
  change Integrable (ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel (sourceCell i)) (rowMeasure r)
  have h := (row_reciprocal_integrable r).const_mul 4
  convert h using 1
  funext x
  rw [show r = (physicalRow i s).toRow from rfl,
    P2OriginalSixthPhysicalRow.rowGap_eq]
  simp_rw [P2OriginalSixthPhysicalRow.rowFactors_eq]
  simp only [ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.savingKernel,ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.factorProduct,mul_div_assoc]

/-- Null overlap is removed explicitly before finite additivity. This is
an equality of actual six-dimensional Lebesgue integrals, not an iterated
integral definition or a sum accepted as a source-measure premise. -/
theorem integral_original_inner_union (i : Fin 11) :
    ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (originalInnerUnion i) = cellSimplexIntegral i := by
  let A := fun s : Fin (archive i).simplices.size => support i s
  let overlap : Set Point := ⋃ s : Fin (archive i).simplices.size,
    ⋃ t : Fin (archive i).simplices.size, if s = t then ∅ else A s ∩ A t
  let good := fun s => A s \ overlap
  have ha (s : Fin (archive i).simplices.size) : MeasurableSet (A s) := support_measurable _ _
  have hn : volume overlap = 0 := by
    apply measure_iUnion_null
    intro s
    apply measure_iUnion_null
    intro t
    by_cases he : s = t
    · simp [he]
    · simp only [if_neg he]
      exact within_cell_null i he
  have hm : MeasurableSet overlap := by
    apply MeasurableSet.iUnion
    intro s
    apply MeasurableSet.iUnion
    intro t
    by_cases he : s = t
    · simp [he]
    · simp only [if_neg he]
      exact (ha s).inter (ha t)
  have hd : Pairwise (fun s t => Disjoint (good s) (good t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    rintro x ⟨hs,hs'⟩ ⟨ht,_⟩
    apply hs'
    exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨t,by simpa only [if_neg hst] using And.intro hs ht⟩⟩
  have hne : ∀ᵐ x : Point ∂volume, x ∉ overlap := by
    rw [ae_iff]
    simpa only [not_not] using hn
  have hae (s : Fin (archive i).simplices.size) : good s =ᵐ[volume] A s := by
    filter_upwards [hne] with x hx
    simp [good,hx]
  have hU := integral_iUnion_fintype (fun s => (ha s).diff hm) hd
    (fun s => (kernel_integrable_on_row i s).mono_set Set.diff_subset)
  have hSet : originalInnerUnion i =ᵐ[volume] ⋃ s, good s := by
    filter_upwards [hne] with x hx
    simp only [originalInnerUnion,mem_iUnion,good,mem_diff,A]
    simp [hx]
  unfold ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral
  rw [setIntegral_congr_set hSet,hU]
  exact Finset.sum_congr rfl (fun s _ => setIntegral_congr_set (hae s))

/-- Full original Q96 replacement floor on the eleven actual inner
unions. No old total is added and no extra physical Jacobian is applied.
Comparison to PhysicalCell or the admitted same-policy occurrence source
still requires its own source/history theorem. -/
theorem original_all2631_inner_union_floor :
    (1208544915921356327515701 : ℝ)/(2:ℝ)^96 ≤
      ∑ i : Fin 11, ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (originalInnerUnion i) := by
  simp_rw [integral_original_inner_union]
  exact P2OriginalSixthSimplexFloorIntegral.original_all2631_stored_floor

end
end ImbalancedChen.P2OriginalSixthPullingUnion
