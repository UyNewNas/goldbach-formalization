import ImbalancedChen.P2OriginalLaterSixthArchive
import ImbalancedChen.P2OriginalSixthPullingUnion

/-! Pulling incidence of the archived twenty-one pieces. Only containment
of each selected simplex in the pulling list is needed. The archived row
order and vertex permutations do not affect the volume or its floor. -/
namespace ImbalancedChen.P2OriginalLaterSixthOwnedIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive
open P2OriginalSixthSimplexBinding (QPoint castPoint)
open P2OriginalSixthSimplexMoments (Point bary_nonneg support_measurable)
open P2OriginalSixthMomentRow (rowSupport rowMeasure row_reciprocal_integrable)
open P2OriginalSaving16PullingFaceInduction (Shape pull pull_pair_separated)
open P2OriginalSixthPullingUnion (embed lift restrict eval_embed restrict_lift affine_zero_volume)

def support (i : Piece) (s : Individual i) : Set Point := rowSupport (physicalRow i s).toRow
def inner (i : Piece) : Set Point := ⋃ s : Individual i,support i s
def pieceIntegral (i : Piece) : ℝ := sourceIntegral i (inner i)

def chartGate (i : Piece) (a : Plane) : Plane :=
  if charted i then
    ![a 0+(a 4+a 5)/2,a 1-(a 4+a 5)/2,a 2-a 4-a 5,
      a 3-a 4-a 5,-a 4-a 5,-a 4-3*a 5,a 6]
  else a
def gate (i : Piece) (g : Fin (bank i).gates.size) : Plane :=
  chartGate i (fun j => (bank i).gates[g].getD j.val 0)
def facet (i : Piece) (f : Fin (bank i).facets.size) := (bank i).facets[f].toList
def faceRecord (i : Piece) (f : List Nat) := ((bank i).faces.toList.find? (fun r => r.vertices.toList == f)).getD default
def pivot (i : Piece) (f : List Nat) := (faceRecord i f).pivot
def children (i : Piece) (f : List Nat) :=
  ((faceRecord i f).facetSets.toList.map Array.toList).filter (fun y => !(y.contains (pivot i f)))
def whole (i : Piece) := List.range (bank i).vertices.size
def pulled (i : Piece) := pull (pivot i) (children i) 7 (whole i)
def keys (i : Piece) := (bank i).simplices.toList.map (fun r => r.ids.toList.toFinset)

def Incidence (i : Piece) : Prop :=
  (∀ g : Fin (bank i).gates.size,∀ v : Fin (bank i).vertices.size,0≤evalQ (gate i g) (vertex i v)) ∧
  (∀ f : Fin (bank i).facets.size,∃ g : Fin (bank i).gates.size,
    ∀ v : Fin (bank i).vertices.size,v.val∈facet i f ↔ evalQ (gate i g) (vertex i v)=0) ∧
  Shape (facet i) (pivot i) (children i) 7 (whole i) ∧
  (∀ s : Individual i,∃ v∈pulled i,v.toFinset=(sx i s).ids.toList.toFinset) ∧ (keys i).Nodup
instance (i : Piece) : Decidable (Incidence i) := by unfold Incidence; infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem incidence (i : Piece) : Incidence i := by fin_cases i <;> decide

theorem id_mem (i : Piece) (s : Individual i) (k : Fin 7) :
    (sx i s).ids.getD k.val 0 ∈ (sx i s).ids.toList := by
  have hk : k.val<(sx i s).ids.size := by rw [(original_primitive i s).idCount]; exact k.isLt
  rw [←Array.getElem_eq_getD (h:=hk) 0]
  exact Array.getElem_mem_toList hk

private theorem key_ne (i : Piece) (s t : Individual i) (hne : s≠t) :
    (sx i s).ids.toList.toFinset≠(sx i t).ids.toList.toFinset := by
  intro he
  have hs : s.val<(keys i).length := by simpa [keys] using s.isLt
  have ht : t.val<(keys i).length := by simpa [keys] using t.isLt
  have h : (keys i)[s.val]=(keys i)[t.val] := by simpa [keys,sx] using he
  exact hne (Fin.ext ((List.getElem_inj (h₀:=hs) (h₁:=ht) (incidence i).2.2.2.2).mp h))

theorem separator (i : Piece) (s t : Individual i) (hne : s≠t) :
    ∃ a : Plane,(∀ k,evalQ a (rowVertices i s k)≤0) ∧ (∀ k,0≤evalQ a (rowVertices i t k)) ∧
      ∃ x : Point,eval a x≠0 := by
  let h := incidence i
  choose g hg using h.2.1
  let V := fun v : Nat => embed (vertex i v)
  let G := fun f : Fin (bank i).facets.size => lift (gate i (g f))
  have he f v : P2OriginalSaving16OriginalArchive.evalQ (G f) (V v)=evalQ (gate i (g f)) (vertex i v) := by
    change P2OriginalSaving16OriginalArchive.evalQ (lift (gate i (g f))) (embed (vertex i v)) =
      P2OriginalSixthPullingUnion.evalQ (gate i (g f)) (vertex i v)
    rw [eval_embed,restrict_lift]
  have hp f v (hv : v∈whole i) : 0≤P2OriginalSaving16OriginalArchive.evalQ (G f) (V v) := by
    rw [he]; exact h.1 (g f) ⟨v,by simpa [whole] using hv⟩
  have hf f v (hv : v∈whole i) : v∈facet i f ↔ P2OriginalSaving16OriginalArchive.evalQ (G f) (V v)=0 := by
    rw [he]; exact hg f ⟨v,by simpa [whole] using hv⟩
  obtain ⟨s',hs',es⟩ := h.2.2.2.1 s
  obtain ⟨t',ht',et⟩ := h.2.2.2.1 t
  have hne' : s'≠t' := by rintro rfl; exact key_ne i s t hne (es.symm.trans et)
  obtain ⟨a,hs,ht,v,_,hv⟩ := pull_pair_separated V G (facet i) (whole i) (pivot i) (children i)
    hp hf (fun _ hz => hz) h.2.2.1 hs' ht' hne'
  refine ⟨restrict a,?_,?_,castPoint (vertex i v),?_⟩
  · intro k
    have hm : (sx i s).ids.getD k.val 0∈s' := by
      rw [←List.mem_toFinset,es,List.mem_toFinset]; exact id_mem i s k
    simpa only [V,eval_embed,rowVertices] using hs _ hm
  · intro k
    have hm : (sx i t).ids.getD k.val 0∈t' := by
      rw [←List.mem_toFinset,et,List.mem_toFinset]; exact id_mem i t k
    simpa only [V,eval_embed,rowVertices] using ht _ hm
  · rw [eval_cast]
    have hh : evalQ (restrict a) (vertex i v)≠0 := by simpa only [V,eval_embed] using hv
    exact_mod_cast hh

theorem nonneg_on (i : Piece) (s : Individual i) (a : Plane) (h : ∀ k,0≤evalQ a (rowVertices i s k))
    {t : Point} (ht : t∈support i s) : 0≤eval a t := by
  let r := physicalRow i s
  have H := physical_eval r a t
  rw [←H]
  obtain ⟨y,hy,he⟩ := ht
  have hcoord : P2OriginalSixthMomentRow.rowCoordinates r.toRow t=y := by
    rw [←he]
    simp [P2OriginalSixthMomentRow.rowCoordinates]
  rw [hcoord]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (bary_nonneg hy k) (by exact_mod_cast h k))

theorem nonpos_on (i : Piece) (s : Individual i) (a : Plane) (h : ∀ k,evalQ a (rowVertices i s k)≤0)
    {t : Point} (ht : t∈support i s) : eval a t≤0 := by
  have hneg : ∀ k,0≤evalQ (-a) (rowVertices i s k) := by
    intro k; simpa [evalQ,Finset.sum_neg_distrib] using neg_nonneg.mpr (h k)
  simpa [eval,Finset.sum_neg_distrib] using (nonneg_on i s (-a) hneg ht)

theorem within_null (i : Piece) (s t : Individual i) (h : s≠t) :
    volume (support i s ∩ support i t)=0 := by
  obtain ⟨a,h1,h2,ha⟩ := separator i s t h
  exact measure_mono_null (fun x hx => le_antisymm (nonpos_on i s a h1 hx.1) (nonneg_on i t a h2 hx.2))
    (affine_zero_volume a ha)

theorem row_integrable (i : Piece) (s : Individual i) : IntegrableOn (kernel i) (support i s) := by
  let r := (physicalRow i s).toRow
  have hi := (row_reciprocal_integrable r).const_mul 4
  change Integrable (kernel i) (rowMeasure r)
  convert hi using 1
  funext x
  rw [←row_density (physicalRow i s)]
  simp [r,P2OriginalSixthMomentRow.rowDensity,mul_div_assoc]

theorem pairwise_null_integral {ι : Type*} [Fintype ι] (A : ι → Set Point) (f : Point→ℝ)
    (hm : ∀ i,MeasurableSet (A i)) (hi : ∀ i,IntegrableOn f (A i))
    (hn : ∀ i j,i≠j→volume (A i∩A j)=0) :
    (∫ t in ⋃ i,A i,f t) = ∑ i,∫ t in A i,f t := by
  classical
  let overlap : Set Point := ⋃ i,⋃ j,if i=j then ∅ else A i∩A j
  let good := fun i => A i \ overlap
  have null : volume overlap=0 := by
    apply measure_iUnion_null; intro i
    apply measure_iUnion_null; intro j
    by_cases e : i=j
    · simp [e]
    · simpa only [if_neg e] using hn i j e
  have meas : MeasurableSet overlap := by
    apply MeasurableSet.iUnion; intro i
    apply MeasurableSet.iUnion; intro j
    by_cases e : i=j
    · simp [e]
    · simpa only [if_neg e] using (hm i).inter (hm j)
  have dis : Pairwise (fun i j => Disjoint (good i) (good j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨hai,hout⟩ ⟨haj,_⟩
    exact hout (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa only [if_neg hij] using And.intro hai haj⟩⟩)
  have ha : ∀ᵐ x : Point ∂volume,x∉overlap := by rw [ae_iff]; simpa only [not_not] using null
  have eqS (i : ι) : good i=ᵐ[volume] A i := by filter_upwards [ha] with t ht; simp [good,ht]
  have eqU : (⋃ i,A i)=ᵐ[volume] ⋃ i,good i := by
    filter_upwards [ha] with t ht
    simp [good,ht]
  rw [setIntegral_congr_set eqU,integral_iUnion_fintype (fun i => (hm i).diff meas) dis
    (fun i => (hi i).mono_set Set.diff_subset)]
  exact Finset.sum_congr rfl (fun i _ => setIntegral_congr_set (eqS i))

theorem piece_is_sum (i : Piece) : pieceIntegral i=∑ s : Individual i,sourceIntegral i (support i s) :=
  pairwise_null_integral (support i) (kernel i) (fun _ => support_measurable _ _) (row_integrable i) (within_null i)

theorem original_seven_slot_inner_floor (j : Fin 7) :
    currentUpperEighteenGains ⟨7+j.val,by omega⟩ ≤
      ∑ i∈Finset.univ.filter (fun i => slot i=j),pieceIntegral i := by
  rw [numerical_slot]
  unfold totalQ96
  simp only [Int.cast_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [piece_is_sum]
  exact Finset.sum_le_sum fun s _ => original_row_floor (physicalRow i s) _ (original_ordinary_Jensen i s)

end
end ImbalancedChen.P2OriginalLaterSixthOwnedIntegral
