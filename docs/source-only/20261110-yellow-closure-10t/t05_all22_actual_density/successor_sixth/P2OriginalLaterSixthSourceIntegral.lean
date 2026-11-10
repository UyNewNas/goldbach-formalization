import ImbalancedChen.P2OriginalLaterSixthOwnedIntegral
import ImbalancedChen.P2OriginalLaterSixthRationalGates

/-! The numerical simplices enter the strict original sources after
deleting finitely many affine walls. Same-stage actions have unique
source ownership; both G13 comparison corrections keep their own
gates and contribute at the two earlier mask34 comparisons. -/
namespace ImbalancedChen.P2OriginalLaterSixthSourceIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive
open P2OriginalLaterSixthOwnedIntegral (support inner pieceIntegral chartGate nonneg_on nonpos_on id_mem)
open P2OriginalLaterSixthRationalGates (raw castPlane cast_original)
open P2OriginalSixthSimplexBinding (castPoint)
open P2OriginalSixthSimplexMoments (Point)
open P2OriginalSixthPullingUnion (affine_zero_volume)
open Certificates.P2OriginalSixthElevenLogSemantics (descending33)

def fail33 : Plane := ![-57/64,5/2,1,1,2,0,5/2]
def gates (i : Piece) : List Plane :=
  ((raw (action i)).map (chartGate i)) ++ if correction i then [fail33] else []
def domain (i : Piece) : Set Point :=
  {t | P4AOriginalSixthLaterSemantics.Source (action i) t ∧
    (correction i=true → descending33 t<t 0+t 1+t 2+t 5+2*t 3)}
def owned (i : Piece) : Set Point := inner i∩domain i

theorem eval_chart (i : Piece) (r : Plane) (t : Point) :
    eval (chartGate i r) t=P4AOriginalSixthLaterSemantics.eval (castPlane r)
      (P4AOriginalSixthLaterSemantics.coordinates (action i) t) := by
  cases hm : P4AOriginalSixthLaterLiteral.mapped (action i) <;>
    simp [chartGate,charted,hm,eval,P4AOriginalSixthLaterSemantics.eval,castPlane,
      P4AOriginalSixthLaterSemantics.coordinates,Certificates.P2OriginalSixthElevenLogSemantics.chart,
      Certificates.P2OriginalSixthElevenLogSemantics.R0,Certificates.P2OriginalSixthElevenLogSemantics.S5,
      Certificates.P2OriginalSixthElevenLogSemantics.H5,Fin.sum_univ_succ] <;> ring

theorem gate_domain (i : Piece) (t : Point) : t∈domain i ↔ ∀ a∈gates i,0<eval a t := by
  have base : P4AOriginalSixthLaterSemantics.Source (action i) t ↔
      ∀ a∈(raw (action i)).map (chartGate i),0<eval a t := by
    unfold P4AOriginalSixthLaterSemantics.Source
    rw [←cast_original]
    simp only [List.forall_mem_map,eval_chart]
  have hf : 0<eval fail33 t ↔ descending33 t<t 0+t 1+t 2+t 5+2*t 3 := by
    norm_num [eval,fail33,descending33,Fin.sum_univ_succ]; constructor <;> linarith
  cases hc : correction i <;> simp [domain,gates,hc,base,hf]

def SourceCheck (i : Piece) : Prop :=
  ∀ a∈gates i,(∀ v : Fin (bank i).vertices.size,0≤evalQ a (vertex i v)) ∧
               ∃ v : Fin (bank i).vertices.size,0<evalQ a (vertex i v)
instance (i : Piece) : Decidable (SourceCheck i) := by unfold SourceCheck; infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_check (i : Piece) : SourceCheck i := by fin_cases i <;> decide

theorem continuous_eval (a : Plane) : Continuous (eval a) := by unfold eval; fun_prop
theorem domain_open (i : Piece) : IsOpen (domain i) := by
  have h : domain i=⋂ a : {b // b∈(gates i).toFinset},{t | 0<eval a.val t} := by
    ext x
    simp only [gate_domain,mem_iUnion,mem_iInter,mem_setOf_eq]
    simp
  rw [h]
  exact isOpen_iInter_of_finite (fun a => isOpen_lt continuous_const (continuous_eval a.val))

theorem in_inner_nonnegative (i : Piece) (a : Plane) (ha : a∈gates i) {t : Point} (ht : t∈inner i) :
    0≤eval a t := by
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  apply nonneg_on i s a _ hs
  intro k
  exact (source_check i a ha).1 ⟨(sx i s).ids.getD k.val 0,(original_primitive i s).idsWithin k⟩

private theorem nonzero (i : Piece) (a : Plane) (ha : a∈gates i) : ∃ t : Point,eval a t≠0 := by
  obtain ⟨j,hj⟩ := (source_check i a ha).2
  exact ⟨castPoint (vertex i j),by rw [eval_cast];exact_mod_cast hj.ne'⟩

theorem inner_ae_owned (i : Piece) : inner i=ᵐ[volume] owned i := by
  let wall : Set Point := ⋃ a : {b // b∈(gates i).toFinset},{x | eval a.val x=0}
  have hw : volume wall=0 := by
    apply measure_iUnion_null
    intro a
    exact affine_zero_volume a.val (nonzero i a.val (List.mem_toFinset.mp a.property))
  have hae : ∀ᵐ x : Point ∂volume,x∉wall := by rw [ae_iff]; simpa only [not_not] using hw
  filter_upwards [hae] with t ht
  change t∈inner i ↔ t∈inner i∩domain i
  refine ⟨fun hx => ⟨hx,(gate_domain i t).mpr ?_⟩,fun hx => hx.1⟩
  intro a ha
  apply lt_of_le_of_ne (in_inner_nonnegative i a ha hx)
  intro hzero
  exact ht (mem_iUnion.mpr ⟨⟨a,List.mem_toFinset.mpr ha⟩,hzero.symm⟩)

def bankGroup (i : Piece) : ℕ := if correction i then 8 else P4AOriginalSixthLaterLiteral.stage (action i)
def separates (i j : Piece) : Prop :=
  ∃ a∈gates i,∀ v : Fin (bank j).vertices.size,evalQ a (vertex j v)≤0
instance (i j : Piece) : Decidable (separates i j) := by unfold separates; infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_separators (i j : Piece) :
    bankGroup i=bankGroup j → i≠j → separates i j ∨ separates j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem one_way (i j : Piece) (hs : separates i j) : Disjoint (owned i) (owned j) := by
  obtain ⟨a,ha,hv⟩ := hs
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hp := (gate_domain i x).mp hx.2 a ha
  obtain ⟨s,hmem⟩ := mem_iUnion.mp hy.1
  have hn := nonpos_on j s a (fun k => hv ⟨(sx j s).ids.getD k.val 0,(original_primitive j s).idsWithin k⟩) hmem
  exact hp.not_ge hn

theorem same_group_disjoint (i j : Piece) (hg : bankGroup i=bankGroup j) (hne : i≠j) :
    Disjoint (owned i) (owned j) := by
  rcases original_separators i j hg hne with h|h
  · exact one_way i j h
  · exact (one_way j i h).symm

theorem seven_original_source_floors (j : Fin 7) :
    currentUpperEighteenGains ⟨7+j.val,by omega⟩ ≤
      ∑ i∈Finset.univ.filter (fun i => slot i=j),sourceIntegral i (owned i) := by
  apply (P2OriginalLaterSixthOwnedIntegral.original_seven_slot_inner_floor j).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  exact setIntegral_congr_set (inner_ae_owned i)

end
end ImbalancedChen.P2OriginalLaterSixthSourceIntegral
