import ImbalancedChen.P2OriginalLaterSixthStageMass
import ImbalancedChen.P2OriginalSixthPhysicalGateRows
import ImbalancedChen.P2OriginalSixthCrossCellOwnership
import ImbalancedChen.P4AOriginalLaterSixthHistoryRows

/-! Original earlier-cap comparisons on the later physical simplices.
An earlier action either already lies below the comparison or one of its
own required affine tests excludes it. A weak earlier test may be an
equality on a proper wall, which is deleted explicitly. -/
namespace ImbalancedChen.P4AOriginalLaterSixthPriorGeometry
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive (bank Individual rowVertices vertex sx original_primitive)
open P2OriginalLaterSixthOwnedIntegral (support inner chartGate nonneg_on nonpos_on)
open P2OriginalLaterSixthSourceIntegral (domain owned gate_domain eval_chart)
open P2OriginalLaterSixthRationalGates (raw castPlane cast_original)
open P2OriginalSixthSimplexMoments (Point)
open P2OriginalSixthSimplexBinding (QPoint castPoint)
open P2OriginalSixthPhysicalGateRows (Gate row next physicalCell_iff_rows)
open P2OriginalSixthLogArchive (sourceCell)
open P4AOriginalSixthLaterLiteral (Cell stage)
open P4AOriginalSixthLaterSemantics (Source endpoint)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell newCap)

def embed (c : Cell) : Piece := ⟨c.val,by omega⟩
theorem action_embed (c : Cell) : action (embed c)=c := by fin_cases c <;> rfl
theorem ordinary_embed (c : Cell) : correction (embed c)=false := by fin_cases c <;> rfl

def laterPlanes (c : Cell) := (raw c).map (chartGate (embed c))
theorem source_iff_planes (c : Cell) (t : Point) : Source c t ↔ ∀ p∈laterPlanes c,0<eval p t := by
  have h := gate_domain (embed c) t
  simpa [domain,P2OriginalLaterSixthSourceIntegral.gates,laterPlanes,action_embed,ordinary_embed] using h

theorem eval_next (j : Fin 11) (t : Point) : eval (next (sourceCell j)) t=newCap (sourceCell j) t := by
  change P2OriginalSixthPullingUnion.eval (next (sourceCell j)) t=_
  fin_cases j <;> simp [sourceCell,next,newCap,Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,
    P2OriginalSixthPhysicalGateRows.asc33,P2OriginalSixthPhysicalGateRows.clipped,
    P2OriginalSixthPhysicalGateRows.s5,Certificates.P2OriginalSixthElevenLogSemantics.ascending33,
    Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,Certificates.P2OriginalSixthElevenLogSemantics.S5,
    Certificates.P2OriginalSixthElevenLogSemantics.eta]
  all_goals ring

def proper (a : Plane) : Prop := ∃ t : Point,eval a t≠0
def wall (j : Fin 11) (g : Gate) : Set Point :=
  if proper (row (sourceCell j) g) then {t | eval (row (sourceCell j) g) t=0} else ∅
def regular : Set Point := (⋃ j : Fin 11,⋃ g : Gate,wall j g)ᶜ

theorem regular_ae : ∀ᵐ t : Point ∂volume,t∈regular := by
  rw [ae_iff]
  have hh : volume (⋃ j : Fin 11,⋃ g : Gate,wall j g)=0 := by
    apply measure_iUnion_null
    intro j
    apply measure_iUnion_null
    intro g
    by_cases hp : proper (row (sourceCell j) g)
    · simpa only [wall,if_pos hp] using P2OriginalSixthPullingUnion.affine_zero_volume (row (sourceCell j) g) hp
    · simp [wall,hp]
  simpa only [regular,mem_compl_iff,not_not,setOf_mem_eq] using hh

theorem regular_open : IsOpen regular := by
  apply IsClosed.isOpen_compl
  apply isClosed_iUnion_of_finite
  intro j
  apply isClosed_iUnion_of_finite
  intro g
  by_cases hp : proper (row (sourceCell j) g)
  · simpa only [wall,if_pos hp] using isClosed_eq
      (P2OriginalLaterSixthSourceIntegral.continuous_eval (row (sourceCell j) g)) continuous_const
  · simp [wall,hp]

theorem regular_nonzero {t : Point} (ht : t∈regular) (j : Fin 11) (g : Gate)
    (hp : proper (row (sourceCell j) g)) : eval (row (sourceCell j) g) t≠0 := by
  intro hz
  apply ht
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨g,by simpa [wall,hp] using hz⟩⟩

/-- The coefficient data refer to actual vertices. On the curved tent
the same side is used throughout each individual convex simplex. -/
def BeforeEleven {m : ℕ} (v : Fin m→QPoint) (i : Piece) (j : Fin 11) : Prop :=
  (∀ h : Fin m,evalQ (next (sourceCell j)) (v h)≤evalQ (lower i) (v h)) ∨
  ∃ g : Gate,(∀ h : Fin m,evalQ (row (sourceCell j) g) (v h)≤0) ∧
    (g.strict=true ∨ ∃ h : Fin m,evalQ (row (sourceCell j) g) (v h)<0)
instance {m : ℕ} (v : Fin m→QPoint) (i : Piece) (j : Fin 11) : Decidable (BeforeEleven v i j) := by
  unfold BeforeEleven
  infer_instance

def BeforeLater {m : ℕ} (v : Fin m→QPoint) (i : Piece) (c : Cell) : Prop :=
  (∀ h : Fin m,evalQ (upper (embed c)) (v h)≤evalQ (lower i) (v h)) ∨
  ∃ a∈laterPlanes c,∀ h : Fin m,evalQ a (v h)≤0
instance {m : ℕ} (v : Fin m→QPoint) (i : Piece) (c : Cell) : Decidable (BeforeLater v i c) := by
  unfold BeforeLater
  infer_instance

def allVertices (i : Piece) (k : Fin (bank i).vertices.size) : QPoint := vertex i k
def sourceIndex (i : Piece) (s : Individual i) (k : Fin 7) : Fin (bank i).vertices.size :=
  ⟨(sx i s).ids.getD k.val 0,(original_primitive i s).idsWithin k⟩

def gateList : List Gate :=
  [.rpos,.largest,.oldCutoff,.compactCutoff,.history3,.history5,.oldW,.comparison,.pairAbove,
   .winner,.positiveGap,.selectedAscending,.selectedDescending,.oldArgument,.newArgument] ++
  List.ofFn Gate.order ++ List.ofFn Gate.oldBranch ++ List.ofFn Gate.first3Branch ++
  List.ofFn Gate.fullSquare ++ List.ofFn Gate.remainingSquare ++ List.ofFn Gate.priority

theorem strict_rows (j : Fin 11) {t : Point} (hr : t∈regular) (hc : PhysicalCell (sourceCell j) t) :
    ∀ g∈gateList,0<eval (row (sourceCell j) g) t ∨ ∀ l,row (sourceCell j) g l=0 := by
  intro g _
  by_cases hz : ∀ l,row (sourceCell j) g l=0
  · exact Or.inr hz
  · push_neg at hz
    have hw := regular_nonzero hr j g (P2OriginalSixthCrossCellOwnership.affine_nonzero_of_coefficient hz)
    have h := (physicalCell_iff_rows (sourceCell j) t).mp hc g
    cases hg : g.strict <;> simp only [hg,Bool.false_eq_true,Bool.true_eq_true,if_false,if_true] at h
    · exact Or.inl (lt_of_le_of_ne h (Ne.symm hw))
    · exact Or.inl h

theorem affine_order (i : Piece) (s : Individual i) (a b : Plane) (t : Point)
    (h : ∀ k,evalQ a (rowVertices i s k)≤evalQ b (rowVertices i s k)) (ht : t∈support i s) :
    eval a t≤eval b t := by
  have hd (k) : 0≤evalQ (b-a) (rowVertices i s k) := by
    have he : evalQ (b-a) (rowVertices i s k)=evalQ b (rowVertices i s k)-evalQ a (rowVertices i s k) := by
      simp [evalQ,sub_mul,Finset.sum_sub_distrib] <;> ring
    rw [he]
    exact sub_nonneg.mpr (h k)
  have hv := nonneg_on i s (b-a) hd ht
  rw [P2OriginalLaterSixthCorrections.eval_diff] at hv
  exact sub_nonneg.mp hv

private theorem test_consequence {m : ℕ} (v : Fin m→QPoint) (i : Piece) (j : Fin 11)
    (s : Individual i) (lift : Fin 7→Fin m) (hl : ∀ k,rowVertices i s k=v (lift k))
    {t : Point} (ht : t∈support i s) (hr : t∈regular) (hc : PhysicalCell (sourceCell j) t)
    (he : BeforeEleven v i j) : newCap (sourceCell j) t≤eval (lower i) t := by
  rcases he with he|⟨g,hg,hkind⟩
  · rw [←eval_next]
    exact affine_order i s _ _ t (fun k => by rw [hl k];exact he (lift k)) ht
  · have hneg := nonpos_on i s (row (sourceCell j) g) (fun k => by rw [hl k];exact hg (lift k)) ht
    have hpos := (physicalCell_iff_rows (sourceCell j) t).mp hc g
    rcases hkind with hg'|⟨k,hk⟩
    · rw [hg',if_true] at hpos
      exact False.elim ((not_lt_of_ge hneg) hpos)
    · have hprop : proper (row (sourceCell j) g) := ⟨castPoint (v k),by rw [eval_cast];exact_mod_cast hk.ne⟩
      have hw := regular_nonzero hr j g hprop
      have hweak : 0≤eval (row (sourceCell j) g) t := by
        cases hb : g.strict <;> simp only [hb,if_false,if_true] at hpos
        · exact hpos
        · exact hpos.le
      exact False.elim (hw (le_antisymm hneg hweak))

private theorem eleven_simple (i : Piece) (j : Fin 11) {t : Point} (ht : t∈inner i) (hr : t∈regular)
    (hc : PhysicalCell (sourceCell j) t) (cert : BeforeEleven (allVertices i) i j ∨
      ∀ s : Individual i,BeforeEleven (rowVertices i s) i j) : newCap (sourceCell j) t≤eval (lower i) t := by
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  rcases cert with ha|ha
  · exact test_consequence _ i j s (sourceIndex i s) (fun _=>rfl) hs hr hc ha
  · exact test_consequence _ i j s id (fun _=>rfl) hs hr hc (ha s)

private theorem later_consequence {m : ℕ} (v : Fin m→QPoint) (i : Piece) (c : Cell)
    (s : Individual i) (lift : Fin 7→Fin m) (hl : ∀ k,rowVertices i s k=v (lift k))
    {t : Point} (ht : t∈support i s) (hc : Source c t) (he : BeforeLater v i c) :
    endpoint c t≤eval (lower i) t := by
  rcases he with he|⟨a,ha,hv⟩
  · have hv' := affine_order i s _ _ t (fun k => by rw [hl k];exact he (lift k)) ht
    simpa only [eval_upper,ordinary_embed,action_embed,Bool.false_eq_true,if_false] using hv'
  · have hn := nonpos_on i s a (fun k => by rw [hl k];exact hv (lift k)) ht
    exact False.elim ((not_lt_of_ge hn) ((source_iff_planes c t).mp hc a ha))

private theorem later_simple (i : Piece) (c : Cell) {t : Point} (ht : t∈inner i)
    (hc : Source c t) (cert : BeforeLater (allVertices i) i c ∨
      ∀ s : Individual i,BeforeLater (rowVertices i s) i c) : endpoint c t≤eval (lower i) t := by
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  rcases cert with ha|ha
  · exact later_consequence _ i c s (sourceIndex i s) (fun _=>rfl) hs hc ha
  · exact later_consequence _ i c s id (fun _=>rfl) hs hc (ha s)

/- For an overlap requiring a combination of original rows, the fallback
uses the exact open affine systems on both families. All proper earlier
weak rows are strict off the explicitly deleted null walls. -/
open P2OriginalSixthPhysicalGateRows (constant coord s5 s6 h3 h5 w old clipped asc33 desc33 asc34
  subset selected square remaining)
open P2OriginalLaterSixthSourceIntegral (gates fail33)
open P4AOriginalSixthLaterLiteral (mapped)

local macro "literal_later_rows" h:ident : tactic =>
  `(tactic| (norm_num [gates,laterPlanes,raw,chartGate,charted,action,correction,embed,mapped,fail33,
      eval,Fin.sum_univ_succ,List.mem_cons] at $h <;> repeat' rcases $h with ⟨hAffine,$h⟩))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem previous_eleven (i : Piece) (j : Fin 11) {t : Point} (ht : t∈owned i) (hr : t∈regular)
    (hc : PhysicalCell (sourceCell j) t) : newCap (sourceCell j) t≤eval (lower i) t := by
  fin_cases i <;> fin_cases j <;> first
  | exact eleven_simple _ _ ht.1 hr hc (by decide)
  | have hNow := (gate_domain _ _).mp ht.2
    have hOld := strict_rows _ hr hc
    literal_later_rows hNow
    norm_num [gateList,row,sourceCell,constant,coord,s5,s6,h3,h5,w,old,clipped,asc33,desc33,asc34,
      P2OriginalSixthPhysicalGateRows.r0,subset,selected,square,remaining,Certificates.P2OriginalSixthElevenLogSemantics.bit,
      Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,Certificates.P2OriginalSixthElevenLogSemantics.Cell.descending,
      Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask,Certificates.P2OriginalSixthElevenLogSemantics.Cell.pattern,
      Certificates.P2OriginalSixthElevenLogSemantics.pair12Branches,Certificates.P2OriginalSixthElevenLogSemantics.variableMasks,
      eval,Pi.smul_apply,smul_eq_mul,
      List.ofFn_succ,Fin.forall_fin_succ,Fin.sum_univ_succ] at hOld
    repeat' rcases hOld with ⟨hRow,hOld⟩
    norm_num [newCap,sourceCell,lower,r0,r17,d33,a34,eval,Certificates.P2OriginalSixthElevenLogSemantics.Cell.family,
      Certificates.P2OriginalSixthElevenLogSemantics.ascending33,Certificates.P2OriginalSixthElevenLogSemantics.clippedCap,
      Certificates.P2OriginalSixthElevenLogSemantics.S5,Certificates.P2OriginalSixthElevenLogSemantics.eta,Fin.sum_univ_succ]
    all_goals linarith

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem previous_later (i : Piece) (c : Cell) {t : Point} (ht : t∈owned i)
    (hstage : stage c<stage (action i)) (hc : Source c t) : endpoint c t≤eval (lower i) t := by
  fin_cases i <;> fin_cases c <;> first
  | exact False.elim ((by decide : ¬_) hstage)
  | exact later_simple _ _ ht.1 hc (by decide)
  | have hNow := (gate_domain _ _).mp ht.2
    have hOld := (source_iff_planes _ _).mp hc
    literal_later_rows hNow
    literal_later_rows hOld
    norm_num [endpoint,P4AOriginalSixthLaterLiteral.descending,P4AOriginalSixthLaterLiteral.mask,
      P4AOriginalSixthLaterSemantics.selectedSum,Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit,Certificates.P2OriginalSixthElevenLogSemantics.eta,
      eval,lower,r0,r17,d33,a34,Fin.sum_univ_succ]
    all_goals linarith

end
end ImbalancedChen.P4AOriginalLaterSixthPriorGeometry
