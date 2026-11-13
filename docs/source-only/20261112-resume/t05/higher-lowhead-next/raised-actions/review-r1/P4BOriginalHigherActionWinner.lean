import ImbalancedChen.P4BOriginalHigherActionReads

/-! Exact finite winners on the compiled representative. The choice used
below is made on the labelled word and the retained physical policy;
it does not depend on the HB integer, a modulus owner or a frequency. -/
namespace ImbalancedChen.P4BOriginalHigherActionWinner
noncomputable section
open scoped BigOperators
open Classical VariableEnvelope
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowRepresentative (g d t level lastLevel atThird owner_data uncovered_raises)
open P4BOriginalHigherActionReads (raw anc point root five six eight stage reachedFive reachedSix)
open P2OriginalFourthCapProducerInterface (ProducerRow)
open P1OriginalVariableFourthContinuation (producerEligible)
open P1OriginalVariableFifthContinuation (FifthRow)
open P1GuardFrozenFiniteCapAlgebra (finiteMax_attained rounded protect clamp clamp_bounds clamp_eq rounded_error)
open P4AOriginalOrderedThirdFullPolicy (fourth fifth cap5 cap6 accepted)
open P4AOriginalSixthActionBank (Action allActions endpoint)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87HistoryCore (width)
open P4BOriginalHigherActionMargins (reserve reserve_bounds)

inductive SourceAction (P : Params) where
  | four (r : ProducerRow)
  | five (r : FifthRow (d P).m)
  | six (a : Action)
  | eight (c : Cell)

namespace SourceAction
variable {P : Params}

def arity : SourceAction P→ℕ
  | .four _ => 4 | .five _ => 5 | .six _ => 6 | .eight _ => 8

def mask : (a : SourceAction P)→Finset (Fin a.arity)
  | .four r => r.selected | .five r => r.selected
  | .six a => P4AOriginalSixthActionBank.selected a
  | .eight c => P4AOriginalFull87SourceDictionary.selected c

def value (J : List ℕ) : SourceAction P→ℝ
  | .four r => (rounded P.n (r.bufferedCandidate (P.e:ℝ) (point P J 4)):ℝ)
  | .five r => (rounded P.n (P1OriginalVariableFifthContinuation.candidate (P.e:ℝ) r.selected (point P J 5)):ℝ)
  | .six a => (rounded P.n (endpoint a (point P J 6)):ℝ)
  | .eight c => (finiteCap P.n c (point P J 8):ℝ)

def admitted (J : List ℕ) : SourceAction P→Prop
  | .four r => r∈(d P).rows4 ∧ producerEligible (d P).licensed4 r (point P J 4)
  | .five r => r∈(d P).rows5 ∧ P1OriginalVariableFifthContinuation.eligible (d P).e (d P).chi
      (d P).m (d P).omega (d P).J5 r (point P J 5)
  | .six a => a∈allActions ∧ accepted (root P J) (d P) (P.N:ℝ) P.n (anc P J 6) a
  | .eight c => P4AOriginalFull87SourceDispatch.ownerAtPrefix (P.N:ℝ) (raw P J)=some c ∧
      point P J 8∈P4AOriginalFull87StrictActionTrim.trim c (width P.r)

/-- A numerical tie may use only an attained row on the evaluated path.
The inherited fifth passes through the raw fourth maximum. An eighth
miss reaches the complete sixth maximum; a hit names its actual owner. -/
def traced (J : List ℕ) : SourceAction P→Prop
  | .four r => reachedFive P J ∧
      fifth (root P J) (d P) (P.N:ℝ) (anc P J 5)=fourth (root P J) (d P) (P.N:ℝ) (anc P J 4) ∧
      fourth (root P J) (d P) (P.N:ℝ) (anc P J 4)=r.bufferedCandidate (P.e:ℝ) (point P J 4)
  | .five r => reachedFive P J ∧ fifth (root P J) (d P) (P.N:ℝ) (anc P J 5)=
      P1OriginalVariableFifthContinuation.candidate (P.e:ℝ) r.selected (point P J 5)
  | .six a => reachedSix P J ∧ P4BOriginalHigherActionReads.six P J=(rounded P.n (endpoint a (point P J 6)):ℝ)
  | .eight c => stage P J=.eighth ∧ P4BOriginalHigherActionReads.eight P J=some (finiteCap P.n c (point P J 8))
end SourceAction

theorem rounded_le_when_pos (n : ℕ) (x : ℝ) (h : 0<(rounded n x:ℝ)) : (rounded n x:ℝ)≤x := by
  have hc := clamp_bounds x
  have ee := (rounded_error n (clamp x) hc.1 hc.2).2.2
  have id : rounded n (clamp x)=rounded n x := by unfold rounded; rw [clamp_eq hc.1 hc.2]
  rw [id] at ee
  have pos := h.trans_le ee
  have hx : 0≤x := by
    by_contra! hn
    have hz : clamp x=0 := max_eq_left ((min_le_right cap x).trans hn.le)
    rw [hz] at pos; exact (lt_irrefl _ pos)
  exact ee.trans (max_le hx (min_le_right cap x))

private abbrev Found (P : Params) (J : List ℕ) (V : ℝ) :=
  ∃ b : SourceAction P,b.arity≤(raw P J).length ∧ (b.admitted J ∧ b.traced J) ∧ V=b.value J

private theorem five_found (P : Params) {J : List ℕ} (hk : 5≤(raw P J).length)
    (hlow : P5OriginalCommonFourthSourceNavigation.firstCoordinate (P.N:ℝ) (raw P J)≤mu)
    (hR : 0≤(root P J).scalar) (arm : reachedFive P J) (hr : (root P J).scalar<five P J) : Found P J (five P J) := by
  let R := root P J
  let d' := d P
  let L4 := fourth R d' (P.N:ℝ) (anc P J 4)
  let L5 := fifth R d' (P.N:ℝ) (anc P J 5)
  have eP : five P J=max R.scalar (rounded P.n L5:ℝ) := P4AOriginalEarlyFiniteStages.cap5_as_protect _ _ _ _ _
  have val : five P J=(rounded P.n L5:ℝ) := by
    rw [eP] at hr ⊢
    exact max_eq_right ((lt_max_iff.mp hr).resolve_left (lt_irrefl _)).le
  have hraw : R.scalar<L5 := by
    rw [val] at hr; exact hr.trans_le (rounded_le_when_pos P.n L5 (hR.trans_lt hr))
  have len5 : (anc P J 5).length=5 := by simp [anc,rosserAncestor_length,min_eq_left hk]
  have len4 : (anc P J 4).length=4 := by simp [anc,rosserAncestor_length,min_eq_left (show 4≤(raw P J).length by omega)]
  have e5 : L5=P1OriginalVariableFourthContinuation.finiteMax d'.rows5
      (fun r => P1OriginalVariableFifthContinuation.eligible d'.e d'.chi d'.m d'.omega d'.J5 r (point P J 5))
      (fun r => P1OriginalVariableFifthContinuation.candidate (d'.e:ℝ) r.selected (point P J 5)) L4 := by
    simp only [L5,fifth,if_pos len5,anc,rosserAncestor_nested 4 5 (by decide),L4]
  rcases finiteMax_attained d'.rows5
      (fun r => P1OriginalVariableFifthContinuation.eligible d'.e d'.chi d'.m d'.omega d'.J5 r (point P J 5))
      (fun r => P1OriginalVariableFifthContinuation.candidate (d'.e:ℝ) r.selected (point P J 5)) L4
      with h|⟨r,hm,ha,h⟩
  · have h54 := e5.trans h
    have e4 : L4=P1OriginalVariableFourthContinuation.finiteMax d'.rows4
        (fun r => producerEligible d'.licensed4 r (point P J 4))
        (fun r => r.bufferedCandidate (d'.e:ℝ) (point P J 4)) R.scalar := by
      rw [show L4=fourth R d' (P.N:ℝ) (anc P J 4) from rfl,fourth,if_pos len4,
        P4BOriginalHigherActionReads.third_four P (by omega) hlow]
    rcases finiteMax_attained d'.rows4 (fun r => producerEligible d'.licensed4 r (point P J 4))
        (fun r => r.bufferedCandidate (d'.e:ℝ) (point P J 4)) R.scalar with h'|⟨r,hm,ha,h'⟩
    · exact ((ne_of_gt hraw) (h54.trans (e4.trans h'))).elim
    · exact ⟨.four r,by change 4≤_; omega,⟨⟨hm,ha⟩,arm,h54,e4.trans h'⟩,val.trans
        (congrArg (fun x => (rounded P.n x:ℝ)) (h54.trans (e4.trans h')))⟩
  · exact ⟨.five r,hk,⟨⟨hm,ha⟩,arm,e5.trans h⟩,val.trans (congrArg (fun x => (rounded P.n x:ℝ)) (e5.trans h))⟩

private theorem six_found (P : Params) {J : List ℕ} (hk : 6≤(raw P J).length)
    (hlow : P5OriginalCommonFourthSourceNavigation.firstCoordinate (P.N:ℝ) (raw P J)≤mu)
    (hR : 0≤(root P J).scalar) (arm : reachedSix P J) (hr : (root P J).scalar<six P J) : Found P J (six P J) := by
  have eq : six P J=P1OriginalVariableFourthContinuation.finiteMax allActions
      (accepted (root P J) (d P) (P.N:ℝ) P.n (anc P J 6))
      (fun a => (rounded P.n (endpoint a (point P J 6)):ℝ)) (five P J) := by
    simp only [six,cap6,anc,rosserAncestor_nested 5 6 (by decide),five]
  rcases finiteMax_attained allActions (accepted (root P J) (d P) (P.N:ℝ) P.n (anc P J 6))
      (fun a => (rounded P.n (endpoint a (point P J 6)):ℝ)) (five P J) with h|⟨a,ha,he,h⟩
  · have hh := eq.trans h
    rw [hh] at hr ⊢; exact five_found P (by omega) hlow hR (Or.inr ⟨arm,hh⟩) hr
  · exact ⟨.six a,hk,⟨⟨ha,he⟩,arm,eq.trans h⟩,eq.trans h⟩

/-- Every remaining low word names an actual selected original action
whose finite value equals the whole retained odd-history exponent. -/
theorem original (P : Params) {J : List ℕ} (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (hstep : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0≤P.omega)
    (hJ : J∈P.words) (h4 : 4≤J.length) (hlo : t P J 0≤mu) (hn : ¬atThird P J) :
    ∃ b : SourceAction P,b.arity≤(raw P J).length ∧ (b.admitted J ∧ b.traced J) ∧ lastLevel P J=b.value J := by
  obtain ⟨_,hroot,hl⟩ := P4BOriginalHigherActionReads.root_at P hN he.le ho hJ hlo
  have raised := uncovered_raises P hN ho hJ hn
  have height : (1/2:ℝ)≤level P J := P4BOriginalHigherLowRootRows.half_le (by exact_mod_cast he) hes hstep
    (owner_data P hN he.le ho hJ).2.2 hlo
  have hR : 0≤(root P J).scalar := by rw [hroot]; linarith only [height]
  have H : (root P J).scalar<lastLevel P J := by rw [hroot]; exact raised
  have h5 : 5≤J.length := by
    by_contra! h
    have hh := P4BOriginalHigherLowRepresentative.four P hN he.le ho hJ (by omega) hlo
    exact (ne_of_gt raised) hh
  rcases P4BOriginalHigherActionReads.last P hN he.le ho hJ h5 hlo with ⟨st,h⟩|⟨hs,arm,h⟩|⟨a,h8,st,ha,h⟩
  · rw [h] at H ⊢; exact five_found P (P4BOriginalHigherActionReads.arity P hN hJ h5) hl hR (Or.inl st) H
  · rw [h] at H ⊢; exact six_found P hs hl hR arm H
  · obtain ⟨c,hc,ht,hv⟩ := P4AOriginalFull87FiniteEighthPolicy.selectedCap_some_spec _ _ _ _ a ha
    exact ⟨.eight c,h8,⟨⟨hc,ht⟩,st,ha.trans (congrArg some hv)⟩,h.trans (congrArg (fun y : ℚ => (y:ℝ)) hv)⟩

theorem native_margin (P : Params) {J : List ℕ} (he : 0<P.e) (b : SourceAction P)
    (hb : b.admitted J) (hv : 0<b.value J) :
    let t' := point P J b.arity
    let s := ∑ i∈b.mask,t' i
    b.value J+reserve P.e P.r P.n≤v s ∧
      ∀ j∉b.mask,selectedSquareExpr b.mask t' j+reserve P.e P.r P.n≤v s := by
  cases b with
  | four r =>
    have H := P4BOriginalHigherActionMargins.fourth he P.r P.n hb.1 hb.2.1 hb.2.2
    exact ⟨(add_le_add_right (rounded_le_when_pos _ _ hv) _).trans H.1,H.2⟩
  | five r =>
    have H := P4BOriginalHigherActionMargins.fifth he P.r P.n P.q P.a r (point P J 5) hb.2
    exact ⟨(add_le_add_right (rounded_le_when_pos _ _ hv) _).trans H.1,H.2⟩
  | six a => exact P4BOriginalHigherActionMargins.sixth he P.r P.n P.q P.a (P.N:ℝ) (root P J) (anc P J 6) a hb.2
  | eight c => exact P4BOriginalHigherActionMargins.eighth he P.r P.n hb.2

end
end ImbalancedChen.P4BOriginalHigherActionWinner
