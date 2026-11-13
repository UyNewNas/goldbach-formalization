import ImbalancedChen.P4BOriginalHigherLowEndpointBounds
import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P1QuantizedActionLicense
import ImbalancedChen.P4AOriginalFull87FiniteEighthPolicy

/-! Source margins on the native masks. Fourth rows are certified on
their *closed* boxes, and their rational endpoint gaps form one finite
bank before the coarse resolution, the target and the physical policy. -/
namespace ImbalancedChen.P4BOriginalHigherActionMargins
noncomputable section
open scoped BigOperators
open Classical VariableEnvelope
open P1QuantizedActionLicense (Gate gate LowerLicense lowerLicense_iff exists_positive_floor)
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4 originalAdmission4_geometry)
open P1OriginalVariableFifthContinuation (FifthRow gateCheck_sound)
open P4AOriginalOrderedThirdFullPolicy (Root accepted)
open P4AOriginalSixthActionBank (Action)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SourceDictionary (Cell Source)
open P4AOriginalFull87FiniteEighthCap (finiteCap downCap_error)
open P4AOriginalFull87StrictActionTrim (trim mem_trim trim_subset_source actionSlack)

private def form (I : Finset (Fin 4)) : Gate 4 → Affine
  | none => halfGate
  | some (false,j) => fullGate j
  | some (true,j) => if j∈I then halfGate else selectedGate I j

private theorem form_eval (I : Finset (Fin 4)) (g : Gate 4) (t : Fin 4→ℝ) :
    (form I g).eval t=gate I t g := by
  cases g with
  | none => exact halfGate_eval t
  | some u =>
    rcases u with ⟨b,j⟩
    cases b with
    | false => exact fullGate_eval t j
    | true => by_cases hj : j∈I <;> simp only [form,gate,hj,if_true,if_false,halfGate_eval,selectedGate_eval]

private def edge (r : ProducerRow) (s : Bool) (g : Gate 4) : ℝ :=
  (((tentPlane r.selected s).sub (form r.selected g)).lower r.lower r.upper:ℝ)

private theorem edge_pos {r : ProducerRow} (ha : originalAdmission4 r) (s : Bool) (g : Gate 4) :
    0<edge r s g := by
  obtain ⟨_,_,_,_,_,_,_,_,h,_,_⟩ := originalAdmission4_geometry r ha
  cases g with
  | none => exact h.1 s
  | some u =>
    rcases u with ⟨b,j⟩
    cases b with
    | false => exact h.2.1 s j
    | true =>
      by_cases hj : j∈r.selected
      · simpa only [edge,form,if_pos hj] using h.1 s
      · simpa only [edge,form,if_neg hj] using h.2.2 s j hj

private def gapBank := originalRows4.product (Finset.univ : Finset (Bool × Gate 4))

theorem fourth_floor :
    ∃ gap : ℝ,0<gap ∧ ∀r∈originalRows4,originalAdmission4 r →
      ∀ t∈r.box,∀ g : Gate 4,gap+gate r.selected t g≤v (∑i∈r.selected,t i) := by
  obtain ⟨gap,hg,H⟩ := exists_positive_floor gapBank (fun p => originalAdmission4 p.1)
    (fun p => edge p.1 p.2.1 p.2.2) (fun _ _ ha => edge_pos ha _ _)
  refine ⟨gap,hg,?_⟩
  intro r hr ha t ht g
  have side (s : Bool) : gap+gate r.selected t g≤(tentPlane r.selected s).eval t := by
    have hmin := H (r,s,g) (Finset.mem_product.mpr ⟨hr,Finset.mem_univ _⟩) ha
    have hval := ((tentPlane r.selected s).sub (form r.selected g)).lower_le_eval
      r.lower r.upper t ht.1 ht.2
    rw [Affine.eval_sub,form_eval] at hval
    exact (le_sub_iff_add_le.mp (hmin.trans hval))
  rw [←newCap_eq_v]; exact le_min (side false) (side true)

def fourthGap : ℝ := fourth_floor.choose
theorem fourthGap_pos : 0<fourthGap := fourth_floor.choose_spec.1

/-- The chosen pre-target gap is smaller than each distinct original
payment: the fourth finite edge, the fifth buffered cap, a sixth step,
and the eighth trim. -/
def reserve (e : ℚ) (r n : ℕ) : ℝ :=
  min (min fourthGap (e:ℝ)) (min (width n) (width r))

theorem reserve_bounds {e : ℚ} (he : 0<e) (r n : ℕ) :
    0<reserve e r n ∧ reserve e r n≤fourthGap ∧ reserve e r n≤(e:ℝ) ∧
      reserve e r n≤width n ∧ reserve e r n≤width r := by
  unfold reserve
  exact ⟨lt_min (lt_min fourthGap_pos (by exact_mod_cast he)) (lt_min (width_pos n) (width_pos r)),
    (min_le_left _ _).trans (min_le_left _ _),(min_le_left _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

theorem fourth {e : ℚ} (he : 0<e) (qr n : ℕ) {r : ProducerRow} (hr : r∈originalRows4)
    (ha : originalAdmission4 r) {t : Fin 4→ℝ} (ht : t∈r.box) :
    (r.bufferedCandidate (e:ℝ) t)+reserve e qr n≤v (∑i∈r.selected,t i) ∧
      ∀j∉r.selected,selectedSquareExpr r.selected t j+reserve e qr n≤v (∑i∈r.selected,t i) := by
  obtain ⟨_,h4,he',_,_⟩ := reserve_bounds he qr n
  refine ⟨by rw [r.bufferedCandidate_eq]; linarith only [he',(by exact_mod_cast he : 0<(e:ℝ))],?_⟩
  intro j hj
  have H := fourth_floor.choose_spec.2 r hr ha t ht (some (true,j))
  simp only [gate,if_neg hj] at H
  linarith only [H,h4]

theorem fifth {e : ℚ} (he : 0<e) (qr n q : ℕ) (a : ℝ)
    (r : FifthRow (P4AOriginalNewFifthUnion.data e q a).m) (t : Fin 5→ℝ)
    (hh : P1OriginalVariableFifthContinuation.eligible e ((e:ℝ)/20)
      (P4AOriginalNewFifthUnion.data e q a).m a (P4AOriginalNewFifthUnion.data e q a).J5 r t) :
    let M := P1OriginalVariableFifthContinuation.candidate (e:ℝ) r.selected t
    M+reserve e qr n≤v (∑i∈r.selected,t i) ∧
      ∀j∉r.selected,selectedSquareExpr r.selected t j+reserve e qr n≤v (∑i∈r.selected,t i) := by
  have hg := gateCheck_sound e _ r t hh.2.1 hh.2.2
  have he' := (reserve_bounds he qr n).2.2.1
  have eq : P1OriginalVariableFifthContinuation.candidate (e:ℝ) r.selected t=
      v (∑i∈r.selected,t i)-2*(e:ℝ) := by
    rw [P1OriginalVariableFifthContinuation.candidate,P1OriginalVariableFifthContinuation.envelope_eq_v]
  have hm : P1OriginalVariableFifthContinuation.candidate (e:ℝ) r.selected t+reserve e qr n≤v (∑i∈r.selected,t i) := by
    linarith only [eq,he',(by exact_mod_cast he : 0<(e:ℝ))]
  exact ⟨hm,fun j hj => ((add_lt_add_right (hg.2.2 j hj) _).le).trans hm⟩

theorem sixth {e : ℚ} (he : 0<e) (qr n q : ℕ) (a N : ℝ) (R : Root) (h : List ℕ)
    (act : Action) (hh : accepted R (P4AOriginalNewFifthUnion.data e q a) N n h act) :
    let t := primeHistoryLogCoordinates N 6 h
    let I := P4AOriginalSixthActionBank.selected act
    let M := (P1GuardFrozenFiniteCapAlgebra.rounded n (P4AOriginalSixthActionBank.endpoint act t):ℝ)
    M+reserve e qr n≤v (∑i∈I,t i) ∧
      ∀j∉I,selectedSquareExpr I t j+reserve e qr n≤v (∑i∈I,t i) := by
  let t := primeHistoryLogCoordinates N 6 h
  let I := P4AOriginalSixthActionBank.selected act
  let M := (P1GuardFrozenFiniteCapAlgebra.rounded n (P4AOriginalSixthActionBank.endpoint act t):ℝ)
  have hM : M+width n≤v (∑i∈I,t i) := hh.2.2
  have ha : M+reserve e qr n≤v (∑i∈I,t i) := (add_le_add_left (reserve_bounds he qr n).2.2.2.1 M).trans hM
  have H := (lowerLicense_iff I t M).mp hh.2.1
  exact ⟨ha,fun j hj => ((add_lt_add_right (H.2.2 j hj) _).le).trans ha⟩

theorem eighth {e : ℚ} (he : 0<e) (qr n : ℕ) {c : Cell} {t : Fin 8→ℝ} (ht : t∈trim c (width qr)) :
    let I := P4AOriginalFull87SourceDictionary.selected c
    (finiteCap n c t:ℝ)+reserve e qr n≤v (∑i∈I,t i) ∧
      ∀j∉I,selectedSquareExpr I t j+reserve e qr n≤v (∑i∈I,t i) := by
  have hs := trim_subset_source c (width_pos qr) ht
  have htend := (P4AOriginalFull87SourceDictionary.source_selected_license hs).le
  have hr := reserve_bounds he qr n
  have hcap := (downCap_error n (P4AOriginalFull87SourceDictionary.newCap c t)).2
  dsimp only
  constructor
  · change (P4AOriginalFull87FiniteEighthCap.downCap n _:ℝ)+_≤_
    linarith only [hcap,hr.2.2.2.1,htend]
  · intro j hj
    have hh := ((mem_trim c (width qr) t).mp ht).2.2 (.complement j)
    simp only [actionSlack,if_neg hj] at hh
    linarith only [hh,hr.2.2.2.2,htend]

end
end ImbalancedChen.P4BOriginalHigherActionMargins
