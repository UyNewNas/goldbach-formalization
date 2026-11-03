import ImbalancedChen.P1QuantizedActionLicense
import ImbalancedChen.P4AOriginalFull87FiniteParentCaps
import ImbalancedChen.P5OriginalFourthFifthSourceInputs

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Uniform half/full/complementary square margins on the ACTUAL original
fourth bank and the ACTUAL fifth gateCheck cells. The fourth budget precedes
e,q,N. The fifth budget is selected after e and the finite archive mesh;
no unjustified uniformity over infinitely many meshes is asserted.
Original admissions remain unchanged. No assertion that all archived wire
rows pass the original tests, or that an old numerical gain is preserved.
-/
namespace ImbalancedChen.P4AOriginalFourthFifthUniformActionLicense
noncomputable section
open scoped Classical BigOperators Topology
open P1QuantizedActionLicense P1GuardFrozenFiniteCapAlgebra
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor
open P4AOriginalCompleteSixthChronology
open P5OriginalFourthFifthSourceInputs
open P4AOriginalFull87HistoryCore (width width_pos)
open VariableEnvelope

private def fourthGate (r : ProducerRow) : Gate 4 → Affine
  | none => halfGate
  | some (false,j) => fullGate j
  | some (true,j) => if j ∈ r.selected then halfGate else selectedGate r.selected j

private theorem fourthGate_eval (r : ProducerRow) (g : Gate 4) (t : Point) :
    (fourthGate r g).eval t = gate r.selected t g := by
  cases g with
  | none => exact halfGate_eval t
  | some x =>
    rcases x with ⟨b,j⟩
    cases b with
    | false => exact fullGate_eval t j
    | true =>
      by_cases hj : j ∈ r.selected
      · simp only [fourthGate, gate, if_pos hj, halfGate_eval]
      · simp only [fourthGate, gate, if_neg hj, selectedGate_eval]

/-- Exact correlated endpoint differences from the original producer.
This is not a sample, midpoint gap or newly postulated Geometry field. -/
def fourthGap (r : ProducerRow) (i : Bool × Gate 4) : ℝ :=
  (((tentPlane r.selected i.1).sub (fourthGate r i.2)).lower r.lower r.upper : ℝ)

theorem fourthGap_pos (r : ProducerRow) (hr : r.Geometry) (i : Bool × Gate 4) :
    0 < fourthGap r i := by
  rcases hr with ⟨_,_,_,_,_,_,_,_,hg,_,_⟩
  rcases i with ⟨side,g⟩
  cases g with
  | none => exact hg.1 side
  | some x =>
    rcases x with ⟨b,j⟩
    cases b with
    | false => exact hg.2.1 side j
    | true =>
      by_cases hj : j ∈ r.selected
      · simpa only [fourthGap, fourthGate, if_pos hj] using hg.1 side
      · simpa only [fourthGap, fourthGate, if_neg hj] using hg.2.2 side j hj

/-- The finite original bank, with a sentinel for an empty admitted set,
provides ONE positive budget for every row, side, gate and point of its
entire original CLOSED rectangle. No gap argument is accepted by callers. -/
theorem exists_original_fourth_budget :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r ∈ originalRows4, originalAdmission4 r →
      ∀ t : Point, t ∈ r.box → ∀ g : Gate 4,
        gate r.selected t g + delta ≤ r.candidate t := by
  obtain ⟨delta,hd,hfloor⟩ := exists_positive_floor
    (originalRows4.product (Finset.univ : Finset (Bool × Gate 4)))
    (fun a => originalAdmission4 a.1) (fun a => fourthGap a.1 a.2)
    (by intro a _ ha; exact fourthGap_pos a.1 (originalAdmission4_geometry a.1 ha) a.2)
  refine ⟨delta,hd,?_⟩
  intro r hr ha t ht g
  have hside (b : Bool) : gate r.selected t g + delta ≤ (tentPlane r.selected b).eval t := by
    have hlow := hfloor (r,(b,g)) (Finset.mem_product.mpr ⟨hr,Finset.mem_univ _⟩) ha
    have hb := ((tentPlane r.selected b).sub (fourthGate r g)).lower_le_eval
      r.lower r.upper t ht.1 ht.2
    rw [Affine.eval_sub, fourthGate_eval] at hb
    change delta ≤ (((tentPlane r.selected b).sub (fourthGate r g)).lower r.lower r.upper : ℝ) at hlow
    linarith
  exact le_min (hside false) (hside true)

/-- The original 2e and the quantizer loss are both paid from the same
proved margin. Nothing here assumes that Geometry licenses arbitrary e. -/
theorem fourth_rounded_of_budget (delta : ℝ) (hd : 0 < delta)
    (r : ProducerRow) (t : Point)
    (hg : ∀ g : Gate 4, gate r.selected t g + delta ≤ r.candidate t)
    (e : ℝ) (he : 0 ≤ e) (heSmall : 8 * e ≤ delta)
    (n : ℕ) (hn : 8 * width n < delta) :
    LowerLicense r.selected t (rounded n (r.bufferedCandidate e t) : ℝ) ∧
      (rounded n (r.bufferedCandidate e t) : ℝ) + width n + 2 * e ≤
        v (∑ i ∈ r.selected, t i) := by
  have hc : r.bufferedCandidate e t ≤ cap := by
    rw [r.bufferedCandidate_eq]
    linarith [v_le_cap (∑ i ∈ r.selected, t i)]
  have hmargin : ∀ g : Gate 4,
      gate r.selected t g + delta / 2 ≤ r.bufferedCandidate e t := by
    intro g
    have h := hg g
    dsimp only [ProducerRow.bufferedCandidate]
    linarith
  obtain ⟨hl,hu⟩ := rounded_licensed n r.selected t (r.bufferedCandidate e t)
    (delta / 2) (by positivity) hc hmargin (by linarith)
  refine ⟨fun g => by have h := hl g; linarith, ?_⟩
  rw [r.bufferedCandidate_eq] at hu
  linarith

/-- The EXACT rational surplus tested by the original gateCheck. -/
def fifthGap (e : ℚ) (m : ℕ) (r : P1OriginalVariableFifthContinuation.FifthRow m) : ℚ :=
  qVLo (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i)
    (∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i) - 2 * e -
    selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell)

theorem fifthGap_pos (e : ℚ) (m : ℕ)
    (r : P1OriginalVariableFifthContinuation.FifthRow m)
    (hc : P1OriginalVariableFifthContinuation.gateCheck e m r = true) :
    0 < fifthGap e m r := by
  have h := of_decide_eq_true hc
  change selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell) + 2 * e <
    qVLo (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i)
      (∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i) at h
  unfold fifthGap
  linarith

/-- A uniform bound on the WHOLE original half-open fifth cell, obtained
from its upper corner. The real point does not supply its own gap. -/
theorem fifth_gap_lower (e : ℚ) (m : ℕ)
    (r : P1OriginalVariableFifthContinuation.FifthRow m) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) (g : Gate 5) :
    gate r.selected t g + (fifthGap e m r : ℝ) ≤
      P1OriginalVariableFifthContinuation.candidate (e : ℝ) r.selected t := by
  let lo := qLogPrimeMeshLo 0 (19 / 96) m r.cell
  let hi := qLogPrimeMeshHi 0 (19 / 96) m r.cell
  have hl (i : Fin 5) : (lo i : ℝ) ≤ t i := by
    dsimp only [lo]
    rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hu (i : Fin 5) : t i ≤ (hi i : ℝ) := by
    dsimp only [hi]
    rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le
  have hgate : gate r.selected t g ≤ (selectedCapLower r.selected 0 hi : ℝ) := by
    cases g with
    | none => exact_mod_cast selectedCapLower_half_le r.selected 0 hi
    | some x =>
      rcases x with ⟨b,j⟩
      cases b with
      | false =>
        have hm := prefixSquareExpr_mono hu j
        have hb : ((prefixSquareExpr hi j : ℚ) : ℝ) ≤ selectedCapLower r.selected 0 hi := by
          exact_mod_cast selectedCapLower_prefix_le r.selected 0 hi j
        rw [cast_prefixSquareExpr] at hb
        exact hm.trans hb
      | true =>
        by_cases hj : j ∈ r.selected
        · simp only [gate, if_pos hj]
          exact_mod_cast selectedCapLower_half_le r.selected 0 hi
        · simp only [gate, if_neg hj]
          have hm := selectedSquareExpr_mono r.selected hu j
          have hb : ((selectedSquareExpr r.selected hi j : ℚ) : ℝ) ≤
              selectedCapLower r.selected 0 hi := by
            exact_mod_cast selectedCapLower_selected_le r.selected 0 hi j hj
          rw [cast_selectedSquareExpr] at hb
          exact hm.trans hb
  have hv : (qVLo (∑ i ∈ r.selected, lo i) (∑ i ∈ r.selected, hi i) : ℝ) ≤
      v (∑ i ∈ r.selected, t i) := by
    apply qVLo_le_v
    · push_cast; exact Finset.sum_le_sum (fun i _ => hl i)
    · push_cast; exact Finset.sum_le_sum (fun i _ => hu i)
  rw [P1OriginalVariableFifthContinuation.candidate,
    P1OriginalVariableFifthContinuation.envelope_eq_v]
  dsimp only [fifthGap]
  push_cast
  dsimp only [lo,hi] at hgate hv
  linarith

/-- Resolution is chosen after the original finite e/m bank, but before
omega-dependent eligibility queries, N and points. All original gateCheck
rows in that bank are covered, even before the later eligibility filters. -/
theorem exists_fifth_resolution (d : OriginalData) (he : 0 ≤ d.e) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ r ∈ d.rows5,
      P1OriginalVariableFifthContinuation.gateCheck d.e d.m r = true →
      ∀ t : Fin 5 → ℝ, t ∈ logPrimeMeshCell 0 (19 / 96) d.m r.cell →
        LowerLicense r.selected t
          (rounded n (P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t) : ℝ) ∧
        (rounded n (P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t) : ℝ)
          + width n + 2 * (d.e : ℝ) ≤ v (∑ i ∈ r.selected, t i) := by
  obtain ⟨delta,hd,hfloor⟩ := exists_positive_floor d.rows5
    (fun r => P1OriginalVariableFifthContinuation.gateCheck d.e d.m r = true)
    (fun r => (fifthGap d.e d.m r : ℝ))
    (by intro r _ hc; exact_mod_cast fifthGap_pos d.e d.m r hc)
  obtain ⟨n0,hn0⟩ := exists_resolution delta hd
  refine ⟨n0,?_⟩
  intro n hn r hr hc t ht
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have hu := P1OriginalVariableFifthContinuation.candidate_le_global_cap
    (d.e : ℝ) heR r.selected t
  have hm : ∀ g : Gate 5, gate r.selected t g + delta ≤
      P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t := by
    intro g
    have hh := fifth_gap_lower d.e d.m r t ht g
    have hδ := hfloor r hr hc
    linarith
  obtain ⟨hl,hu'⟩ := rounded_licensed n r.selected t _ delta hd hu hm
    (by have h := hn0 n hn; have hw := width_pos n; linarith)
  refine ⟨fun g => by have h := hl g; linarith, ?_⟩
  rw [P1OriginalVariableFifthContinuation.candidate,
    P1OriginalVariableFifthContinuation.envelope_eq_v] at hu'
  linarith

/-- Output property on the SAME original4/5 data. It is a conclusion of
the concrete schedule theorem, not an additional user-supplied licence. -/
def ArchiveLicenses (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  let d := data e q om
  (∀ r ∈ d.rows4, d.licensed4 r → ∀ t : Point, t ∈ r.box →
    LowerLicense r.selected t (rounded n (r.bufferedCandidate (d.e : ℝ) t) : ℝ) ∧
    (rounded n (r.bufferedCandidate (d.e : ℝ) t) : ℝ) + width n + 2 * (d.e : ℝ) ≤
      v (∑ i ∈ r.selected, t i)) ∧
  (∀ r ∈ d.rows5, ∀ t : Fin 5 → ℝ,
    P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega d.J5 r t →
    LowerLicense r.selected t
      (rounded n (P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t) : ℝ) ∧
    (rounded n (P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t) : ℝ)
      + width n + 2 * (d.e : ℝ) ≤ v (∑ i ∈ r.selected, t i))

/-- Genuine original archive supplier, no assumed margin, Geometry or
cap license. e0 precedes q; n0 follows the finite archive choice e,q,omega.
The old all-q cofinal membership theorem can therefore be reused by taking
a larger n AFTER q is fixed. No uniform n0 over infinitely many q is claimed. -/
theorem exists_original_archive_action_precision :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ q : ℕ, ∀ om : ℝ, ∃ n0 : ℕ, ∀ n ≥ n0, ArchiveLicenses n e q om := by
  obtain ⟨delta,hd,hfourth⟩ := exists_original_fourth_budget
  obtain ⟨n4,hn4⟩ := exists_resolution delta hd
  refine ⟨delta / 8,by positivity,?_⟩
  intro e he hee q om
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he.le
  obtain ⟨n5,hn5⟩ := exists_fifth_resolution (data e q om) he.le
  refine ⟨max n4 n5,?_⟩
  intro n hn
  constructor
  · intro r hr ha t ht
    have hr' : r ∈ originalRows4 := hr
    have ha' : originalAdmission4 r := ha
    exact fourth_rounded_of_budget delta hd r t (hfourth r hr' ha' t ht)
      (e : ℝ) heR (by linarith) n (hn4 n ((le_max_left _ _).trans hn))
  · intro r hr t ht
    exact hn5 n ((le_max_right _ _).trans hn) r hr ht.2.1 t ht.2.2

end
end ImbalancedChen.P4AOriginalFourthFifthUniformActionLicense
