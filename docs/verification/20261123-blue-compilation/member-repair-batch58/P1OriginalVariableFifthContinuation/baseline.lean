import ImbalancedChen.P1OriginalVariableFourthContinuation
import ImbalancedChen.P1OriginalCoarseFifthContinuationCells
import ImbalancedChen.SelectedPrefixBoxCap

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The fifth continuation of the *variable* original-fourth profile.  Every
eligible fifth row contributes the literal pointwise manuscript envelope
`min ((1+s_I)/2) (57/64-3*s_I/2) - 2e`; overlapping rows are all maximized.
The inherited seed is the actual fourth producer profile on the same fourth
ancestor.  Fifth row selection is fixed before N and retains the original
third coarse/rough gate.  `gateCheck` is a finite rational whole-box test
for the full and selected square gates of the variable candidate.  It does
not assert that any historical numerical row has passed.

No gain, integral, density, or fifth numerical certificate is postulated.
The fourth and fifth policies keep the same original initial policy, raw Q3,
rank-four first-stop frontier, and target-deleted rough carrier.
-/

namespace ImbalancedChen.P1OriginalVariableFifthContinuation

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open HistoricalThirdCoarse
open P1OriginalVariableFourthContinuation
open P1OriginalCoarseFifthContinuation
open P2OriginalFourthCapProducerInterface

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

structure FifthRow (m : ℕ) where
  cell : Label5 m
  selected : Finset (Fin 5)

def envelope (I : Finset (Fin 5)) (t : Point5) : ℝ :=
  let s := ∑ i ∈ I, t i
  min ((1 + s) / 2) (57 / 64 - (3 / 2) * s)

def candidate (e : ℝ) (I : Finset (Fin 5)) (t : Point5) : ℝ :=
  envelope I t - 2 * e

theorem envelope_eq_v (I : Finset (Fin 5)) (t : Point5) :
    envelope I t = v (∑ i ∈ I, t i) := by
  rw [envelope, v_eq_min]
  rfl

theorem candidate_eq_original_cap (e : ℝ) (I : Finset (Fin 5)) (t : Point5) :
    candidate e I t =
      min ((1 + ∑ i ∈ I, t i) / 2)
        (57 / 64 - (3 / 2 : ℝ) * ∑ i ∈ I, t i) - 2 * e := rfl

theorem candidate_le_original_cap (e : ℝ) (he : 0 ≤ e)
    (I : Finset (Fin 5)) (t : Point5) : candidate e I t ≤ envelope I t := by
  dsimp [candidate]
  linarith

theorem candidate_le_global_cap (e : ℝ) (he : 0 ≤ e)
    (I : Finset (Fin 5)) (t : Point5) :
    candidate e I t ≤ VariableEnvelope.cap := by
  calc
    candidate e I t ≤ envelope I t := candidate_le_original_cap e he I t
    _ = v (∑ i ∈ I, t i) := envelope_eq_v I t
    _ ≤ VariableEnvelope.cap := v_le_cap _

/-- A strict rational endpoint test for the pointwise cap after buffer loss.
It proves all square gates directly, without replacing M_I(t) by a midpoint. -/
def gateCheck (e : ℚ) (m : ℕ) (r : FifthRow m) : Bool :=
  decide (selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell) +
    2 * e < qVLo
      (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i)
      (∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i))

/-- Eligibility retains the original selected third ancestor and the
whole-cell rough cutoff; the remaining condition is exact cell membership. -/
def eligible (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (r : FifthRow m) (t : Point5) : Prop :=
  r.cell ∈ selectedFifthCells e chi m omega J5 ∧
    gateCheck e m r = true ∧
      t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell

theorem eligible_original_third_gate (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (r : FifthRow m) (t : Point5)
    (h : eligible e chi m omega J5 r t) :
    historicalPrefixProject (by omega : 3 ≤ 5) r.cell ∈
        HistoricalThirdCoarse.cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 5) r.cell) 2 : ℝ) := by
  exact ((mem_selectedFifthCells e chi m omega J5 r.cell).mp h.1).2

theorem gateCheck_sound (e : ℚ) (m : ℕ) (r : FifthRow m) (t : Point5)
    (hc : gateCheck e m r = true)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    (1 / 2 : ℝ) < candidate (e : ℝ) r.selected t ∧
      (∀ k, prefixSquareExpr t k < candidate (e : ℝ) r.selected t) ∧
      (∀ k ∉ r.selected,
        selectedSquareExpr r.selected t k < candidate (e : ℝ) r.selected t) := by
  have hlo (i : Fin 5) :
      (qLogPrimeMeshLo 0 (19 / 96) m r.cell i : ℝ) ≤ t i := by
    rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hhi (i : Fin 5) :
      t i ≤ (qLogPrimeMeshHi 0 (19 / 96) m r.cell i : ℝ) := by
    rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m r.cell) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le
  have hslo :
      ((∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i : ℚ) : ℝ) ≤
        ∑ i ∈ r.selected, t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hlo i)
  have hshi :
      (∑ i ∈ r.selected, t i) ≤
        ((∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hhi i)
  have hv := qVLo_le_v hslo hshi
  have hcheck :
      (selectedCapLower r.selected 0
          (qLogPrimeMeshHi 0 (19 / 96) m r.cell) : ℝ) + 2 * (e : ℝ) <
        v (∑ i ∈ r.selected, t i) := by
    have hq : selectedCapLower r.selected 0
        (qLogPrimeMeshHi 0 (19 / 96) m r.cell) + 2 * e <
          qVLo
            (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i)
            (∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i) := by
      simpa only [gateCheck, decide_eq_true_eq] using hc
    have hr :
        ((selectedCapLower r.selected 0
          (qLogPrimeMeshHi 0 (19 / 96) m r.cell) + 2 * e : ℚ) : ℝ) <
          (qVLo
            (∑ i ∈ r.selected, qLogPrimeMeshLo 0 (19 / 96) m r.cell i)
            (∑ i ∈ r.selected, qLogPrimeMeshHi 0 (19 / 96) m r.cell i) : ℝ) :=
      Rat.cast_lt.mpr hq
    push_cast at hr
    exact hr.trans_le hv
  rw [← envelope_eq_v] at hcheck
  have hfloor :
      (selectedCapLower r.selected 0
        (qLogPrimeMeshHi 0 (19 / 96) m r.cell) : ℝ) <
        candidate (e : ℝ) r.selected t := by
    dsimp [candidate]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hh : (1 / 2 : ℝ) ≤
        selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell) := by
      exact_mod_cast selectedCapLower_half_le r.selected 0 _
    exact hh.trans_lt hfloor
  · intro k
    have hu : prefixSquareExpr t k ≤
        prefixSquareExpr
          (fun i => (qLogPrimeMeshHi 0 (19 / 96) m r.cell i : ℝ)) k :=
      prefixSquareExpr_mono hhi k
    have hh :
        ((prefixSquareExpr (qLogPrimeMeshHi 0 (19 / 96) m r.cell) k : ℚ) : ℝ) ≤
          selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell) := by
      exact_mod_cast selectedCapLower_prefix_le r.selected 0 _ k
    rw [cast_prefixSquareExpr] at hh
    exact hu.trans_lt (hh.trans_lt hfloor)
  · intro k hk
    have hu : selectedSquareExpr r.selected t k ≤
        selectedSquareExpr r.selected
          (fun i => (qLogPrimeMeshHi 0 (19 / 96) m r.cell i : ℝ)) k :=
      selectedSquareExpr_mono r.selected hhi k
    have hh :
        ((selectedSquareExpr r.selected
          (qLogPrimeMeshHi 0 (19 / 96) m r.cell) k : ℚ) : ℝ) ≤
            selectedCapLower r.selected 0 (qLogPrimeMeshHi 0 (19 / 96) m r.cell) := by
      exact_mod_cast selectedCapLower_selected_le r.selected 0 _ k hk
    rw [cast_selectedSquareExpr] at hh
    exact hu.trans_lt (hh.trans_lt hfloor)

section OriginalFourthParent

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

def inherited4 (pre : List ℕ) : ℝ :=
  P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi m omega N
    rows4 (producerEligible licensed4) (fun r => r.bufferedCandidate (e : ℝ))
    (rosserAncestor 4 pre)

def exponent5 (pre : List ℕ) : ℝ :=
  if pre.length = 5 then
    finiteMax rows5 (fun r => eligible e chi m omega J5 r
      (primeHistoryLogCoordinates N 5 pre))
      (fun r => candidate (e : ℝ) r.selected
        (primeHistoryLogCoordinates N 5 pre))
      (inherited4 e chi m omega N rows4 licensed4 pre)
  else inherited4 e chi m omega N rows4 licensed4 pre

def level5 (pre : List ℕ) : ℝ :=
  N ^ exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre

def policy5 : Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (initialPolicy (e : ℝ) m N)
    (rawLevel (e : ℝ) chi m omega N)
    (level5 e chi m omega N rows4 licensed4 J5 rows5)

theorem inherited4_eq_actual_fourth (pre : List ℕ) :
    N ^ inherited4 e chi m omega N rows4 licensed4 pre =
      producerLevel4 (e : ℝ) chi m omega N rows4 licensed4
        (rosserAncestor 4 pre) := rfl

/-- h45 is structural: even a losing fifth candidate cannot lower the
fourth cap.  The fourth seed is the variable producer maximum, not old5
from a rational constant-cap table. -/
theorem inherited4_le_exponent5 (pre : List ℕ) :
    inherited4 e chi m omega N rows4 licensed4 pre ≤
      exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre := by
  unfold exponent5
  split_ifs
  · exact finiteMax_seed_le rows5 _ _ _
  · exact le_rfl

theorem fourthLevel_le_fifthLevel (hN : 1 ≤ N) (pre : List ℕ) :
    producerLevel4 (e : ℝ) chi m omega N rows4 licensed4
        (rosserAncestor 4 pre) ≤
      level5 e chi m omega N rows4 licensed4 J5 rows5 pre := by
  rw [← inherited4_eq_actual_fourth]
  exact Real.rpow_le_rpow_of_exponent_le hN
    (inherited4_le_exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre)

/-- The comparison is on each actual next candidate of the same original
rank-four frontier, including candidates rejected by the old own test. -/
theorem actual_h45 (Nnat cap : ℕ) (hN : 1 < (Nnat : ℝ)) (z : ℝ)
    (hident : N = (Nnat : ℝ))
    (frontier candidateState : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (Nnat : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse Nnat cap 0 z))
    (hc : candidateState ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining) :
    producerLevel4 (e : ℝ) chi m omega N rows4 licensed4 frontier.selectedPrefix ≤
      level5 e chi m omega N rows4 licensed4 J5 rows5
        candidateState.selectedPrefix := by
  have hfrontlen := firstExitDepthFrontier_selected_length 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (Nnat : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse Nnat cap 0 z) true 1 (by simp) frontier hf
  obtain ⟨before, q, after, hremaining, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.remaining frontier.positive frontier.mass
      candidateState).mp hc
  have ha : rosserAncestor 4 candidateState.selectedPrefix = frontier.selectedPrefix := by
    rw [hstate]
    calc
      rosserAncestor 4 (q :: frontier.selectedPrefix) =
          rosserAncestor 4 frontier.selectedPrefix :=
        rosserAncestor_cons 4 q frontier.selectedPrefix (by omega)
      _ = frontier.selectedPrefix :=
        rosserAncestor_self_of_length 4 frontier.selectedPrefix hfrontlen
  have hh := fourthLevel_le_fifthLevel e chi m omega N rows4 licensed4 J5 rows5
    (by rw [hident]; exact hN.le) candidateState.selectedPrefix
  simpa only [ha] using hh

theorem fifth_row_le_exponent5 (pre : List ℕ) (hlen : pre.length = 5)
    (r : FifthRow m) (hr : r ∈ rows5)
    (he : eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre)) :
    candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre) ≤
      exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre := by
  unfold exponent5
  rw [if_pos hlen]
  exact finiteMax_row_le rows5 _ _ _ r hr he

theorem fifth_row_full_gates (pre : List ℕ) (r : FifthRow m)
    (he : eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre)) :
    (1 / 2 : ℝ) < candidate (e : ℝ) r.selected
        (primeHistoryLogCoordinates N 5 pre) ∧
      (∀ k, prefixSquareExpr (primeHistoryLogCoordinates N 5 pre) k <
        candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre)) ∧
      (∀ k ∉ r.selected,
        selectedSquareExpr r.selected (primeHistoryLogCoordinates N 5 pre) k <
          candidate (e : ℝ) r.selected (primeHistoryLogCoordinates N 5 pre)) := by
  exact gateCheck_sound e m r _ he.2.1 he.2.2

theorem exponent5_outside (pre : List ℕ)
    (hout : ∀ r ∈ rows5,
      ¬ eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre)) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre =
      inherited4 e chi m omega N rows4 licensed4 pre := by
  unfold exponent5
  split_ifs
  · exact finiteMax_eq_seed_of_outside rows5 _ _ _ hout
  · rfl

theorem policy5_through_four (positive : Bool) (pre : List ℕ)
    (hlen : pre.length ≤ 4) :
    policy5 e chi m omega N rows4 licensed4 J5 rows5 positive pre =
      HistoricalThirdCoarse.policy (e : ℝ) chi m omega N positive pre := by
  simp only [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen]
  rfl

/-- Both policies enumerate the very same original third-capped rank-four
frontier on the same carrier; fifth rows are invisible at firstStop. -/
theorem same_rank_four_frontier (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        (policy5 e chi m omega N rows4 licensed4 J5 rows5)
        h pre positive mass carrier =
      firstExitDepthFrontier 4
        (producerPolicy4 (e : ℝ) chi m omega N rows4 licensed4)
        h pre positive mass carrier := by
  calc
    _ = firstExitDepthFrontier 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega N)
        h pre positive mass carrier := by
          exact fifthCappedUpperPolicy_frontier_four
            (initialPolicy (e : ℝ) m N) (rawLevel (e : ℝ) chi m omega N)
            (level5 e chi m omega N rows4 licensed4 J5 rows5)
            h pre carrier positive mass
    _ = _ := by
      exact (fourthCappedUpperPolicy_frontier_four
        (initialPolicy (e : ℝ) m N) (rawLevel (e : ℝ) chi m omega N)
        (producerLevel4 (e : ℝ) chi m omega N rows4 licensed4)
        h pre carrier positive mass).symm

/-- The canonical fifth correction enumerates the target-deleted rough
carrier and every next candidate from the unchanged original third parent.
Its two own-cube terms use the variable fourth and fifth levels above. -/
def actualFifthSaving (Nnat cap : ℕ) (z : ℝ) : ℝ :=
  actualHistoricalFifthSaving
    (initialPolicy (e : ℝ) m (Nnat : ℝ))
    (rawLevel (e : ℝ) chi m omega (Nnat : ℝ))
    (producerLevel4 (e : ℝ) chi m omega (Nnat : ℝ) rows4 licensed4)
    (level5 e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)
    Nnat cap z

end OriginalFourthParent
end
end ImbalancedChen.P1OriginalVariableFifthContinuation
