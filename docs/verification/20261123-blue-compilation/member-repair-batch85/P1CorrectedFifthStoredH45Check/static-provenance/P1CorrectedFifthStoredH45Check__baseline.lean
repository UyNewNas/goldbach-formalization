import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A finite rational whole-cell check supplies the missing corrected stored
h45 comparison. The seed upper bound keeps the exact rational transition
test and safely includes both potentially gated original Gamma branches.
Every supplied fourth producer row receives a qVHi upper bound on the
projected ORIGINAL fifth mesh box, even when the row is ineligible there.

The check is arithmetic data only: it reads no N, actual prime history,
licensing predicate, density, integral or saving. No claim is made that the
adopted numerical rows pass it. That concrete finite instance remains OPEN.
-/

namespace ImbalancedChen.P1CorrectedFifthStoredH45Check

open scoped BigOperators
open VariableEnvelope

/-- All potentially contributing Gamma branch endpoints, without the
real xz/yz admission tests. This is a computable conservative upper bound. -/
def fullGammaUpperQ (b : RationalBox) : ℚ :=
  max (qVLo b.lx b.ux) (max (qVLo (b.lx + b.ly) (b.ux + b.uy))
    (max (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
      (max (HistoricalThirdCoarse.rescue b)
        (max (qVLo (b.lx + b.lz) (b.ux + b.uz))
          (qVLo (b.ly + b.lz) (b.uy + b.uz))))))

/-- The original transition is rational when e is rational. -/
def gammaUpperQ (e : ℚ) (b : RationalBox) : ℚ :=
  if b.ux ≤ 25 / 128 - 4 * e then fullGammaUpperQ b else qVLo b.lx b.ux

def seedUpperQ (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) : ℚ :=
  gammaUpperQ e (HistoricalThirdCoarse.box m
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)) - 2 * e

def projectedLo (m : ℕ) (j : Fin 5 → Fin (m + 1)) : Fin 4 → ℚ :=
  historicalPrefixProject (by omega : 4 ≤ 5) (qLogPrimeMeshLo 0 (19 / 96) m j)

def projectedHi (m : ℕ) (j : Fin 5 → Fin (m + 1)) : Fin 4 → ℚ :=
  historicalPrefixProject (by omega : 4 ≤ 5) (qLogPrimeMeshHi 0 (19 / 96) m j)

def rowUpperQ (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1))
    (r : P2OriginalFourthCapProducerInterface.ProducerRow) : ℚ :=
  qVHi (∑ i ∈ r.selected, projectedLo m j i)
    (∑ i ∈ r.selected, projectedHi m j i) - 2 * e

/-- Explicit finite decidability avoids a real comparison or classical
proposition decision inside the rational row checker. -/
def rowUpperCheck (D : HistoricalPrefixCapData) (e : ℚ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (j : Fin 5 → Fin (D.m + 1)) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := rows4)
    (p := fun r _ => rowUpperQ e D.m j r ≤ D.cap5 j))

def storedH45Check (D : HistoricalPrefixCapData)
    (J : Finset (Fin 5 → Fin (D.m + 1))) (e : ℚ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := D.cells5 ∩ J)
    (p := fun j _ => seedUpperQ e D.m j ≤ D.cap5 j ∧ rowUpperCheck D e rows4 j = true))

noncomputable section
open scoped Classical
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary

theorem fullGamma_le_fullGammaUpperQ (e : ℝ) (b : RationalBox) :
    HistoricalThirdCoarse.fullGamma e b ≤ fullGammaUpperQ b := by
  have h0 : qVLo b.lx b.ux ≤ fullGammaUpperQ b := le_max_left _ _
  have hxy : qVLo (b.lx + b.ly) (b.ux + b.uy) ≤ fullGammaUpperQ b :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hxyz : qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) ≤ fullGammaUpperQ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hr : HistoricalThirdCoarse.rescue b ≤ fullGammaUpperQ b :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hxz : qVLo (b.lx + b.lz) (b.ux + b.uz) ≤ fullGammaUpperQ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hyz : qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ fullGammaUpperQ b :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  unfold HistoricalThirdCoarse.fullGamma
  simp only [max_le_iff]
  refine ⟨h0, hxy, hxyz, hr, ?_, ?_⟩
  · split_ifs <;> assumption
  · split_ifs <;> assumption

theorem gamma_le_gammaUpperQ (e : ℚ) (b : RationalBox) :
    HistoricalThirdCoarse.gamma (e : ℝ) b ≤ gammaUpperQ e b := by
  by_cases hq : b.ux ≤ 25 / 128 - 4 * e
  · have hr : (b.ux : ℝ) ≤ mu - 4 * (e : ℝ) := by
      change (b.ux : ℝ) ≤ 25 / 128 - 4 * (e : ℝ)
      exact_mod_cast hq
    simp only [gammaUpperQ, if_pos hq, HistoricalThirdCoarse.gamma, if_pos hr]
    exact fullGamma_le_fullGammaUpperQ (e : ℝ) b
  · have hr : ¬ (b.ux : ℝ) ≤ mu - 4 * (e : ℝ) := by
      intro h
      apply hq
      change (b.ux : ℝ) ≤ 25 / 128 - 4 * (e : ℝ) at h
      exact_mod_cast h
    simp only [gammaUpperQ, if_neg hq, HistoricalThirdCoarse.gamma, if_neg hr]
    exact le_rfl

theorem storedH45Check_sound
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m)) (e : ℚ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (hcheck : storedH45Check D J e rows4 = true) :
    ∀ j ∈ D.cells5 ∩ J, seedUpperQ e D.m j ≤ D.cap5 j ∧
      ∀ r ∈ rows4, rowUpperQ e D.m j r ≤ D.cap5 j := by
  have h : ∀ j ∈ D.cells5 ∩ J,
      seedUpperQ e D.m j ≤ D.cap5 j ∧ rowUpperCheck D e rows4 j = true := by
    simpa only [storedH45Check, decide_eq_true_eq] using hcheck
  intro j hj
  refine ⟨(h j hj).1, ?_⟩
  simpa only [rowUpperCheck, decide_eq_true_eq] using (h j hj).2

/-- A qVHi row bound is valid on the projected whole original fifth box,
regardless of whether the row is licensed or its own producer box meets it. -/
theorem bufferedCandidate_le_rowUpperQ
    (e : ℚ) (m : ℕ) (j : Label5 m)
    (r : P2OriginalFourthCapProducerInterface.ProducerRow) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    r.bufferedCandidate (e : ℝ) (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤
      (rowUpperQ e m j r : ℝ) := by
  have hlo (i : Fin 4) : (projectedLo m j i : ℝ) ≤
      historicalPrefixProject (by omega : 4 ≤ 5) t i := by
    unfold projectedLo historicalPrefixProject
    rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j)]
    exact (mem_logPrimeMeshCell.mp ht _).1
  have hhi (i : Fin 4) : historicalPrefixProject (by omega : 4 ≤ 5) t i ≤
      (projectedHi m j i : ℝ) := by
    unfold projectedHi historicalPrefixProject
    rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j)]
    exact (mem_logPrimeMeshCell.mp ht _).2.le
  have hslo : ((∑ i ∈ r.selected, projectedLo m j i : ℚ) : ℝ) ≤
      ∑ i ∈ r.selected, historicalPrefixProject (by omega : 4 ≤ 5) t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hlo i)
  have hshi : (∑ i ∈ r.selected, historicalPrefixProject (by omega : 4 ≤ 5) t i) ≤
      ((∑ i ∈ r.selected, projectedHi m j i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hhi i)
  rw [r.bufferedCandidate_eq]
  have hv := v_le_qVHi hslo hshi
  simpa only [rowUpperQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] using
    sub_le_sub_right hv (2 * (e : ℝ))

theorem originalVariableFourthProfile_le_storedCap
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) D.m j) :
    originalVariableFourthProfile e chi omega D.m j rows4 licensed4 t ≤ (D.cap5 j : ℝ) := by
  have hselected : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) := by
    apply (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) j).mpr
    exact ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have hs := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi D.m omega (D.cells5 ∩ J) j hselected ht
  have hc := storedH45Check_sound D J e rows4 hcheck j hj
  unfold originalVariableFourthProfile P1OriginalVariableFourthContinuation.profile4
  apply P1OriginalVariableFourthContinuation.finiteMax_le
  · rw [hs]
    have hq := (sub_le_sub_right (gamma_le_gammaUpperQ e
      (HistoricalThirdCoarse.box D.m
        (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j))) (2 * e)).trans hc.1
    have hr : ((HistoricalThirdCoarse.gamma (e : ℝ)
        (HistoricalThirdCoarse.box D.m
          (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner j)) - 2 * e : ℚ) : ℝ) ≤
        (D.cap5 j : ℝ) := Rat.cast_le.mpr hq
    simpa only [HistoricalThirdCoarse.levelExponent, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_ofNat] using hr
  · intro r hr _he
    exact (bufferedCandidate_le_rowUpperQ e D.m j r t ht).trans
      (Rat.cast_le.mpr (hc.2 r hr))

/-- On any actual five-prime history the selected branch uses the finite
check; the outside branch keeps exactly the same fourth ancestor. -/
theorem fourthAncestorLevel_le_correctedStoredLevel
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (N : ℕ) (hN : 1 < N) (history : List ℕ) (hlen : history.length = 5)
    (hprime : ∀ p ∈ history, Nat.Prime p) :
    P1OriginalVariableFourthContinuation.producerLevel4 (e : ℝ) chi D.m omega (N : ℝ)
        rows4 licensed4 (rosserAncestor 4 history) ≤
      P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
        D J e chi omega (N : ℝ) rows4 licensed4 history := by
  unfold P1OriginalVariableFourthContinuation.producerLevel4
    P1OriginalVariableFourthContinuation.level4
    P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le)
  by_cases hcell : ∃ j ∈ D.cells5 ∩ J,
      primeHistoryLogCoordinates (N : ℝ) 5 history ∈ logPrimeMeshCell 0 (19 / 96) D.m j
  · obtain ⟨j, hj, ht⟩ := hcell
    have ht' : actualPrimeTupleLog N (primeHistoryTuple 5 history) ∈
        logPrimeMeshCell 0 (19 / 96) D.m j := ht
    have hp : ∀ i, 0 < primeHistoryTuple 5 history i :=
      primeHistoryTuple_pos hlen (fun p hp => (hprime p hp).pos)
    have hold := original_fourth_exponent_on_fifth_cell D e chi omega rows4 licensed4
      N hN (primeHistoryTuple 5 history) hp j ht'
    rw [tupleHistory_primeHistoryTuple history hlen] at hold
    rw [hold, P1VariableFifthOriginalBaseQ3Bridge.corrected_stored_level_on_selected_cell
      D J e chi omega (N : ℝ) rows4 licensed4 history hlen j hj ht]
    exact originalVariableFourthProfile_le_storedCap D J e chi omega rows4 licensed4
      howned hcheck j hj _ ht'
  · have hout : ∀ j ∈ D.cells5 ∩ J,
        primeHistoryLogCoordinates (N : ℝ) 5 history ∉
          logPrimeMeshCell 0 (19 / 96) D.m j := by
      intro j hj ht
      exact hcell ⟨j, hj, ht⟩
    exact (P1VariableFifthOriginalBaseQ3Bridge.corrected_stored_exponent_outside
      D J e chi omega (N : ℝ) rows4 licensed4 history hout).symm.le

theorem actual_h45
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (frontier candidate : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4 (originalT3 e chi D.m omega N)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hc : candidate ∈ firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining) :
    originalQ4 e chi D.m omega N rows4 licensed4 frontier.selectedPrefix ≤
      P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
        D J e chi omega (N : ℝ) rows4 licensed4 candidate.selectedPrefix := by
  obtain ⟨hlen, _hsort, _hP, _hcut, _hremaining, _hsign, _hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry 4 (originalT3 e chi D.m omega N) N cap z
      frontier hf candidate hc
  have hfrontlen := firstExitDepthFrontier_selected_length 4
    (originalT3 e chi D.m omega N) (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) frontier hf
  obtain ⟨_before, q, _after, _hrem, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix frontier.remaining
        frontier.positive frontier.mass candidate).mp hc
  have ha : rosserAncestor 4 candidate.selectedPrefix = frontier.selectedPrefix := by
    rw [hstate, rosserAncestor_cons 4 q frontier.selectedPrefix (by omega),
      rosserAncestor_self_of_length 4 frontier.selectedPrefix hfrontlen]
  have hh := fourthAncestorLevel_le_correctedStoredLevel D J e chi omega rows4 licensed4
    howned hcheck N hN candidate.selectedPrefix hlen hprime
  simpa only [ha, originalQ4] using hh

/-- The formerly missing h45 premise is now supplied by a genuine finite
rational checker. No desired density or saving is a hypothesis. -/
theorem corrected_fourth_to_fifth_finite_density_identity
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
    (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows4 = true)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    originalFourthRetained e chi D.m omega N cap z rows4 licensed4 -
      firstExitRetainedPolynomial
        (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredPolicy5
          D J e chi omega (N : ℝ) rows4 licensed4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      correctedStoredCharge D J e chi omega N cap z rows4 licensed4 := by
  unfold originalFourthRetained
    P1VariableFifthOriginalBaseQ3Bridge.correctedStoredPolicy5 correctedStoredCharge
  apply actualHistoricalFifthSaving_eq
  · intro state hstate
    exact P1OriginalVariableFourthContinuation.producer_actual_h34
      (e : ℝ) chi D.m omega N cap (by exact_mod_cast hN.le) z rows4 licensed4 state
      (by simpa only [originalBase, originalQ3, HistoricalThirdCoarse.policy] using hstate)
  · intro frontier hf candidate hc
    exact actual_h45 D J e chi omega rows4 licensed4 howned hcheck N cap hN z
      frontier candidate hf hc

end
end ImbalancedChen.P1CorrectedFifthStoredH45Check
