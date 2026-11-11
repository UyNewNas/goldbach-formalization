import ImbalancedChen.P4AOriginalFiniteAll22RawLedger
import ImbalancedChen.P5OriginalCommonFourthSourceNavigation

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.
Actual inactive current Roots cancel. The complete actual rank-four source
retains literal ownFifth/cap5, signed states, and the original carrier.
No early numerical payment, distribution bound, or hUpper is claimed.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22EarlyInactive
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root current base common third fourth fifth five)
open P4AOriginalOrderedSixthStages (ownFifth orderedFifth orderedFifth_splice)
open P4AOriginalFiniteFallbackPolicy (Rule high dispatch)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonFourthSourceNavigation
  (firstCoordinate firstCoordinate_ancestor firstCoordinate_cons
   ancestor_first_coordinate guards_false_below_mu)
open P1OriginalVariableFourthContinuation (finiteMax_eq_seed_of_dominated)
open P1Pair12RetainedSignedSource
open P4AOriginalFull87RawChronology (rawRoot rawChange cutoff)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFiniteAll22RawLedger (lowStage lowerEarly)

theorem base_current (d : OriginalData) (omega : ℝ) (N : ℕ)
    (b : Bool) (h : List ℕ) :
    base (current d omega N h) d N b h = fresh d omega N b h := by
  rfl

theorem common_current_below (d : OriginalData) (omega : ℝ) (N : ℕ)
    (b : Bool) (h : List ℕ) (hlow : ¬high N h) :
    common (current d omega N h) d N b h = fresh d omega N b h := by
  by_cases h2 : h.length ≤ 2
  · have h3 : h.length ≤ 3 := by omega
    simpa only [common, if_pos h2, if_pos h3, Bool.or_self] using
      base_current d omega N b h
  · have hm : firstCoordinate N h ≤ VariableEnvelope.mu := le_of_not_gt hlow
    obtain ⟨hs, ht⟩ := guards_false_below_mu N h (by omega) hm
    simpa only [common, if_neg h2, if_neg hs, if_neg ht,
      ite_self, Bool.or_self] using base_current d omega N b h

/-- No historical owner premise: low and not-current.lower force initial. -/
theorem scalar_initial_of_inactive (d : OriginalData) (omega : ℝ)
    (N : ℕ) (h : List ℕ) (hlen : 3 ≤ h.length)
    (hlow : ¬high N h) (hinactive : ¬(current d omega N h).lower) :
    (current d omega N h).scalar = HistoricalThirdCoarse.initial (d.e : ℝ) := by
  have hm : firstCoordinate N h ≤ VariableEnvelope.mu := le_of_not_gt hlow
  have hx : primeHistoryLogCoordinates N 3 (rosserAncestor 3 h) 0 ≤ VariableEnvelope.mu := by
    rw [ancestor_first_coordinate N 3 (by decide) h hlen]
    exact hm
  change ¬(primeHistoryLogCoordinates N 3 (rosserAncestor 3 h) 0 ≤ VariableEnvelope.mu ∧
    HistoricalThirdCoarse.active omega N (rosserAncestor 3 h) ∧
    ∃ j ∈ P4AOriginalOrderedThirdTable.retained (d.e : ℝ) d.m,
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 h) ∈
        logPrimeMeshCell 0 (19/96) d.m j) at hinactive
  change P4AOriginalOrderedThirdTable.rawExponent (d.e : ℝ) d.m omega N
    (rosserAncestor 3 h) = HistoricalThirdCoarse.initial (d.e : ℝ)
  unfold P4AOriginalOrderedThirdTable.rawExponent
  by_cases ha : HistoricalThirdCoarse.active omega N (rosserAncestor 3 h)
  · rw [if_pos ha]
    unfold P4AOriginalOrderedThirdTable.atPoint
    split_ifs with ho
    · exact False.elim (hinactive ⟨hx, ha, ho⟩)
    · rfl
  · rw [if_neg ha]

/-- The existing range arithmetic, with the already fixed initial seed. -/
private theorem fourth_candidate_le_initial (e : ℝ)
    (r : P2OriginalFourthCapProducerInterface.ProducerRow)
    (t : Fin 4 → ℝ) :
    r.bufferedCandidate e t ≤ HistoricalThirdCoarse.initial e := by
  rw [r.bufferedCandidate_eq]
  have hv := VariableEnvelope.v_le_cap (∑ i ∈ r.selected, t i)
  dsimp [HistoricalThirdCoarse.initial, extendedDistributionCap, VariableEnvelope.cap] at *
  linarith

private theorem fifth_candidate_le_initial (e : ℝ)
    (I : Finset (Fin 5)) (t : Fin 5 → ℝ) :
    P1OriginalVariableFifthContinuation.candidate e I t ≤
      HistoricalThirdCoarse.initial e := by
  unfold P1OriginalVariableFifthContinuation.candidate
  rw [P1OriginalVariableFifthContinuation.envelope_eq_v]
  have hv := VariableEnvelope.v_le_cap (∑ i ∈ I, t i)
  dsimp [HistoricalThirdCoarse.initial, extendedDistributionCap, VariableEnvelope.cap] at *
  linarith

theorem third_initial_below (R : Root) (d : OriginalData) (N : ℝ)
    (h : List ℕ) (hlen : 3 ≤ h.length)
    (hlow : firstCoordinate N h ≤ VariableEnvelope.mu)
    (hscalar : R.scalar = HistoricalThirdCoarse.initial (d.e : ℝ)) :
    third R N h = HistoricalThirdCoarse.initial (d.e : ℝ) := by
  obtain ⟨hs, ht⟩ := guards_false_below_mu N h hlen hlow
  simp only [third, if_neg ht, if_neg hs, max_self, hscalar]

theorem fourth_initial_below (R : Root) (d : OriginalData) (N : ℝ)
    (h : List ℕ) (hlen : 3 ≤ h.length)
    (hlow : firstCoordinate N h ≤ VariableEnvelope.mu)
    (hscalar : R.scalar = HistoricalThirdCoarse.initial (d.e : ℝ)) :
    fourth R d N h = HistoricalThirdCoarse.initial (d.e : ℝ) := by
  have hthird := third_initial_below R d N h hlen hlow hscalar
  unfold fourth
  split_ifs with h4
  · rw [hthird]
    exact finiteMax_eq_seed_of_dominated _ _ _ _
      (fun r _ _ => fourth_candidate_le_initial (d.e : ℝ) r _)
  · exact hthird

theorem fifth_initial_below (R : Root) (d : OriginalData) (N : ℝ)
    (h : List ℕ) (hlen : 3 ≤ h.length)
    (hlow : firstCoordinate N h ≤ VariableEnvelope.mu)
    (hscalar : R.scalar = HistoricalThirdCoarse.initial (d.e : ℝ)) :
    fifth R d N h = HistoricalThirdCoarse.initial (d.e : ℝ) := by
  have hl4 : 3 ≤ (rosserAncestor 4 h).length := by
    simp only [rosserAncestor, List.length_drop]
    omega
  have hm4 : firstCoordinate N (rosserAncestor 4 h) ≤ VariableEnvelope.mu := by
    rw [firstCoordinate_ancestor N 4 (by decide)]
    exact hlow
  have hfourth := fourth_initial_below R d N (rosserAncestor 4 h) hl4 hm4 hscalar
  unfold fifth
  simp only [hfourth]
  split_ifs with h5
  · exact finiteMax_eq_seed_of_dominated _ _ _ _
      (fun r _ _ => fifth_candidate_le_initial (d.e : ℝ) r.selected _)
  · rfl

/-- The actual false mode uses raw fifth, so no rounding fact is assumed. -/
theorem fifth_eq_fresh_of_inactive (n : ℕ) (d : OriginalData)
    (omega : ℝ) (N : ℕ) (b : Bool) (h : List ℕ)
    (hlow : ¬high N h) (hinactive : ¬(current d omega N h).lower) :
    orderedFifth n d omega N b h = fresh d omega N b h := by
  by_cases h4 : h.length ≤ 4
  · simpa only [orderedFifth, five, firstExitDepthSplicePolicy, if_pos h4] using
      common_current_below d omega N b h hlow
  · have hlen : 3 ≤ h.length := by omega
    have hscalar := scalar_initial_of_inactive d omega N h hlen hlow hinactive
    have hl5 : 3 ≤ (rosserAncestor 5 h).length := by
      simp only [rosserAncestor, List.length_drop]
      omega
    have hm5 : firstCoordinate N (rosserAncestor 5 h) ≤ VariableEnvelope.mu := by
      rw [firstCoordinate_ancestor N 5 (by decide)]
      exact le_of_not_gt hlow
    have hf := fifth_initial_below (current d omega N h) d N
      (rosserAncestor 5 h) hl5 hm5 hscalar
    have hown : ownFifth n d omega N (rosserAncestor 5 h) =
        HistoricalThirdCoarse.initial (d.e : ℝ) := by
      simp only [ownFifth,
        P4AOriginalOrderedThirdFullPolicy.current_ancestor d omega N h 5 (by decide),
        if_neg hinactive]
      exact hf
    rw [orderedFifth_splice]
    change firstExitDepthSplicePolicy 4
      (fun pos pre => common (current d omega N pre) d N pos pre)
      (frozenParityRosserPolicy false 5 (fun pre => (N : ℝ)^ownFifth n d omega N pre))
      b h = _
    simp only [firstExitDepthSplicePolicy, if_neg h4,
      frozenParityRosserPolicy, ancestorFrozenPolicy, hown]
    rw [←base_current d omega N b h]
    simp only [base, if_neg (show ¬h.length ≤ 2 by omega), hscalar]

def earlyPolicy (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) : Rule :=
  dispatch N (fresh d omega N) (orderedFifth n d omega N)

/-- Actual mode switch and literal cap5 remain inside ownFifth. -/
def earlyTail (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) : Rule :=
  dispatch N (fresh d omega N)
    (frozenParityRosserPolicy false 5 (fun h => (N : ℝ)^ownFifth n d omega N h))

theorem early_splice (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :
    earlyPolicy n d omega N =
      firstExitDepthSplicePolicy 4 (fresh d omega N) (earlyTail n d omega N) := by
  funext b h
  by_cases h4 : h.length ≤ 4
  · simp only [earlyPolicy, firstExitDepthSplicePolicy, if_pos h4]
    by_cases hh : high N h
    · simp only [dispatch, if_pos hh]
    · simp only [dispatch, if_neg hh, orderedFifth, five,
        firstExitDepthSplicePolicy, if_pos h4]
      exact common_current_below d omega N b h hh
  · rw [earlyPolicy, orderedFifth_splice]
    simp only [earlyTail, P4AOriginalSavedSixthFrontier.afterFour,
      dispatch, firstExitDepthSplicePolicy, if_neg h4]
    split_ifs <;> rfl

theorem early_eq_fresh_of_inactive (n : ℕ) (d : OriginalData)
    (omega : ℝ) (N : ℕ) (b : Bool) (h : List ℕ)
    (hinactive : ¬(current d omega N h).lower) :
    earlyPolicy n d omega N b h = fresh d omega N b h := by
  by_cases hh : high N h
  · simp only [earlyPolicy, dispatch, if_pos hh]
  · simpa only [earlyPolicy, dispatch, if_neg hh] using
      fifth_eq_fresh_of_inactive n d omega N b h hh hinactive

theorem tail_node_inactive (n : ℕ) (d : OriginalData)
    (omega : ℝ) (N : ℕ) (b : Bool) (h : List ℕ)
    (hlen : 4 < h.length) (hinactive : ¬(current d omega N h).lower) :
    earlyTail n d omega N b h = fresh d omega N b h := by
  have he := early_eq_fresh_of_inactive n d omega N b h hinactive
  rw [early_splice] at he
  simpa only [firstExitDepthSplicePolicy, if_neg (Nat.not_le_of_gt hlen)] using he

/-- Full actual continuation cancels, for every signed terminal test. -/
theorem tail_test_inactive (n : ℕ) (d : OriginalData) (omega : ℝ)
    (N : ℕ) (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 4 ≤ pre.length) (hinactive : ¬(current d omega N pre).lower) :
    signedTest (earlyTail n d omega N) h T pre positive mass remaining =
      signedTest (fresh d omega N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hn : 4 < (p :: pre).length := by simp only [List.length_cons]; omega
    have hc : current d omega N (p :: pre) = current d omega N pre := by
      simp only [current, rosserAncestor_cons 3 p pre (by omega : 3 ≤ pre.length)]
    have hi : ¬(current d omega N (p :: pre)).lower := by
      rw [hc]
      exact hinactive
    simp only [signedTest, tail_node_inactive n d omega N (!positive) (p :: pre) hn hi]
    rw [ih pre positive mass hlen hinactive,
      ih (p :: pre) (!positive) (mass * h p) hn.le hi]

theorem signed_change (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (C : List ℕ) :
    signedTest (earlyPolicy n d omega N) h T [] true 1 C -
        signedTest (fresh d omega N) h T [] true 1 C =
      ((firstExitDepthFrontier 4 (fresh d omega N) h [] true 1 C).map
        (fun s => signedTest (earlyTail n d omega N) h T
            s.selectedPrefix s.positive s.mass s.remaining -
          signedTest (fresh d omega N) h T
            s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  rw [early_splice]
  exact signedTest_splice_sub_eq_frontier 4 (fresh d omega N)
    (earlyTail n d omega N) h T [] C true 1

theorem inactive_frontier_term_zero (n : ℕ) (d : OriginalData)
    (omega : ℝ) (N : ℕ) (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (C : List ℕ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 4 (fresh d omega N) h [] true 1 C)
    (hinactive : ¬(current d omega N s.selectedPrefix).lower) :
    signedTest (earlyTail n d omega N) h T
        s.selectedPrefix s.positive s.mass s.remaining -
      signedTest (fresh d omega N) h T
        s.selectedPrefix s.positive s.mass s.remaining = 0 := by
  have hl := firstExitDepthFrontier_selected_length 4 (fresh d omega N)
    h [] C true 1 (by simp) s hs
  rw [tail_test_inactive n d omega N h T s.selectedPrefix s.remaining
    s.positive s.mass (by omega) hinactive, sub_self]

theorem fresh_even (d : OriginalData) (omega : ℝ) (N : ℕ) (h : List ℕ) :
    fresh d omega N true h = true := by
  simp [fresh, P4AOriginalOrderedThirdTable.policy, thirdCappedUpperPolicy,
    firstExitDepthSplicePolicy, HistoricalThirdCoarse.initialPolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy,
    ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem early_even (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ)
    (h : List ℕ) : earlyPolicy n d omega N true h = true := by
  simp only [earlyPolicy, dispatch, fresh_even,
    P4AOriginalOrderedSixthSigned.fifth_even, ite_self]

private theorem signed_read (P : Rule) (hP : ∀ h, P true h = true) (N : ℕ) :
    signedTest P weight (fun _ _ => 1) [] true 1 (carrier N) = rawRoot P N := by
  rw [P5OriginalCommonFourthSourceLedger.signedTest_one_eq_polynomial]
  exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    P hP N N 0 (cutoff N)

theorem raw_change (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :
    rawRoot (earlyPolicy n d omega N) N - rawRoot (fresh d omega N) N =
      rawChange 4 (fresh d omega N) (fresh d omega N) (earlyTail n d omega N) N := by
  rw [←signed_read _ (early_even n d omega N),
    ←signed_read _ (fresh_even d omega N)]
  exact signed_change n d omega N weight (fun _ _ => 1) (carrier N)

theorem lowStage_zero_eq_early (n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) :
    lowStage 0 n e q a omega N = earlyPolicy n (data e q a) omega N := by
  rw [P4AOriginalFiniteAll22RawLedger.lowStage_zero]
  rfl

/-- Exact actual early source; only active current-root terms remain.
No numerical floor or historical13 substitution occurs. -/
theorem lowerEarly_eq_source (n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) :
    lowerEarly n e q a omega N =
      normalize N (-rawChange 4 (fresh (data e q a) omega N)
        (fresh (data e q a) omega N) (earlyTail n (data e q a) omega N) N) := by
  unfold lowerEarly
  rw [lowStage_zero_eq_early]
  congr 1
  have hc := raw_change n (data e q a) omega N
  linarith only [hc]

end
end ImbalancedChen.P4AOriginalFiniteAll22EarlyInactive
