import ImbalancedChen.P4AOriginalFull87FiniteEighthCap
import ImbalancedChen.P4AOriginalFull87ActualSourceMembership
import ImbalancedChen.P4AOriginalFull87CompleteSixthSignedSource

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

An explicit finite-cap EIGHTH stage on the unchanged COMPLETE sixth tree.
All original source tests are read at the same frozen eighth ancestor.
The actual earlier tree, occurrence list, signs and carriers are untouched.
Outside the trimmed source the complete predecessor is inherited. In
particular this policy is NOT identified with the raw full87 policy or
with the held compiledRho. Ranks 4/5/6 have not been scalar-finitized here.
-/
namespace ImbalancedChen.P4AOriginalFull87FiniteEighthPolicy
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope P4AOriginalFull87SourceDictionary
open P1Pair12RetainedSignedSource
open P4AOriginalFull87StrictActionTrim P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalCompleteSixthChronology (currentSixthPolicy currentSixthExponent)
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length)
open P4AOriginalFull87ActualSourceMembership (canonicalState)

/-- The source owner is the ORIGINAL owner. No new tie-breaking rule or
future child query is introduced. The scalar belongs to a pre-N alphabet. -/
def selectedCap (delta : ℝ) (n : ℕ) (N : ℝ) (history : List ℕ) : Option ℚ :=
  match ownerAtPrefix N history with
  | none => none
  | some c =>
      if point8 N history ∈ trim c delta then
        some (finiteCap n c (point8 N history)) else none

theorem selectedCap_some_spec (delta : ℝ) (n : ℕ) (N : ℝ)
    (history : List ℕ) (a : ℚ) (ha : selectedCap delta n N history = some a) :
    ∃ c : Cell, ownerAtPrefix N history = some c ∧
      point8 N history ∈ trim c delta ∧ a = finiteCap n c (point8 N history) := by
  cases ho : ownerAtPrefix N history with
  | none => simp [selectedCap, ho] at ha
  | some c =>
      by_cases ht : point8 N history ∈ trim c delta
      · have heq : finiteCap n c (point8 N history) = a := by
          simpa only [selectedCap, ho, if_pos ht, Option.some.injEq] using ha
        exact ⟨c, ho, ht, heq.symm⟩
      · simp [selectedCap, ho, ht] at ha

theorem selectedCap_mem_alphabet (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (N : ℝ) (history : List ℕ) (a : ℚ)
    (ha : selectedCap delta n N history = some a) : a ∈ alphabet n := by
  obtain ⟨c, _, ht, rfl⟩ := selectedCap_some_spec delta n N history a ha
  exact finiteCap_mem_alphabet n (trim_subset_source c hd ht)

theorem selectedCap_append (delta : ℝ) (n : ℕ) (N : ℝ)
    (later history : List ℕ) (hl : 8 ≤ history.length) :
    selectedCap delta n N (later ++ history) = selectedCap delta n N history := by
  simp only [selectedCap,
    P4AOriginalFull87SourceDispatch.ownerAtPrefix_append N later history hl,
    P4AOriginalFull87SourceDispatch.point8_append N later history hl]

theorem point8_at_eight (N : ℝ) (history : List ℕ) (hl : history.length = 8) :
    point8 N history = primeHistoryLogCoordinates N 8 history := by
  rw [point8, rosserAncestor_self_of_length 8 history hl]

theorem selectedCap_of_trim (delta : ℝ) (hd : 0 < delta) (n : ℕ)
    (N : ℝ) (history : List ℕ) (hl : history.length = 8) (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c delta) :
    selectedCap delta n N history =
      some (finiteCap n c (primeHistoryLogCoordinates N 8 history)) := by
  have ho := (P4AOriginalFull87SourceDispatch.ownerAtPrefix_rank_eight N history hl c).mpr
    (trim_subset_source c hd ht)
  simp only [selectedCap, ho, point8_at_eight N history hl, if_pos ht]

def continuation (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ) : Bool :=
  match selectedCap delta n N history with
  | none => currentSixthPolicy e q omega N positive history
  | some a => ordinaryParityRosserPolicy false (N ^ (a : ℝ)) positive history

/-- Only the new eighth stage is changed. This is deliberately not named
rho or compiledRho and is not a claimed replacement of the earlier tree. -/
def eighthPolicy (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (currentSixthPolicy e q omega N)
    (continuation delta n e q omega N)

theorem through_eight (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ) (hl : history.length ≤ 8) :
    eighthPolicy delta n e q omega N positive history =
      currentSixthPolicy e q omega N positive history := by
  simp only [eighthPolicy, firstExitDepthSplicePolicy, if_pos hl]

theorem policy_even (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (history : List ℕ) : eighthPolicy delta n e q omega N true history = true := by
  by_cases hl : history.length ≤ 8
  · rw [through_eight delta n e q omega N true history hl]
    exact P4AOriginalCompleteSixthChronology.current_policy_even e q omega N history
  · simp only [eighthPolicy, firstExitDepthSplicePolicy, if_neg hl, continuation]
    cases selectedCap delta n N history
    · exact P4AOriginalCompleteSixthChronology.current_policy_even e q omega N history
    · simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem no_action_inherits (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hn : selectedCap delta n N history = none) :
    eighthPolicy delta n e q omega N positive history =
      currentSixthPolicy e q omega N positive history := by
  by_cases hl : history.length ≤ 8
  · exact through_eight delta n e q omega N positive history hl
  · simp only [eighthPolicy, firstExitDepthSplicePolicy, if_neg hl, continuation, hn]

/-- Original no-owner/equality/inherit strata remain exactly as before. -/
theorem no_original_owner_unchanged (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (omega N : ℝ) (positive : Bool) (history : List ℕ)
    (ho : ownerAtPrefix N history = none) :
    eighthPolicy delta n e q omega N positive history =
      P4AOriginalFull87CompleteSixthDispatch.policy e q omega N positive history := by
  rw [no_action_inherits delta n e q omega N positive history
      (by simp only [selectedCap, ho]),
    P4AOriginalFull87CompleteSixthDispatch.policy_outside e q omega N positive history ho]

/-- Exact list equality, not just equality of supports or sums. -/
theorem frontier_eq_complete (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (weight : ℕ → ℝ) (history carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (eighthPolicy delta n e q omega N)
      weight history positive mass carrier =
    firstExitDepthFrontier 8 (currentSixthPolicy e q omega N)
      weight history positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl _ _ weight history carrier positive mass

theorem frontier_eq_raw87 (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (weight : ℕ → ℝ) (history carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (eighthPolicy delta n e q omega N)
      weight history positive mass carrier =
    firstExitDepthFrontier 8 (P4AOriginalFull87CompleteSixthDispatch.policy e q omega N)
      weight history positive mass carrier := by
  rw [frontier_eq_complete,
    P4AOriginalFull87CompleteSixthDispatch.policy_frontier]

theorem selected_descendants (delta : ℝ) (hd : 0 < delta) (n : ℕ)
    (e : ℚ) (q : ℕ) (omega N : ℝ) (history later : List ℕ)
    (hl : history.length = 8) (p : ℕ) (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c delta) (positive : Bool) :
    eighthPolicy delta n e q omega N positive ((p :: later) ++ history) =
      ordinaryParityRosserPolicy false
        (N ^ (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ))
        positive ((p :: later) ++ history) := by
  have hdeep : ¬((p :: later) ++ history).length ≤ 8 := by
    simp only [List.length_append, List.length_cons, hl]
    omega
  have ho := selectedCap_of_trim delta hd n N history hl c ht
  simp only [eighthPolicy, firstExitDepthSplicePolicy, if_neg hdeep, continuation,
    selectedCap_append delta n N (p :: later) history (by omega), ho]

/-- The actual occurrence list of trimmed original owners in this policy. -/
def trimmedStates (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (c : Cell) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 (eighthPolicy delta n e q omega (N : ℝ))
    weight [] true 1 (roughPrimeUniverse N cap w z)).filter fun state =>
      decide (ownerAtPrefix (N : ℝ) state.selectedPrefix = some c ∧
        point8 (N : ℝ) state.selectedPrefix ∈ trim c delta)

/-- A raw original source state survives as the SAME state, with its exact
mass/sign/suffix. The public schedule below supplies the raw membership. -/
theorem canonical_mem_trimmedStates (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (omega : ℝ) (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (p : Fin 8 → ℕ) (c : Cell)
    (ht : point (N : ℝ) p ∈ trim c delta)
    (hr : canonicalState N cap w weight p ∈
      P4AOriginalFull87ActualSourceMembership.sourceStates e q omega N cap w z weight c) :
    canonicalState N cap w weight p ∈ trimmedStates delta n e q omega N cap w z weight c := by
  obtain ⟨hfrontier, howner⟩ := List.mem_filter.mp hr
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true ⟨of_decide_eq_true howner, ?_⟩⟩
  · rw [frontier_eq_raw87]
    exact hfrontier
  · change point8 (N : ℝ) (pre p) ∈ trim c delta
    rw [point8_at_eight (N : ℝ) (pre p) (pre_length p)]
    exact ht

/-- Independent actual-frontier source for the new finite eighth stage.
This is not a desired density estimate defined as a difference of targets. -/
def signedChange (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  ((firstExitDepthFrontier 8 (currentSixthPolicy e q omega N)
    weight [] true 1 carrier).map fun state =>
      signedTest (continuation delta n e q omega N) weight T
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest (currentSixthPolicy e q omega N) weight T
        state.selectedPrefix state.positive state.mass state.remaining).sum

theorem signed_change_eq (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ)
    (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (eighthPolicy delta n e q omega N) weight T [] true 1 carrier -
      signedTest (currentSixthPolicy e q omega N) weight T [] true 1 carrier =
        signedChange delta n e q omega N weight T carrier :=
  signedTest_splice_sub_eq_frontier 8 _ _ weight T [] carrier true 1

end
end ImbalancedChen.P4AOriginalFull87FiniteEighthPolicy
