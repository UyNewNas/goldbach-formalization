import ImbalancedChen.P4AOriginalSixthLicensedFilter

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A new own-sixth licensed-action tree. The earlier finite fifth policy is
unchanged. Outside its supported below-mu activation branch the original
complete-sixth continuation is inherited. The original eighth action reads
its own eighth ancestor on this NEW sixth predecessor. The unsafe margin
complement is not deleted and is not granted an unproved action licence.

Source admission is reconstructed in the new tree from the original odd
history margins. No global equality of old/new eighth frontiers, signed
coefficients, numerical gains or reserve payment is asserted.
-/
namespace ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualCommonHistory P4AOriginalFull87SevenCubeAdmission
open P4AOriginalFull87FiniteParentCaps P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_of_trim selectedCap_append)
open P4AOriginalFull87FiniteParentPolicy (active active_ancestor source_active
  fifthPolicy fifth_even fifth_inactive level5Exponent)
open P4AOriginalSixthLicensedFilter

/-- The finite label depends only on its own sixth ancestor when queried
through the frozen continuation below. The activation guard is own-third. -/
def level6Exponent (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ) : ℝ :=
  if active e q om N history then licensedCap n e q om N history
  else currentSixthExponent e q om N history

def sixthPolicy (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (fifthPolicy n e q om N)
    (frozenParityRosserPolicy false 6 (fun h => N ^ level6Exponent n e q om N h))

def eighthContinuation (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (positive : Bool) (history : List ℕ) : Bool :=
  match selectedCap delta n N history with
  | none => sixthPolicy n e q om N positive history
  | some a => ordinaryParityRosserPolicy false (N ^ (a : ℝ)) positive history

def policy (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (sixthPolicy n e q om N)
    (eighthContinuation delta n e q om N)

/-- All later calls read the same selected sixth prefix, regardless of
whether this prefix used an accepted action or the fifth fallback. -/
theorem frozen_continuation_append (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (later history : List ℕ) (hlen : 6 ≤ history.length) (positive : Bool) :
    frozenParityRosserPolicy false 6 (fun h => N ^ level6Exponent n e q om N h)
        positive (later ++ history) =
      ordinaryParityRosserPolicy false
        (N ^ level6Exponent n e q om N (rosserAncestor 6 history))
        positive (later ++ history) := by
  simp only [frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_append 6 later history hlen]

/-- Both trees have this exact earlier rank-six frontier, even though
their rank-eight frontiers can differ. -/
theorem frontier_six_eq_fifth (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (weight : ℕ → ℝ) (history carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 6 (sixthPolicy n e q om N) weight history positive mass carrier =
      firstExitDepthFrontier 6 (fifthPolicy n e q om N) weight history positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 6 6 le_rfl _ _ weight history carrier positive mass

theorem sixth_even (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ) :
    sixthPolicy n e q om N true history = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (fifth_even n e q om N) (fun h => frozenParityRosserPolicy_upper_even 6 _ h) history

theorem policy_even (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ) :
    policy delta n e q om N true history = true := by
  apply UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    (sixth_even n e q om N) _ history
  intro h
  unfold eighthContinuation
  cases selectedCap delta n N h
  · exact sixth_even n e q om N h
  · simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem through_eight (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (positive : Bool) (history : List ℕ) (hlen : history.length ≤ 8) :
    policy delta n e q om N positive history = sixthPolicy n e q om N positive history := by
  simp only [policy, firstExitDepthSplicePolicy, if_pos hlen]

/-- Only the early decisions are globally identical to the raw87 tree. -/
theorem through_four_eq_raw (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (positive : Bool) (history : List ℕ) (hlen : history.length ≤ 4) :
    policy delta n e q om N positive history =
      P4AOriginalFull87CompleteSixthDispatch.policy e q om N positive history := by
  rw [through_eight delta n e q om N positive history (by omega),
    P4AOriginalFull87CompleteSixthDispatch.policy_through_eight e q om N positive history (by omega),
    current_policy_through_six e q om N positive history (by omega)]
  simp only [sixthPolicy, fifthPolicy, policy5, firstExitDepthSplicePolicy,
    if_pos (show history.length ≤ 6 by omega), if_pos hlen]

theorem sixth_inactive (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (positive : Bool) (history : List ℕ) (ha : ¬active e q om N history) :
    sixthPolicy n e q om N positive history = currentSixthPolicy e q om N positive history := by
  have hanc : ¬active e q om N (rosserAncestor 6 history) :=
    fun h => ha ((active_ancestor e q om N 6 (by decide) history).mp h)
  unfold sixthPolicy currentSixthPolicy firstExitDepthSplicePolicy
  by_cases hl : history.length ≤ 6
  · simp only [if_pos hl]
    exact fifth_inactive n e q om N positive history ha
  · simp only [if_neg hl, frozenParityRosserPolicy, ancestorFrozenPolicy,
      level6Exponent, if_neg hanc]

/-- The new eighth stage stops on its NEW sixth frontier. No equality to
the old sixth frontier is claimed after changing the earlier caps. -/
theorem frontier_eq_new_sixth (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (weight : ℕ → ℝ) (history carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (policy delta n e q om N) weight history positive mass carrier =
      firstExitDepthFrontier 8 (sixthPolicy n e q om N) weight history positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl _ _ weight history carrier positive mass

theorem selected_descendants (delta : ℝ) (hd : 0 < delta) (n : ℕ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (history later : List ℕ) (hlen : history.length = 8)
    (p : ℕ) (c : Cell) (ht : primeHistoryLogCoordinates N 8 history ∈ trim c delta)
    (positive : Bool) :
    policy delta n e q om N positive ((p :: later) ++ history) =
      ordinaryParityRosserPolicy false
        (N ^ (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ))
        positive ((p :: later) ++ history) := by
  have hdeep : ¬((p :: later) ++ history).length ≤ 8 := by
    simp only [List.length_append, List.length_cons, hlen]
    omega
  have hs := selectedCap_of_trim delta hd n N history hlen c ht
  simp only [policy, firstExitDepthSplicePolicy, if_neg hdeep, eighthContinuation,
    selectedCap_append delta n N (p :: later) history (by omega), hs]

/-- Admission is re-established in the new tree. The first/third tests
are reused exactly; the fifth/seventh tests use finite parent bounds. -/
theorem validSelection_of_history (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (he : 0 ≤ e) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ i, (p i).Prime) (c : Cell) (hs : Source c (point N p))
    (hr : RealizedHistory e q om N (pre p) c) :
    FirstExitValidSelection (policy delta n e q om N) [] true (pre p).reverse := by
  have hv := P4AOriginalFull87PolicyReverseAdmission.validSelection_of_realized_history
    e q om N he hN p hp c hs hr
  simp only [pre, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, FirstExitValidSelection,
    Bool.not_true, Bool.not_false] at hv
  obtain ⟨h1, _h2, h3, _h4, _h5, _h6, _h7, _h8, _⟩ := hv
  have hpos : ∀ i, 0 < p i := fun i => (hp i).pos
  have hord := source_strictAnti N hN p hpos c hs
  let d := data e q om
  let L := lambda3 d N (rosserAncestor 4 (pre p))
  have hadm7 := seven_admissible_of_histories N hN p hpos hord L hr.2.2.1
  have hp7 : ∀ r ∈ [p 6, p 5, p 4, p 3, p 2, p 1, p 0], r.Prime := by
    intro r h
    simp only [List.mem_cons, List.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hp _
  have ho7 := (List.pairwise_cons.mp (pre_pairwise p hord)).2
  have hadm5 := ordinaryRosserPrefixAdmissible_of_append false (N^L) [p 6, p 5]
    [p 4, p 3, p 2, p 1, p 0] hp7 ho7 hadm7
  obtain ⟨_hL, h34, h45, h56, _hup, _he4, _he5, _he6⟩ :=
    parent_bounds_of_history n e q om N (pre p) (pre_length p) c hs hr
  have hL5 : L ≤ cap5 n e q om N [p 4, p 3, p 2, p 1, p 0] := by
    simpa [L, pre, rosserAncestor] using h34.trans h45
  have hL6 : L ≤ licensedCap n e q om N [p 5, p 4, p 3, p 2, p 1, p 0] := by
    have hf : cap5 n e q om N (rosserAncestor 5 (pre p)) ≤
        licensedCap n e q om N (rosserAncestor 6 (pre p)) := by
      simpa only [rosserAncestor_nested 5 6 (by decide)] using
        fifth_le_licensedCap n e q om N (rosserAncestor 6 (pre p))
    simpa [L, pre, rosserAncestor] using (h34.trans h45).trans hf
  have ha := source_active e q om N (pre p) (pre_length p) c hs hr
  have ha5 : active e q om N [p 4, p 3, p 2, p 1, p 0] := by
    simpa [pre, rosserAncestor] using
      (active_ancestor e q om N 5 (by decide) (pre p)).mpr ha
  have ha6 : active e q om N [p 5, p 4, p 3, p 2, p 1, p 0] := by
    simpa [pre, rosserAncestor] using
      (active_ancestor e q om N 6 (by decide) (pre p)).mpr ha
  have h5new := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le hN.le hL5) hadm5
  have h7new := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le hN.le hL6) hadm7
  have ht1 : policy delta n e q om N false [p 0] = true := by
    rw [through_four_eq_raw delta n e q om N false _ (by simp)]
    exact h1
  have ht3 : policy delta n e q om N false [p 2, p 1, p 0] = true := by
    rw [through_four_eq_raw delta n e q om N false _ (by simp)]
    exact h3
  have ht5 : policy delta n e q om N false [p 4, p 3, p 2, p 1, p 0] = true := by
    simpa [policy, sixthPolicy, fifthPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level5Exponent, rosserAncestor,
      ordinaryParityRosserPolicy, oddFirstExitPolicy, ha5] using h5new
  have ht7 : policy delta n e q om N false [p 6, p 5, p 4, p 3, p 2, p 1, p 0] = true := by
    simpa [policy, sixthPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, level6Exponent, rosserAncestor,
      ordinaryParityRosserPolicy, oddFirstExitPolicy, ha6] using h7new
  simp only [pre, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.singleton_append, FirstExitValidSelection,
    Bool.not_true, Bool.not_false]
  exact ⟨ht1, policy_even delta n e q om N _, ht3, policy_even delta n e q om N _,
    ht5, policy_even delta n e q om N _, ht7, policy_even delta n e q om N _, trivial⟩

end
end ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
