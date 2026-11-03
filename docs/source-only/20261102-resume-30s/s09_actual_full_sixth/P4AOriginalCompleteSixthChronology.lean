import ImbalancedChen.P4AOriginalSavedSixthArchive
import ImbalancedChen.P4AOriginalSixthLaterSemantics
import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
import ImbalancedChen.P4AOriginalFull87PrefixBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual original4/5 bank precedes the grid400 saved sixth action, the
eleven selected G7 actions, and all nineteen genuine later sixth actions.
No numerical enclosure refinement creates an action. G13's two comparison
corrections are absent from the action list, G14's four nonsingletons occur
once, and discarded old smaller-grid sixth witnesses are not added.

This is the pointwise original endpoint-source construction, before finite
higher-cap freezing. The original actual-parent admission tests are explicit
parts of the producer, not fields supplied by a caller. It does not assert
that every original saved row is admitted at an arbitrary mesh, nor remove
the need for one common compact ancestor realization.
-/
namespace ImbalancedChen.P4AOriginalCompleteSixthChronology
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation

def data (e : ℚ) (q : ℕ) (omega : ℝ) : OriginalData :=
  P4AOriginalArchiveFourteenPositivePresieve.data e q omega

def fifth (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : ℝ :=
  actualParent5 (data e q omega) N pre

/-- The saved finite-box action uses the actual current fifth parent and
the frozen own-third histories from the original preceding tree. -/
def savedEligible (e : ℚ) (q : ℕ) (omega N : ℝ)
    (i : P4AOriginalSavedSixthArchive.Row) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  pre.length = 6 ∧ P4AOriginalSavedSixthArchive.Source i t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H3 t < lambda3 (data e q omega) N pre ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < lambda3 (data e q omega) N pre ∧
    fifth e q omega N pre ≤ P4AOriginalSavedSixthArchive.oldUpper i t

def savedExponent (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Finset.univ (fun i => savedEligible e q omega N i pre)
    (fun i => P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 pre))
    (fifth e q omega N pre)

/-- The existing eleven literal actions are reused without changing their
source conditions. Saved boxes have t6>=1/50; these cells have t6<1/50.
The seed includes the preceding saved action, so it can never be erased. -/
def elevenExponent (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
    (fun c => eligibleSixth (data e q omega) N c pre)
    (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre))
    (savedExponent e q omega N pre)

/-- Current means the result of every earlier action, at this very prefix.
The guard retains the original comparison chart and fifth history. -/
def laterEligible (stage : ℕ) (current : ℝ) (N : ℝ)
    (c : P4AOriginalSixthLaterLiteral.Cell) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  pre.length = 6 ∧ P4AOriginalSixthLaterLiteral.stage c = stage ∧ P4AOriginalSixthLaterSemantics.Source c t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < current ∧ current ≤ P4AOriginalSixthLaterSemantics.comparison c t ∧
    P4AOriginalSixthLaterSemantics.comparison c t < P4AOriginalSixthLaterSemantics.endpoint c t

def applyLater (stage : ℕ) (N current : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Finset.univ (fun c => laterEligible stage current N c pre)
    (fun c => P4AOriginalSixthLaterSemantics.endpoint c (primeHistoryLogCoordinates N 6 pre)) current

def afterLater (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : ℕ → ℝ
  | 0 => elevenExponent e q omega N pre
  | k+1 => applyLater k N (afterLater e q omega N pre k) pre

def currentSixthExponent (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : ℝ :=
  afterLater e q omega N pre 8

def currentSixthPolicy (e : ℚ) (q : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (policy5 (data e q omega) N)
    (frozenParityRosserPolicy false 6 (fun pre => N ^ currentSixthExponent e q omega N pre))

theorem current_policy_eq_sixthPolicy (e : ℚ) (q : ℕ) (omega N : ℝ) :
    currentSixthPolicy e q omega N =
      P4AActualSixthFrozenEighthAdmission.sixthPolicy (policy5 (data e q omega) N)
        (fun pre => N ^ currentSixthExponent e q omega N pre) := rfl

theorem saved_seed_le (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    fifth e q omega N pre ≤ savedExponent e q omega N pre :=
  finiteMax_seed_le _ _ _ _

theorem saved_le_eleven (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    savedExponent e q omega N pre ≤ elevenExponent e q omega N pre :=
  finiteMax_seed_le _ _ _ _

theorem held_eleven_le_eleven (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    lambda6 (data e q omega) N pre ≤ elevenExponent e q omega N pre := by
  apply finiteMax_le
  · exact (saved_seed_le e q omega N pre).trans (saved_le_eleven e q omega N pre)
  · intro c hc he
    exact finiteMax_row_le _ _ _ _ c hc he

theorem afterLater_mono (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    Monotone (afterLater e q omega N pre) := by
  apply monotone_nat_of_le_succ
  intro k
  exact finiteMax_seed_le _ _ _ _

theorem held_eleven_le_current (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    lambda6 (data e q omega) N pre ≤ currentSixthExponent e q omega N pre :=
  (held_eleven_le_eleven e q omega N pre).trans
    (afterLater_mono e q omega N pre (show 0 ≤ 8 by omega))

theorem fifth_le_current (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    actualParent5 (data e q omega) N pre ≤ currentSixthExponent e q omega N pre :=
  (actualParent5_le_lambda6 (data e q omega) N pre).trans
    (held_eleven_le_current e q omega N pre)

theorem current_policy_even (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    currentSixthPolicy e q omega N true pre = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (policy5_even (data e q omega) N)
    (fun p => frozenParityRosserPolicy_upper_even 6 _ p) pre

theorem current_policy_through_six (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) (h : pre.length ≤ 6) :
    currentSixthPolicy e q omega N positive pre = policy5 (data e q omega) N positive pre := by
  simp only [currentSixthPolicy, firstExitDepthSplicePolicy, if_pos h]

theorem current_policy_after_six (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) (h : 6 < pre.length) :
    currentSixthPolicy e q omega N positive pre =
      ordinaryParityRosserPolicy false
        (N ^ currentSixthExponent e q omega N (rosserAncestor 6 pre)) positive pre := by
  simp only [currentSixthPolicy, firstExitDepthSplicePolicy,
    if_neg (by omega : ¬pre.length ≤ 6), frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem actual_eighth_frontier_admissible (e : ℚ) (q : ℕ) (omega : ℝ)
    (N enumerationCap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8 (currentSixthPolicy e q omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N enumerationCap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ)^currentSixthExponent e q omega (N : ℝ) (rosserAncestor 6 state.selectedPrefix))
      state.selectedPrefix :=
  P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
    (policy5 (data e q omega) (N : ℝ))
    (fun pre => (N : ℝ)^currentSixthExponent e q omega (N : ℝ) pre)
    N enumerationCap w z weight state hs

/-- Internal scalar invariant: proved directly from original saved and
literal source licences for every action; no continuation target is input. -/
theorem current_le_of_subset_tents (e : ℚ) (q : ℕ) (omega N R : ℝ) (pre : List ℕ)
    (hfifth : fifth e q omega N pre ≤ R)
    (htents : ∀ m ∈ Finset.Icc 1 63,
      v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m (primeHistoryLogCoordinates N 6 pre)) ≤ R) :
    currentSixthExponent e q omega N pre ≤ R := by
  have hsaved : savedExponent e q omega N pre ≤ R := by
    apply finiteMax_le _ _ _ _ _ hfifth
    intro i _ hi
    exact htents (P4AOriginalSavedSixthArchive.selectedMask i) (P4AOriginalSavedSixthArchive.source_mask_range i _ hi.2.1)
  have heleven : elevenExponent e q omega N pre ≤ R := by
    apply finiteMax_le _ _ _ _ _ hsaved
    intro c _ hc
    have hl : Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre) <
        v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask (primeHistoryLogCoordinates N 6 pre)) := by
      rw [v_eq_min]
      dsimp only [A, C]
      exact lt_min hc.2.1.selectedAscending (by linarith [hc.2.1.selectedDescending])
    exact hl.le.trans (htents c.selectedMask (by cases c <;> norm_num [Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask]))
  have hstage : ∀ k, afterLater e q omega N pre k ≤ R := by
    intro k
    induction k with
    | zero => exact heleven
    | succ k ih =>
      apply finiteMax_le _ _ _ _ _ ih
      intro c _ hc
      exact (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c _ hc.2.2.1).le.trans
        (htents (P4AOriginalSixthLaterLiteral.mask c) (P4AOriginalSixthLaterSemantics.original_mask_range c))
  exact hstage 8

end
end ImbalancedChen.P4AOriginalCompleteSixthChronology
