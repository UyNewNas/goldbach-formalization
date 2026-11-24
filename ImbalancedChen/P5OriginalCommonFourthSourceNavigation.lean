import ImbalancedChen.P5OriginalCommonRefinedSource
import ImbalancedChen.P1OriginalFirstStopInheritance

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original fourth tree and the common fourth tree have the same rank-two
frontier. Their actual continuations agree on t1 <= mu, including equality.
The remaining change is localized to t1 > mu on that original frontier;
no identity between the two global policies or signed monotonicity is used.
-/
namespace ImbalancedChen.P5OriginalCommonFourthSourceNavigation
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1Pair12RetainedSignedSource

def original4 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  P1OriginalVariableFourthContinuation.producerPolicy4
    (d.e : ℝ) d.chi d.m d.omega N d.rows4 d.licensed4

def firstCoordinate (N : ℝ) (pre : List ℕ) : ℝ :=
  primeHistoryLogCoordinates N 1 (rosserAncestor 1 pre) 0

theorem firstCoordinate_ancestor (N : ℝ) (k : ℕ) (hk : 1 ≤ k) (pre : List ℕ) :
    firstCoordinate N (rosserAncestor k pre) = firstCoordinate N pre := by
  simp only [firstCoordinate, rosserAncestor_nested 1 k hk]

theorem firstCoordinate_cons (N : ℝ) (p : ℕ) (pre : List ℕ)
    (hlen : 1 ≤ pre.length) : firstCoordinate N (p :: pre) = firstCoordinate N pre := by
  simp only [firstCoordinate, rosserAncestor_cons 1 p pre hlen]

theorem ancestor_first_coordinate (N : ℝ) (k : ℕ) (hk : 0 < k)
    (pre : List ℕ) (hlen : k ≤ pre.length) :
    primeHistoryLogCoordinates N k (rosserAncestor k pre) ⟨0, hk⟩ =
      firstCoordinate N pre := by
  have hl : (rosserAncestor k pre).length = k := by
    rw [rosserAncestor_length, min_eq_left hlen]
  have h := primeHistoryLogCoordinates_ancestor N hl (by omega : 1 ≤ k) (0 : Fin 1)
  simpa only [firstCoordinate, rosserAncestor_nested 1 k (by omega)] using h.symm

theorem guards_false_below_mu (N : ℝ) (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hmu : firstCoordinate N pre ≤ VariableEnvelope.mu) :
    ¬secondGuard N pre ∧ ¬thirdGuard N pre := by
  have h2 := ancestor_first_coordinate N 2 (by omega) pre (by omega)
  have h3 := ancestor_first_coordinate N 3 (by omega) pre hlen
  constructor
  · intro hs
    have hx := hs.1
    change VariableEnvelope.mu <
      primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0 at hx
    rw [h2] at hx
    exact (not_lt_of_ge hmu) hx
  · intro ht
    have hx := ht.1
    change VariableEnvelope.mu <
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0 at hx
    rw [h3] at hx
    exact (not_lt_of_ge hmu) hx

theorem common3_eq_original_below_mu (d : OriginalData) (N : ℝ)
    (positive : Bool) (pre : List ℕ)
    (hmu : firstCoordinate N pre ≤ VariableEnvelope.mu) :
    common3 d N positive pre = old3 d N positive pre := by
  by_cases h2 : pre.length ≤ 2
  · exact common3_through_two d N positive pre h2
  · obtain ⟨hs, ht⟩ := guards_false_below_mu N pre (by omega) hmu
    have hf : fallback23 d N positive pre = old3 d N positive pre := by
      simp [fallback23, finalPolicy, secondPolicy, thirdReplacement,
        secondReplacement, hs, ht, firstExitDepthSplicePolicy, oldPolicy, old3]
    simp [common3, hf]

theorem fourth_level_eq_original_below_mu (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (hmu : firstCoordinate N pre ≤ VariableEnvelope.mu) :
    level4 d N pre = P1OriginalVariableFourthContinuation.producerLevel4
      (d.e : ℝ) d.chi d.m d.omega N d.rows4 d.licensed4 pre := by
  obtain ⟨hs, ht⟩ := guards_false_below_mu N pre (by omega) hmu
  simp only [level4, exponent4, if_pos hlen, lambda3, fallbackSeed,
    if_neg ht, if_neg hs, max_self, originalSeed,
    P1OriginalVariableFourthContinuation.producerLevel4,
    P1OriginalVariableFourthContinuation.level4,
    P1OriginalVariableFourthContinuation.exponent4,
    P1OriginalVariableFourthContinuation.profile4]

theorem original4_through_four (d : OriginalData) (N : ℝ) (positive : Bool)
    (pre : List ℕ) (hlen : pre.length ≤ 4) :
    original4 d N positive pre = old3 d N positive pre := by
  exact P1OriginalVariableFourthContinuation.policy4_through_four
    (d.e : ℝ) d.chi d.m d.omega N d.rows4
    (P1OriginalVariableFourthContinuation.producerEligible d.licensed4)
    (fun r => r.bufferedCandidate (d.e : ℝ)) positive pre hlen

theorem common4_eq_original_below_mu (d : OriginalData) (N : ℝ)
    (positive : Bool) (pre : List ℕ)
    (hmu : firstCoordinate N pre ≤ VariableEnvelope.mu) :
    policy4 d N positive pre = original4 d N positive pre := by
  by_cases h4 : pre.length ≤ 4
  · rw [original4_through_four d N positive pre h4]
    simpa only [policy4, firstExitDepthSplicePolicy, if_pos h4] using
      common3_eq_original_below_mu d N positive pre hmu
  · have ha : (rosserAncestor 4 pre).length = 4 := by
      rw [rosserAncestor_length, min_eq_left (by omega : 4 ≤ pre.length)]
    have hm : firstCoordinate N (rosserAncestor 4 pre) ≤ VariableEnvelope.mu := by
      rwa [firstCoordinate_ancestor N 4 (by omega)]
    have hQ := fourth_level_eq_original_below_mu d N _ ha hm
    simpa only [policy4, original4,
      P1OriginalVariableFourthContinuation.producerPolicy4,
      P1OriginalVariableFourthContinuation.policy4, fourthCappedUpperPolicy,
      firstExitDepthSplicePolicy, if_neg h4, frozenParityRosserPolicy,
      ancestorFrozenPolicy] using congrArg
        (fun Q => ordinaryParityRosserPolicy false Q positive pre) hQ

theorem common4_eq_splice_original (d : OriginalData) (N : ℝ) :
    policy4 d N = firstExitDepthSplicePolicy 2 (original4 d N) (policy4 d N) := by
  funext positive pre
  by_cases h2 : pre.length ≤ 2
  · have h4 : pre.length ≤ 4 := by omega
    rw [firstExitDepthSplicePolicy, if_pos h2, original4_through_four d N positive pre h4]
    simpa only [policy4, firstExitDepthSplicePolicy, if_pos h4] using
      common3_through_two d N positive pre h2
  · simp only [firstExitDepthSplicePolicy, if_neg h2]

theorem original4_second_frontier (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 2 (original4 d N) h pre positive mass carrier =
      firstExitDepthFrontier 2 (old3 d N) h pre positive mass carrier := by
  exact firstExitDepthFrontier_depthSplice_eq 2 4 (by omega) _ _ h pre carrier positive mass

theorem common4_second_frontier (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 2 (policy4 d N) h pre positive mass carrier =
      firstExitDepthFrontier 2 (old3 d N) h pre positive mass carrier := by
  rw [common4_eq_splice_original, firstExitDepthFrontier_depthSplice_eq 2 2 le_rfl,
    original4_second_frontier]

/-- The equality is for every signed terminal test, including AP-minus-mean
and sign-dependent small beta, on the whole literal continuation. -/
theorem continuation_eq_below_mu (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (pre : List ℕ)
    (hlen : 1 ≤ pre.length) (hmu : firstCoordinate N pre ≤ VariableEnvelope.mu)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy4 d N) h T pre positive mass remaining =
      signedTest (original4 d N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hm : firstCoordinate N (p :: pre) ≤ VariableEnvelope.mu := by
      rwa [firstCoordinate_cons N p pre hlen]
    simp only [signedTest, common4_eq_original_below_mu d N (!positive) (p :: pre) hm]
    rw [ih (pre := pre) (positive := positive) (mass := mass)
        (hlen := hlen) (hmu := hmu),
      ih (pre := p :: pre) (positive := !positive) (mass := mass * h p)
        (hlen := by simp; omega) (hmu := hm)]

/-- Only the actual retained above-mu second branches carry a correction.
The list is not deduplicated and the full incoming state remains intact. -/
def correctionTest (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  (((firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier).filter
    (fun state => decide (VariableEnvelope.mu < firstCoordinate N state.selectedPrefix))).map
      (fun state => signedTest (policy4 d N) h T state.selectedPrefix
          state.positive state.mass state.remaining -
        signedTest (original4 d N) h T state.selectedPrefix
          state.positive state.mass state.remaining)).sum

theorem common4_sub_original_eq_correction (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    signedTest (policy4 d N) h T [] true 1 carrier -
      signedTest (original4 d N) h T [] true 1 carrier =
        correctionTest d N h T carrier := by
  have he := signedTest_splice_sub_eq_frontier 2 (original4 d N) (policy4 d N)
    h T [] carrier true 1
  rw [← common4_eq_splice_original, original4_second_frontier] at he
  rw [he, correctionTest]
  generalize hs : firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier = states
  have hlen : ∀ state ∈ states, state.selectedPrefix.length = 2 := by
    intro state hstate
    rw [← hs] at hstate
    exact firstExitDepthFrontier_selected_length 2 _ h [] carrier true 1
      (by simp) state hstate
  clear he hs
  revert hlen
  induction states with
  | nil => intro hlen; simp
  | cons state states ih =>
    intro hlen
    have hl := hlen state (by simp)
    have htail : ∀ s ∈ states, s.selectedPrefix.length = 2 :=
      fun s hs => hlen s (by simp [hs])
    by_cases hm : VariableEnvelope.mu < firstCoordinate N state.selectedPrefix
    · simp [hm, ih htail]
    · have hc := continuation_eq_below_mu d N h T state.selectedPrefix
        (by omega) (le_of_not_gt hm) state.positive state.mass state.remaining
      simp [hm, hc, ih htail]

/-- First-stop and initial cube are extracted from this correction's actual
frontier, rather than appended as geometric eligibility hypotheses. -/
theorem correction_frontier_original_tests (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (carrier : List ℕ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ (firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier).filter
      (fun state => decide (VariableEnvelope.mu < firstCoordinate N state.selectedPrefix))) :
    state.selectedPrefix.length = 2 ∧
      VariableEnvelope.mu < firstCoordinate N state.selectedPrefix ∧
      HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m N
        (rosserAncestor 1 state.selectedPrefix) ∧
      (primeHistoryTuple 1 state.selectedPrefix 0 : ℝ) ^ 3 <
        N ^ HistoricalThirdCoarse.initial (d.e : ℝ) := by
  obtain ⟨hs, hm⟩ := List.mem_filter.mp hs
  have ht := P1OriginalFirstStopInheritance.frontier_original_first_tests
    (d.e : ℝ) d.chi d.m d.omega N h carrier 2 (by omega) state hs
  exact ⟨firstExitDepthFrontier_selected_length 2 _ h [] carrier true 1
    (by simp) state hs, of_decide_eq_true hm, ht⟩

end
end ImbalancedChen.P5OriginalCommonFourthSourceNavigation
