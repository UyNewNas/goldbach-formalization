import ImbalancedChen.P4AOriginalElevenSixthStage
import ImbalancedChen.P4AOriginalNonsingletonComparison

/-! Each of the eight same-rank updates is evaluated on the actual fifth
frontier. The accepted finite branch and the raw fallback both read the
unrounded predecessor of the candidate's own stage. At step 8 the whole
policy is exactly the R17-corrected complete bank. -/
namespace ImbalancedChen.P4AOriginalLaterSixthStages
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (Accepted active afterLater level6Exponent fifthPolicy sixthPolicy)
open P4AOriginalSixthLaterLiteral (Cell stage)
open P4AOriginalSixthLaterSemantics (endpoint)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P1OriginalVariableFourthContinuation (finiteMax finiteMax_le finiteMax_row_le finiteMax_seed_le)
open P4AOriginalFull87RawChronology (rawRoot)

def licensed (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℕ → ℝ
  | 0 => P4AOriginalElevenSixthStage.level n d N h
  | k+1 => finiteMax Finset.univ
      (fun c : Cell => stage c=k ∧ Accepted n d N h (.later c))
      (fun c => (rounded n (endpoint c (primeHistoryLogCoordinates N 6 h)):ℝ))
      (licensed n d N h k)

def level (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) (k : ℕ) : ℝ :=
  if active d N h then licensed n d N h k else afterLater d N h k

def policy (k n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (fifthPolicy n d N)
    (frozenParityRosserPolicy false 6 (fun h => N^level n d N h k))

theorem licensed_mono (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    Monotone (licensed n d N h) := by
  apply monotone_nat_of_le_succ
  exact fun k => finiteMax_seed_le _ _ _ _

theorem level_zero (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level n d N h 0=P4AOriginalElevenSixthStage.level n d N h := by
  by_cases ha : active d N h
  · simp only [level,if_pos ha,licensed]
  · simp only [level,P4AOriginalElevenSixthStage.level,if_neg ha,afterLater]

theorem level_mono (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    Monotone (level n d N h) := by
  by_cases ha : active d N h
  · simpa only [level,if_pos ha] using licensed_mono n d N h
  · simpa only [level,if_neg ha] using P4AOriginalFull87DataPolicy.afterLater_mono d N h

theorem active_row (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) (c : Cell)
    (ha : active d N h) (hc : Accepted n d N h (.later c)) :
    (rounded n (endpoint c (primeHistoryLogCoordinates N 6 h)):ℝ) ≤ level n d N h (stage c+1) := by
  rw [level,if_pos ha,licensed]
  exact finiteMax_row_le _ _ _ _ c (Finset.mem_univ _) ⟨rfl,hc⟩

theorem level_eight (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level n d N h 8=level6Exponent n d N h := by
  by_cases ha : active d N h
  · have up (k : ℕ) : licensed n d N h k≤P4AOriginalFull87DataPolicy.licensedCap n d N h := by
      induction k with
      | zero => simpa only [licensed,level6Exponent,if_pos ha] using P4AOriginalElevenSixthStage.level_le_sixth n d N h
      | succ k ih =>
        apply finiteMax_le _ _ _ _ _ ih
        intro c _ hc
        exact finiteMax_row_le _ _ _ _ (.later c) (P4AOriginalSixthActionBank.mem_allActions _) hc.2
    rw [level,level6Exponent,if_pos ha]
    apply le_antisymm (up 8)
    have base := licensed_mono n d N h (show 0≤8 by omega)
    have first := P4AOriginalElevenSixthStage.saved_le_level n d N h
    apply finiteMax_le
    · have seed := P4AOriginalSavedSixthStage.fifth_le_level n d N h
      rw [P4AOriginalFull87DataPolicy.level5Exponent,
        P4AOriginalFull87DataPolicy.active_ancestor d N 5 (by decide),if_pos ha] at seed
      exact seed.trans (first.trans base)
    · intro a _ hh
      cases a with
      | saved i => exact (P4AOriginalSavedSixthStage.accepted_lower n d N h i ha hh).trans (first.trans base)
      | eleven c => exact (P4AOriginalElevenSixthStage.accepted_lower n d N h c ha hh).trans base
      | later c =>
        have h := active_row n d N h c ha hh
        rw [level,if_pos ha] at h
        exact h.trans (licensed_mono _ _ _ _ (Nat.succ_le_of_lt (P4AOriginalSixthLaterSemantics.original_stage_range c)))
  · simp only [level,level6Exponent,if_neg ha,P4AOriginalFull87DataPolicy.currentSixthExponent]

theorem policy_zero (n : ℕ) (d : OriginalData) (N : ℝ) :
    policy 0 n d N=P4AOriginalElevenSixthStage.policy n d N := by
  simp only [policy,P4AOriginalElevenSixthStage.policy,level_zero]
theorem policy_eight (n : ℕ) (d : OriginalData) (N : ℝ) :
    policy 8 n d N=sixthPolicy n d N := by
  simp only [policy,sixthPolicy,level_eight]
theorem even (k n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) : policy k n d N true h=true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (P4AOriginalFull87DataPolicy.fifth_even n d N) (fun p => frozenParityRosserPolicy_upper_even 6 _ p) h

def gain (k n : ℕ) (d : OriginalData) (N : ℕ) : ℝ :=
  rawRoot (policy k n d (N:ℝ)) N-rawRoot (policy (k+1) n d (N:ℝ)) N

theorem sum_gain (n : ℕ) (d : OriginalData) (N : ℕ) :
    (∑ k ∈ Finset.range 8,gain k n d N) = -P4AOriginalElevenSixthStage.remaining n d N := by
  have h (K : ℕ) : (∑ k ∈ Finset.range K,gain k n d N)=
      rawRoot (policy 0 n d (N:ℝ)) N - rawRoot (policy K n d (N:ℝ)) N := by
    induction K with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; unfold gain; ring
  rw [h,policy_zero,policy_eight,P4AOriginalElevenSixthStage.remaining]
  ring

end
end ImbalancedChen.P4AOriginalLaterSixthStages
