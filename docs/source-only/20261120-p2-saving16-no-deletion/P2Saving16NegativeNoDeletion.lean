import ImbalancedChen.P2Saving16NegativeCoefficientComparison
import ImbalancedChen.P2Saving16SignedCorrectionFamilies

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The original fourteen continuation only enlarges its own sixth parent.
The statement is about the literal signed full-q coefficient, and makes
no assertion that a selected compiler occurrence actually exists. -/
namespace ImbalancedChen.P2Saving16NegativeNoDeletion
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P2OriginalAscendingEighthCapDictionary
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16NegativeCoefficientComparison P2Saving16NegativeOriginalFibreSum
open P2Saving16OriginalPhysicalEightSource P2Saving16SignedCorrectionFamilies
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalOrderedThirdActualCoefficient (keep)

/-- The very same ancestor is evaluated at the two levels. -/
theorem frozen_upper_increases (old fresh : List ℕ → ℝ)
    (hlevel : ∀ pre, old pre ≤ fresh pre) (b : Bool) (pre : List ℕ)
    (h : frozenParityRosserPolicy false 8 old b pre = true) :
    frozenParityRosserPolicy false 8 fresh b pre = true := by
  cases b with
  | true => simp
  | false =>
      have ho : ordinaryRosserPrefixAdmissible false (old (rosserAncestor 8 pre)) pre := by
        simpa [frozenParityRosserPolicy, ancestorFrozenPolicy,
          ordinaryParityRosserPolicy, oddFirstExitPolicy] using h
      have hn := ordinaryRosserPrefixAdmissible_mono false pre
        (hlevel (rosserAncestor 8 pre)) ho
      simpa [frozenParityRosserPolicy, ancestorFrozenPolicy,
        ordinaryParityRosserPolicy, oddFirstExitPolicy] using hn

/-- No old decision is deleted by the actual fourteen continuation.
This includes the original parent tests through rank eight. -/
theorem original_policy_increases (data : OriginalData) (N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (b : Bool) (pre : List ℕ)
    (h : policy6 data (N : ℝ) b pre = true) :
    originalPolicy data N b pre = true := by
  have heq : firstExitDepthSplicePolicy 8 (policy6 data (N : ℝ))
      (frozenParityRosserPolicy false 8 (currentLevel (N : ℝ) (lambda6 data (N : ℝ)))) =
        policy6 data (N : ℝ) := by
    exact P2OriginalFourteenSignedParentLedger.old_refreeze_eq_parent
      (N : ℝ) (lambda6 data (N : ℝ)) (policy5 data (N : ℝ))
  have hold : firstExitDepthSplicePolicy 8 (policy6 data (N : ℝ))
      (frozenParityRosserPolicy false 8 (currentLevel (N : ℝ) (lambda6 data (N : ℝ)))) b pre = true := by
    rw [heq]
    exact h
  change firstExitDepthSplicePolicy 8 (policy6 data (N : ℝ))
    (frozenParityRosserPolicy false 8
      (familyNextLevel (N : ℝ) (lambda6 data (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern)) b pre = true
  by_cases hk : pre.length ≤ 8
  · simpa [firstExitDepthSplicePolicy, hk] using hold
  · simp only [firstExitDepthSplicePolicy, if_neg hk] at hold ⊢
    exact frozen_upper_increases _ _
      (fun p => currentLevel_le_familyNext (N : ℝ) hN (lambda6 data (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern p) b pre hold

/-- Every old leaf itself survives, including its selected word and mass. -/
theorem retained_leaves_increase {α : Type*} (old fresh : Bool → List α → Bool)
    (hpolicy : ∀ b pre, old b pre = true → fresh b pre = true)
    (weight : α → ℝ) : ∀ (remaining pre : List α) (b : Bool) (mass : ℝ),
      firstExitRetainedLeaves old weight pre b mass remaining ⊆
        firstExitRetainedLeaves fresh weight pre b mass remaining := by
  intro remaining
  induction remaining with
  | nil =>
      intro pre b mass leaf hleaf
      simpa [firstExitRetainedLeaves] using hleaf
  | cons p ps ih =>
      intro pre b mass leaf hleaf
      rw [firstExitRetainedLeaves, List.mem_append] at hleaf
      rw [firstExitRetainedLeaves, List.mem_append]
      rcases hleaf with hskip | hselect
      · exact Or.inl (ih pre b mass hskip)
      · by_cases hp : old (!b) (p :: pre) = true
        · rw [if_pos hp] at hselect
          have hf := hpolicy (!b) (p :: pre) hp
          refine Or.inr ?_
          rw [if_pos hf]
          exact ih (p :: pre) (!b) (mass * weight p) hselect
        · simp [hp] at hselect

/-- The support inclusion follows from a map of actual retained leaves,
not from an equality of unweighted geometric cells. -/
theorem original_raw_support_increases (data : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z : ℝ) :
    rawSupport (policy6 data (N : ℝ) false) N cap w z ⊆
      rawSupport (originalPolicy data N false) N cap w z := by
  intro d hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (raw_support_iff_ordered_leaf (policy6 data (N : ℝ) false) N cap w z d).mp hd
  have hpol : ∀ b pre,
      oddFirstExitPolicy (policy6 data (N : ℝ) false) b pre = true →
        oddFirstExitPolicy (originalPolicy data N false) b pre = true := by
    intro b pre hb
    cases b with
    | true => simp [oddFirstExitPolicy]
    | false =>
        have hp : policy6 data (N : ℝ) false pre = true := by
          simpa [oddFirstExitPolicy] using hb
        simpa [oddFirstExitPolicy] using original_policy_increases data N hN false pre hp
  have hleaf' : leaf ∈ oddFirstExitRetainedLeaves (originalPolicy data N false)
      (fun _ => 1) (roughPrimeUniverse N cap w z) := by
    exact retained_leaves_increase _ _ hpol (fun _ => 1)
      (roughPrimeUniverse N cap w z) [] true 1 hleaf
  exact (raw_support_iff_ordered_leaf (originalPolicy data N false) N cap w z d).mpr
    ⟨leaf, hleaf', hprod⟩

/-- Only additions are possible; zero is retained for unchanged words. -/
theorem original_switch_only_additions (data : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (w z : ℝ) (d : ℕ) :
    originalSwitch (policy6 data (N : ℝ) false) (originalPolicy data N false) N cap w z d =
      if d ∈ rawSupport (originalPolicy data N false) N cap w z ∧
          d ∉ rawSupport (policy6 data (N : ℝ) false) N cap w z then -1 else 0 := by
  have hs := original_raw_support_increases data N cap hN w z
  unfold originalSwitch
  by_cases ho : d ∈ rawSupport (policy6 data (N : ℝ) false) N cap w z
  · have hf := hs ho
    simp [ho, hf]
  · by_cases hf : d ∈ rawSupport (originalPolicy data N false) N cap w z <;>
      simp [ho, hf]

/-- On a selected negative-inner occurrence, literal agreement with the
original new-minus-parent coefficient requires precisely a zero weighted
beta-minus term. No nonvanishing or occurrence is asserted. -/
theorem selected_match_iff_beta_discrepancy_zero
    (data : OriginalData) (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z tau delta L : ℝ)
    (i : Fin 14) (G : ℕ → ℝ) {x : ℕ × ℕ}
    (hx : x ∈ selected ret tag N cap w z tau delta i) :
    ((actualSmallRoughRho (originalPolicy data N false) N cap w z L (x.1*x.2) -
      actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L (x.1*x.2)) * G (x.1*x.2) =
      (rho ret tag N cap w z tau L (x.1*x.2) -
        actualSmallRoughRho ret N cap w z L (x.1*x.2)) * G (x.1*x.2)) ↔
      actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) = 0 := by
  constructor
  · intro heq
    by_contra hn
    have hdelete := (selected_match_iff_original_delete
      (policy6 data (N : ℝ) false) (originalPolicy data N false)
      ret tag N cap w z tau delta L i G hx hn).mp heq
    exact hdelete.2 (original_raw_support_increases data N cap hN w z hdelete.1)
  · intro hz
    have hc := selected_original_and_compiler_coefficients
      (policy6 data (N : ℝ) false) (originalPolicy data N false)
      ret tag N cap w z tau delta L i G hx
    rw [hc.2.1, hc.2.2, mul_assoc, hz]
    simp

/-- The exact remaining gap is -2 beta-minus G on fresh-only words,
and -beta-minus G on unchanged words, at the identical product s*d. -/
theorem selected_original_minus_compiler_no_deletion
    (data : OriginalData) (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z tau delta L : ℝ)
    (i : Fin 14) (G : ℕ → ℝ) :
    (∑ x ∈ selected ret tag N cap w z tau delta i,
      (actualSmallRoughRho (originalPolicy data N false) N cap w z L (x.1*x.2) -
        actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L (x.1*x.2)) * G (x.1*x.2)) -
      selectedSum ret tag N cap w z tau delta L i G =
    ∑ x ∈ selected ret tag N cap w z tau delta i,
      (if x.2 ∈ rawSupport (originalPolicy data N false) N cap w z ∧
          x.2 ∉ rawSupport (policy6 data (N : ℝ) false) N cap w z then (-2 : ℝ) else -1) *
        actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) := by
  rw [selected_original_minus_compiler_gap]
  apply Finset.sum_congr rfl
  intro x hx
  rw [original_switch_only_additions data N cap hN w z x.2]
  split_ifs <;> ring

/-- The same real half-product discrepancy, union bank, positive-w
scales and selected pair occurrences used by the existing compiler. -/
theorem actual_bank_negative_gap_no_deletion
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (N : ℕ) (hN : 1 ≤ (N : ℝ)) (i : Fin 14) (b T : ℝ) :
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    let old := policy6 bank (N : ℝ) false
    let fresh := originalPolicy bank N false
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ)^(nu*beta)
    let ret := keep r n e q a omega N
    let G := P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T
    (∑ x ∈ selected ret (fun _ => []) N N w z tau (width r) i,
      (actualSmallRoughRho fresh N N w z L (x.1*x.2) -
        actualSmallRoughRho old N N w z L (x.1*x.2)) * G (x.1*x.2)) -
      selectedSum ret (fun _ => []) N N w z tau (width r) L i G =
    ∑ x ∈ selected ret (fun _ => []) N N w z tau (width r) i,
      (if x.2 ∈ rawSupport fresh N N w z ∧ x.2 ∉ rawSupport old N N w z
        then (-2 : ℝ) else -1) * actualSmallRosserMinus N N w L x.1 * G (x.1*x.2) := by
  exact selected_original_minus_compiler_no_deletion
    (P4AOriginalFull87UnionHistory.bank e q a)
    (keep r n e q a (nu * beta^2) N) (fun _ => []) N N hN
    ((N : ℝ)^(nu*beta^2)) (P4AOriginalFull87RawChronology.cutoff N)
    tau (width r) ((N : ℝ)^(nu*beta)) i
    (P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T)

end
end ImbalancedChen.P2Saving16NegativeNoDeletion
