import ImbalancedChen.P2Saving16NegativeOriginalFibreSum
import ImbalancedChen.P2OriginalFourteenSignedParentLedger
import ImbalancedChen.P1Pair12RetainedSignedSource
import ImbalancedChen.FirstExitFrontierInvariants

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Reindex the original fourteen-policy signed physical source at positive-w
by its literal ordered eighth frontier. The original parent, the full
remaining carrier and the sign-selected beta test are preserved. No
identity with a compiler correction or geometric-corner coefficient is
asserted. -/
namespace ImbalancedChen.P2Saving16OriginalPhysicalEightSource
noncomputable section
open scoped Classical BigOperators
open Set
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor
open P2OriginalAscendingEighthCapDictionary
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16NegativeOriginalFibreSum P2Saving16SameRhoDistributionFrontier
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)

/-- The original eighth policy on the actual six-parent of this data. -/
def originalPolicy (data : OriginalData) (N : ℕ) : Bool → List ℕ → Bool :=
  P2OriginalFourteenSignedParentLedger.policy (N : ℝ) (lambda6 data (N : ℝ))
    P4AOriginalAscending14Literal42.literalPattern (policy5 data (N : ℝ))

def originalContinuation (data : OriginalData) (N : ℕ) : Bool → List ℕ → Bool :=
  frozenParityRosserPolicy false 8
    (familyNextLevel (N : ℝ) (lambda6 data (N : ℝ))
      P4AOriginalAscending14Literal42.literalPattern)

/-- Actual new-minus-parent continuation at the original ordered tuple.
The full beta test remains inside both signed trees. -/
def originalTupleTerm (data : OriginalData) (N cap : ℕ) (w z L : ℝ)
    (G : ℕ → ℝ) (p : Fin 8 → ℕ) : ℝ :=
  let pre := (List.ofFn p).reverse
  let remaining := roughPrimeUniverse N cap w (pre.getD 0 0 : ℝ)
  signedTest (originalContinuation data N) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) pre true 1 remaining -
  signedTest (policy6 data (N : ℝ)) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) pre true 1 remaining

def originalFrontierSource (data : OriginalData) (N cap : ℕ) (w z L : ℝ)
    (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 8 (policy6 data (N : ℝ)) (fun _ : ℕ => 1)
    [] true 1 (roughPrimeUniverse N cap w z)).map (fun s =>
      signedTest (originalContinuation data N) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining -
      signedTest (policy6 data (N : ℝ)) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining)).sum

/-- Unit-mass rank eight has the actual positive incoming sign, not an
assumed positive sign for the later terminal branches. -/
theorem original_state_term_eq_tuple (data : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8 (policy6 data (N : ℝ)) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)) :
    signedTest (originalContinuation data N) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining -
      signedTest (policy6 data (N : ℝ)) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining =
      originalTupleTerm data N cap w z L G (primeHistoryTuple 8 s.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 8 (policy6 data (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) [] (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
  have hmass : s.mass = 1 := by
    simpa using mem_firstExitDepthFrontier_mass_eq_selected_prod 8
      (policy6 data (N : ℝ)) (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) s hs
  have hp := mem_firstExitDepthFrontier_positive_eq_evenListLength 8
    (policy6 data (N : ℝ)) (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) s hs
  have hsign : signedTreeCoefficient s.positive s.mass = 1 := by
    rw [hp, hmass, signedTreeCoefficient_evenListLength_eq_negOnePow, hlen]
    norm_num
  have hpos : s.positive = true := by
    cases h : s.positive with
    | false => norm_num [h, hmass, signedTreeCoefficient] at hsign
    | true => rfl
  obtain ⟨p, tail, hpre, _, hrem⟩ := mem_firstExitDepthFrontier_roughPrime_remaining
    8 (by decide) (policy6 data (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
    N cap w z s hs
  unfold originalTupleTerm
  rw [primeHistoryTuple_reverse_ofFn hlen, hpos, hmass, hrem, hpre]
  rfl

/-- Original ordered frontier occurrences do not repeat. -/
theorem original_eight_occurrences_nodup (data : OriginalData) (N cap : ℕ) (w z : ℝ) :
    ((firstExitDepthFrontier 8 (policy6 data (N : ℝ)) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)).map
        (fun s => primeHistoryTuple 8 s.selectedPrefix)).Nodup :=
  firstExitRootFrontier_admitted_tuple_nodup 8 (policy6 data (N : ℝ))
    (fun _ : ℕ => 1) (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)

/-- Exact reindexing of all original full-q continuation tests. -/
theorem original_frontier_eq_tuple_sum (data : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    originalFrontierSource data N cap w z L G =
      ∑ p ∈ firstExitAdmittedTuples 8 (policy6 data (N : ℝ)) (roughPrimeUniverse N cap w z),
        originalTupleTerm data N cap w z L G p := by
  have h := firstExitRootFrontier_sum_eq_admitted_tuple_sum 8 (policy6 data (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_nodup N cap w z) (originalTupleTerm data N cap w z L G)
  rw [← h]
  unfold originalFrontierSource
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact original_state_term_eq_tuple data N cap w z L G s hs

/-- This is one exact source identity for the actual old and new trees,
with a shared full-modulus arithmetic test, not a subtraction of bounds. -/
theorem original_physical_change_eq_tuple_sum
    (data : OriginalData) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ actualSmallRoughModuli (originalPolicy data N false) N cap w z,
      actualSmallRoughRho (originalPolicy data N false) N cap w z L m * G m) -
    (∑ m ∈ actualSmallRoughModuli (policy6 data (N : ℝ) false) N cap w z,
      actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L m * G m) =
      ∑ p ∈ firstExitAdmittedTuples 8 (policy6 data (N : ℝ)) (roughPrimeUniverse N cap w z),
        originalTupleTerm data N cap w z L G p := by
  have hparent := policy6_even data (N : ℝ)
  have hnew := P2OriginalFourteenSignedParentLedger.policy_even (N : ℝ)
    (lambda6 data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
    (policy5 data (N : ℝ)) (policy5_even data (N : ℝ))
  have hn := physical_test_eq_signedTest (originalPolicy data N) hnew N cap 1 w z L G
  have ho := physical_test_eq_signedTest (policy6 data (N : ℝ)) hparent N cap 1 w z L G
  simp only [one_mul] at hn ho
  have hs := signedTest_splice_sub_eq_frontier 8 (policy6 data (N : ℝ))
    (originalContinuation data N) (fun _ : ℕ => 1) (attachedLeafTest N cap 1 w L G)
    [] (roughPrimeUniverse N cap w z) true 1
  change signedTest (originalPolicy data N) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      [] true 1 (roughPrimeUniverse N cap w z) -
    signedTest (policy6 data (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      [] true 1 (roughPrimeUniverse N cap w z) = originalFrontierSource data N cap w z L G at hs
  rw [← hn, ← ho, original_frontier_eq_tuple_sum] at hs
  exact hs

/-- The original term can be put on the compiler's complete Q without
changing its signed coefficient or the full-modulus test. -/
theorem original_rho_sum_on_complete_Q (ret : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ support N cap w z, actualSmallRoughRho ret N cap w z L m * G m) =
      ∑ m ∈ actualSmallRoughModuli ret N cap w z,
        actualSmallRoughRho ret N cap w z L m * G m := by
  have h := sum_smallRoughRho_mul_eq_of_rough_enlargement
    (actualSmallRosserSupport N cap w) (rawSupport_subset_universe ret N cap w z)
    (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
    (fun d _ hnot => by rw [raw_value, if_neg hnot]) G
  change (∑ m ∈ support N cap w z,
    smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
      (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) m * G m) =
    (∑ m ∈ actualSmallRoughModuli ret N cap w z,
      actualSmallRoughRho ret N cap w z L m * G m) at h
  rw [raw_attachment_eq_actual ret N cap w z L] at h
  exact h

/-- Original fourteen change and its ordered occurrence list on the same Q,
with the actual beta attachment and arbitrary full-q test. -/
theorem original_physical_change_on_same_Q
    (data : OriginalData) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ support N cap w z,
      (actualSmallRoughRho (originalPolicy data N false) N cap w z L m -
        actualSmallRoughRho (policy6 data (N : ℝ) false) N cap w z L m) * G m) =
      ∑ p ∈ firstExitAdmittedTuples 8 (policy6 data (N : ℝ)) (roughPrimeUniverse N cap w z),
        originalTupleTerm data N cap w z L G p := by
  have h := original_physical_change_eq_tuple_sum data N cap w z L G
  rw [← original_rho_sum_on_complete_Q (originalPolicy data N false) N cap w z L G,
    ← original_rho_sum_on_complete_Q (policy6 data (N : ℝ) false) N cap w z L G] at h
  simpa only [sub_mul, Finset.sum_sub_distrib] using h


/-- At one scheduled original cell, the selected compiler eight-prefixes
index literal original-parent signed continuations. The remaining original
source tuples and all full-q fibre occurrences stay in their own sums.
This supplies both expressions on the same key, without asserting their
individual coefficients or weights are equal. -/
theorem scheduled_original_source_and_compiler_fibres (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        q0 ≤ q → a ≤ 1 / 100 → nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) (b T : ℝ),
          let bank := P4AOriginalFull87UnionHistory.bank e q a
          let omega := nu * beta^2
          let w := (N : ℝ)^omega
          let z := P4AOriginalFull87RawChronology.cutoff N
          let L := (N : ℝ)^(nu*beta)
          let Q := moduli N w
          let f := keep r n e q a omega N
          let G := realHalfProductDiscrepancy b N T
          let A := firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z)
          let B := tuples f (fun _ => []) N N w z tau (width r) i
          B ⊆ A ∧
          (∑ m ∈ Q,
            (actualSmallRoughRho (originalPolicy bank N false) N N w z L m -
              actualSmallRoughRho (policy6 bank (N : ℝ) false) N N w z L m) * G m) =
            (∑ p ∈ B, originalTupleTerm bank N N w z L G p) +
              (∑ p ∈ A.filter (fun p => p ∉ B), originalTupleTerm bank N N w z L G p) ∧
          (∑ p ∈ B, fibreSum f (fun _ => []) N N w z tau (width r) L i G p) =
            selectedSum f (fun _ => []) N N w z tau (width r) L i G := by
  obtain ⟨e0, he0, h⟩ := tuples_are_scheduled_original_fourths r
  refine ⟨e0, he0, ?_⟩
  intro e he he0e
  obtain ⟨q0, hq0⟩ := h e he he0e
  refine ⟨q0, ?_⟩
  intro n q a nu beta tau hq ha hcut hh N hN i b T
  let bank := P4AOriginalFull87UnionHistory.bank e q a
  let w := (N : ℝ)^(nu*beta^2)
  let z := P4AOriginalFull87RawChronology.cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a (nu*beta^2) N
  let G := realHalfProductDiscrepancy b N T
  let A := firstExitAdmittedTuples 8 (policy6 bank (N : ℝ)) (roughPrimeUniverse N N w z)
  let B := tuples f (fun _ => []) N N w z tau (width r) i
  have hsub : B ⊆ A := by
    intro p hp
    exact (hq0 n q a nu beta tau hq ha hcut hh N hN i p hp).1
  have hfilter : A.filter (fun p => p ∈ B) = B := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => hp.2, fun hp => ⟨hsub hp, hp⟩⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun p => p ∈ B)
    (originalTupleTerm bank N N w z L G)
  rw [hfilter] at hsplit
  have hsource := original_physical_change_on_same_Q bank N N w z L G
  rw [← hsplit] at hsource
  refine ⟨hsub, ?_, ?_⟩
  · exact hsource
  · exact (selectedSum_eq_ordered_eight_fibres f (fun _ => []) N N w z tau (width r) L i G).symm

end
end ImbalancedChen.P2Saving16OriginalPhysicalEightSource
