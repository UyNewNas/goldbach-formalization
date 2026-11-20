import ImbalancedChen.OriginalFourthOwnedContinuationLicense

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Global causal history for the actual original fourth producer. The literal
root frontier factors through its own rank-four states as an ordered list,
with every state field and branch multiplicity preserved. Every returned
later state consequently has a real original ancestor, complete prefix
admissibility at that ancestor's attained Q, and its unchanged positional
owner. The actual target-deleted residual carrier is recovered as well.

This is a factorization of the original producer's real skip/select tree,
not an arbitrary relation closure. No parent history witness is assumed.
It is still one original transition, not a reconstruction of the absent
archived twenty-two-stage chronological source.
-/

namespace ImbalancedChen.OriginalFourthCausalFrontierFactorization20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthSuccessorTransition20261026b
open OriginalFourthOwnedContinuationLicense20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
  (licensed : ProducerRow → Prop)

/-- Ordered factorization of the actual producer recursion. Branches that
exhaust before four selections occur on neither side. No branch is added
by presuming that a new policy admits an old selected prefix. -/
theorem original_frontier_factorization (rank : ℕ) (hrank : 4 ≤ rank)
    (weight : ℕ → ℝ) (pre remaining : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier rank
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight pre positive mass remaining =
      (firstExitDepthFrontier 4
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight pre positive mass remaining).flatMap (fun state =>
          firstExitDepthFrontier rank
            (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
            weight state.selectedPrefix state.positive state.mass state.remaining) := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hfour : 4 ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length 4 _ weight pre [] positive mass hfour]
        simp only [List.flatMap_singleton]
      · have hstop : ¬ rank ≤ pre.length := by omega
        simp only [firstExitDepthFrontier, if_neg hfour, if_neg hstop, List.flatMap_nil]
  | cons p ps ih =>
      by_cases hfour : 4 ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length 4 _ weight pre (p :: ps) positive mass hfour]
        simp only [List.flatMap_singleton]
      · have hstop : ¬ rank ≤ pre.length := by omega
        simp only [firstExitDepthFrontier, if_neg hfour, if_neg hstop,
          List.flatMap_append]
        by_cases htest : producerPolicy4 e chi m omega N (fourthFamily records) licensed
            (!positive) (p :: pre) = true
        · simp only [if_pos htest]
          rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * weight p)]
        · simp only [if_neg htest, List.flatMap_nil, List.append_nil]
          exact ih pre positive mass

/-- Every global attained history has a literal inherited producer state.
The Q/owner license and the target-deleted carrier are both conclusions,
not independently chosen geometric or arithmetic inputs. -/
theorem actual_global_history_license
    (Nnat cap : ℕ) (hN : 1 ≤ (Nnat : ℝ)) (z : ℝ) (weight : ℕ → ℝ)
    (rank : ℕ) (hrank : 4 ≤ rank) (descendant : FirstExitDepthState ℕ)
    (hdesc : descendant ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap 0 z)) :
    ∃ ancestor ∈ firstExitDepthFrontier 4
        (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
        weight [] true 1 (roughPrimeUniverse Nnat cap 0 z),
      descendant ∈ firstExitDepthFrontier rank
        (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
        weight ancestor.selectedPrefix ancestor.positive ancestor.mass ancestor.remaining ∧
      producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          descendant.selectedPrefix =
        producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          ancestor.selectedPrefix ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          descendant.selectedPrefix) descendant.selectedPrefix ∧
      ancestorOwner records e chi m omega (Nnat : ℝ) licensed descendant.selectedPrefix =
        ancestorOwner records e chi m omega (Nnat : ℝ) licensed ancestor.selectedPrefix ∧
      descendant.positive = evenListLength descendant.selectedPrefix ∧
      descendant.mass = (descendant.selectedPrefix.map weight).prod ∧
      ∃ q tail, descendant.selectedPrefix = q :: tail ∧
        q ∈ roughPrimeUniverse Nnat cap 0 z ∧
        descendant.remaining = roughPrimeUniverse Nnat cap 0 (q : ℝ) := by
  have hfactor := hdesc
  rw [original_frontier_factorization records e chi m omega (Nnat : ℝ) licensed
    rank hrank weight [] (roughPrimeUniverse Nnat cap 0 z) true 1] at hfactor
  obtain ⟨ancestor, hancestor, hcontinuation⟩ := List.mem_flatMap.mp hfactor
  have hlicense := actual_owned_descendant_license records e chi m omega licensed
    Nnat cap hN z weight ancestor hancestor rank descendant hcontinuation
  have hmass := mem_firstExitDepthFrontier_mass_eq_selected_prod rank
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse Nnat cap 0 z) descendant hdesc
  have hcarrier := mem_firstExitDepthFrontier_roughPrime_remaining rank (by omega)
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight Nnat cap 0 z descendant hdesc
  exact ⟨ancestor, hancestor, hcontinuation, hlicense.1, hlicense.2.1,
    hlicense.2.2.1, hlicense.2.2.2, hmass, hcarrier⟩

end
end ImbalancedChen.OriginalFourthCausalFrontierFactorization20261026b
