import ImbalancedChen.OriginalFourthFrozenAtomCap
import ImbalancedChen.P1OriginalVariableFourthFullSourceActivation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

The constant analytic cap is bound to an ACTUAL original descendant,
including its literal raw-Q3 seed. The finite activation/third-cell label
determines that seed; it is not supplied as a desired equality. The full
original chronological vector, including every tail slot, obtains square
support at the constant cap after spending at most e/2 in endpoint width.

The endpoint inflation inequality here is the elementary input removed by
the subsequent uniform canonical-mesh realization. No square support,
rank bound, archived chronology or distribution conclusion is assumed.
-/

namespace ImbalancedChen.OriginalFourthActualAtomEndpointSupport20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse VariableEnvelope P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthEligibilityPartition
open OriginalFourthOwnedEndpointBuffer20261026b
open OriginalFourthUniformIntegerMeshRealization20261026b
open OriginalFourthPhysicalOwnedModulusSupport20261026b
open OriginalFourthFrozenAtomCap20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- Literal finite source labels, including inactive and active but
unselected third parents, identify the real inherited seed of this history. -/
theorem owned_exponent_on_source_branch (N : ℕ) (hN : 1 < N)
    (history : List ℕ) (hlen : 4 ≤ history.length)
    (hp : ∀ i, 0 < primeHistoryTuple 4 (rosserAncestor 4 history) i)
    (label : Label m)
    (hbranch : primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 history) ∈
      meshBranch m omega label) :
    ownedExponent records e chi m omega (N : ℝ) licensed history =
      producerProfile4 e (fourthFamily records) licensed (branchSeed e chi m label)
        (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 history)) := by
  have ha : (rosserAncestor 4 history).length = 4 := by
    rw [rosserAncestor_length]
    omega
  have htuple := tupleHistory_primeHistoryTuple (rosserAncestor 4 history) ha
  have hseed := seedExponent_on_meshBranch e chi m omega label N hN
    (primeHistoryTuple 4 (rosserAncestor 4 history)) hp
    (show actualPrimeTupleLog N (primeHistoryTuple 4 (rosserAncestor 4 history)) ∈
      meshBranch m omega label from hbranch)
  rw [htuple] at hseed
  unfold ownedExponent exponent4
  rw [if_pos ha, hseed]
  rfl

/-- Positivity of the actual ancestor tuple is derived from the original
physical source. No unrelated tuple is substituted for this state. -/
theorem actual_ancestor_tuple_positive (N cap : ℕ) (w z : ℝ)
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ∀ i, 0 < primeHistoryTuple 4 (rosserAncestor 4 state.selectedPrefix) i := by
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  intro i
  rw [primeHistoryTuple_ancestor hlen hrank i]
  exact (mem_roughPrimeUniverse_prime (hsub.subset
    (List.mem_reverse.mpr (primeHistoryTuple_mem hlen (i.castLE hrank))))).pos

/-- Every original prefix-square test, not only the total product or the
first four slots, is paid at the same finite analytic cap. The rank is a
conclusion of original roughness and the actual policy ceiling. -/
theorem actual_full_vector_at_frozen_cap (he : 0 ≤ e) (rho : ℝ) (hrho : 0 < rho)
    (N cap : ℕ) (hN : 1 < N) (w z tau : ℝ)
    (hrough : (N : ℝ) ^ rho ≤ w) (htau : 0 ≤ tau)
    (hwidth : tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ e / 2)
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (label : Label m) (s : Pattern (fourthFamily records)) (corner : Point)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ e / 24)
    (hbranch : primeHistoryLogCoordinates (N : ℝ) 4
      (rosserAncestor 4 state.selectedPrefix) ∈ meshBranch m omega label)
    (hatom : primeHistoryLogCoordinates (N : ℝ) 4
      (rosserAncestor 4 state.selectedPrefix) ∈ wallAtom (fourthFamily records) s)
    (hcoord : ∀ i, |primeHistoryLogCoordinates (N : ℝ) 4
      (rosserAncestor 4 state.selectedPrefix) i - corner i| ≤ delta)
    (upper : ℕ → ℕ)
    (hsize : ∀ p ∈ state.selectedPrefix.reverse,
      (upper p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ)) :
    actualDwellSupport
      ((N : ℝ) ^ frozenAtomCap e (branchSeed e chi m label)
        (fourthFamily records) licensed s corner delta)
      (state.selectedPrefix.reverse.map upper) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hbound := actual_original_rank_bound records e chi m omega licensed he
    rho hrho N cap hNr w z hrough weight rank hrank state hstate
  have hp := actual_ancestor_tuple_positive records e chi m omega licensed
    N cap w z weight rank hrank state hstate
  have hprofile := owned_exponent_on_source_branch records e chi m omega licensed
    N hN state.selectedPrefix (by omega) hp label hbranch
  have hcap := (actual_profile_frozen_cap_bracket e (branchSeed e chi m label)
    (fourthFamily records) licensed s corner
    (primeHistoryLogCoordinates (N : ℝ) 4 (rosserAncestor 4 state.selectedPrefix))
    delta hdelta hsmall hatom hcoord).1
  rw [← hprofile] at hcap
  have hphysical := actual_owned_frontier_dwell records e chi m omega licensed
    N cap hNr.le w z weight rank hrank state hstate
  change actualDwellSupport
    ((N : ℝ) ^ ownedExponent records e chi m omega (N : ℝ) licensed
      state.selectedPrefix) state.selectedPrefix.reverse at hphysical
  apply actualDwellSupport_upper_inflation hNr htau id upper
    state.selectedPrefix.reverse
    (by simpa only [List.length_reverse, hlen] using hbound) hsize
  · simpa using hphysical
  · linarith

end
end ImbalancedChen.OriginalFourthActualAtomEndpointSupport20261026b
