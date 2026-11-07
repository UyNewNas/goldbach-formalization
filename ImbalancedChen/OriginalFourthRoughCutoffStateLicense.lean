import ImbalancedChen.OriginalFourthCausalFrontierFactorization
import ImbalancedChen.Part3ActualAttachedRoughFrontier

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Actual original owned-Q history under the physical rough lower cutoff.
The inclusive cutoff is a literal filter of the target-deleted full prime
carrier. A retained selected history on that filtered carrier remains a
valid history of the very same original producer. Its complete owned-Q
license is recovered from a genuine full-carrier frontier witness. This
does not equate the two remaining carriers: skipped small primes really
remain deleted on the physical rough side.

The native policy and all its source-history dependence are retained.
No independent beta, hypothetical inherited validity or raw archive
chronological witness is introduced.
-/

namespace ImbalancedChen.OriginalFourthRoughCutoffStateLicense20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthCausalFrontierFactorization20261026b
open Part3.ActualAttachedRoughFrontier

/-- Exact inclusive lower cutoff, with both target deletion and the
enumeration cap retained. No rounding of a real cutoff is used. -/
theorem roughPrimeUniverse_filter_lower (N cap : ℕ) (w z : ℝ) :
    (roughPrimeUniverse N cap 0 z).filter (fun p => w ≤ (p : ℝ)) =
      roughPrimeUniverse N cap w z := by
  have hgt := (roughPrimeUniverse_pairwise_gt N cap 0 z).filter
    (fun p => w ≤ (p : ℝ))
  have hset : ((roughPrimeUniverse N cap 0 z).filter
      (fun p => w ≤ (p : ℝ))).toFinset = roughPrimeFinset N cap w z := by
    ext p
    simp only [List.mem_toFinset, List.mem_filter, mem_roughPrimeUniverse,
      decide_eq_true_eq, mem_roughPrimeFinset]
    constructor
    · rintro ⟨hp, hw⟩
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hw, hp.2.2.2.2⟩
    · intro hp
      exact ⟨⟨hp.1, hp.2.1, hp.2.2.1, Nat.cast_nonneg p, hp.2.2.2.2⟩,
        hp.2.2.2.1⟩
  change _ = (roughPrimeFinset N cap w z).sort (· ≥ ·)
  rw [← hset]
  exact ((List.toFinset_sort (r := (· ≥ ·)) hgt.nodup).mpr
    (hgt.imp fun h => h.le)).symm

theorem roughPrimeUniverse_lower_sublist (N cap : ℕ) (w z : ℝ) :
    roughPrimeUniverse N cap w z <+ roughPrimeUniverse N cap 0 z := by
  rw [← roughPrimeUniverse_filter_lower N cap w z]
  exact List.filter_sublist

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- Genuine physical rough states receive the sharp original dynamic cap
license. A full-carrier state with the same selected history is constructed
from valid selection, rather than presumed from geometric membership. -/
theorem actual_rough_frontier_owned_admissible
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z : ℝ) (weight : ℕ → ℝ)
    (rank : ℕ) (hrank : 4 ≤ rank) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
        state.selectedPrefix) state.selectedPrefix := by
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hleaf := firstExitDepthFrontier_toLeaf_mem rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap w z) true 1 state hstate
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] (roughPrimeUniverse N cap w z) true 1
      { selected := state.selectedPrefix, positive := state.positive, mass := state.mass } hleaf
  change state.selectedPrefix = chosen.reverse ++ [] at hselected
  have hchosenLen : chosen.length = rank := by
    have hs := congrArg List.length hselected
    simp only [List.length_append, List.length_reverse, List.length_nil, add_zero] at hs
    omega
  have hfullSub : chosen <+ roughPrimeUniverse N cap 0 z :=
    hsub.trans (roughPrimeUniverse_lower_sublist N cap w z)
  obtain ⟨fullState, hfullRaw, hfullSelected⟩ := valid_selection_frontier_witness
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight hfullSub [] true 1 hvalid
  have hfull : fullState ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap 0 z) := by
    simpa only [List.length_nil, zero_add, hchosenLen] using hfullRaw
  have hsame : fullState.selectedPrefix = state.selectedPrefix :=
    hfullSelected.trans hselected.symm
  obtain ⟨_ancestor, _hancestor, _hcontinuation, _hQ, hadmissible,
    _howner, _hsign, _hmass, _hcarrier⟩ :=
    actual_global_history_license records e chi m omega licensed N cap hN z weight
      rank hrank fullState hfull
  rwa [hsame] at hadmissible

end
end ImbalancedChen.OriginalFourthRoughCutoffStateLicense20261026b
