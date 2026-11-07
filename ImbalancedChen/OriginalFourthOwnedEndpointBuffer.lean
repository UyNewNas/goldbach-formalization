import ImbalancedChen.OriginalFourthPhysicalOwnedModulusSupport

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Actual original fourth buffer pays the complete endpoint vector. A single
rank bound R and width tau are fixed by tau*(R+1)<=e before the scale or
history varies. Every real retained history of rank four through R then
has full endpoint square support at its actual owned exponent plus e.
On a row-owned branch this is exactly the original pointwise M_I(t)-e:
one of the original two buffer losses remains after endpoint inflation.

No endpoint-square support or final factorization license is an input.
Inherited seed, overlapping max rows, occurrence priority and the physical
rough lower cutoff all remain the literal original source. The original
external distribution and archived chronological witnesses stay OPEN.
-/

namespace ImbalancedChen.OriginalFourthOwnedEndpointBuffer20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthSuccessorTransition20261026b
open OriginalFourthPhysicalOwnedModulusSupport20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
  (licensed : ProducerRow → Prop)

def ownedExponent (history : List ℕ) : ℝ :=
  exponent4 e chi m omega N (fourthFamily records) (producerEligible licensed)
    (fun r => r.bufferedCandidate e) (rosserAncestor 4 history)

theorem ownedExponent_eq_positional_value (history : List ℕ)
    (hlen : 4 ≤ history.length) :
    ownedExponent records e chi m omega N licensed history =
      slotValue records e (seedExponent e chi m omega N (rosserAncestor 4 history))
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))
        (ancestorOwner records e chi m omega N licensed history) := by
  have ha : (rosserAncestor 4 history).length = 4 := by
    rw [rosserAncestor_length]
    omega
  unfold ownedExponent exponent4
  rw [if_pos ha]
  exact (owner_value records e
    (seedExponent e chi m omega N (rosserAncestor 4 history)) licensed
    (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))).symm

/-- Uniform pre-scale buffer budget on all actual source histories up to
the specified rank. All original chronological slots are inflated. -/
theorem actual_uniform_endpoint_buffer
    (Nnat cap : ℕ) (hN : 1 < (Nnat : ℝ)) (w z tau : ℝ) (htau : 0 ≤ tau)
    (R : ℕ) (hwidth : tau * ((R : ℝ) + 1) ≤ e)
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank) (hR : rank ≤ R)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap w z))
    (upper : ℕ → ℕ)
    (hsize : ∀ p ∈ state.selectedPrefix.reverse,
      (upper p : ℝ) ≤ (Nnat : ℝ) ^ tau * (p : ℝ)) :
    actualDwellSupport
      ((Nnat : ℝ) ^ (ownedExponent records e chi m omega (Nnat : ℝ) licensed
        state.selectedPrefix + e)) (state.selectedPrefix.reverse.map upper) := by
  have hphysical := actual_owned_frontier_dwell records e chi m omega licensed
    Nnat cap hN.le w z weight rank hrank state hstate
  change actualDwellSupport
    ((Nnat : ℝ) ^ ownedExponent records e chi m omega (Nnat : ℝ) licensed
      state.selectedPrefix) state.selectedPrefix.reverse at hphysical
  have hlen : state.selectedPrefix.reverse.length ≤ R := by
    rw [List.length_reverse, firstExitDepthFrontier_selected_length rank
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] (roughPrimeUniverse Nnat cap w z) true 1 (by simp) state hstate]
    exact hR
  apply actualDwellSupport_upper_inflation hN htau id upper
    state.selectedPrefix.reverse hlen hsize
  · simpa using hphysical
  · linarith

/-- The attained raw row retains one full e buffer after uniform endpoint
inflation. The original owner, not a newly chosen endpoint maximizer,
identifies the row and its selected mask. -/
theorem actual_row_owned_endpoint_buffer
    (Nnat cap : ℕ) (hN : 1 < (Nnat : ℝ)) (w z tau : ℝ) (htau : 0 ≤ tau)
    (R : ℕ) (hwidth : tau * ((R : ℝ) + 1) ≤ e)
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank) (hR : rank ≤ R)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap w z))
    (i : Fin records.length)
    (howner : ancestorOwner records e chi m omega (Nnat : ℝ) licensed
      state.selectedPrefix = i.succ)
    (upper : ℕ → ℕ)
    (hsize : ∀ p ∈ state.selectedPrefix.reverse,
      (upper p : ℝ) ≤ (Nnat : ℝ) ^ tau * (p : ℝ)) :
    actualDwellSupport
      ((Nnat : ℝ) ^ ((rowAt records i).candidate
        (primeHistoryLogCoordinates (Nnat : ℝ) 4
          (rosserAncestor 4 state.selectedPrefix)) - e))
      (state.selectedPrefix.reverse.map upper) := by
  have hfull := actual_uniform_endpoint_buffer records e chi m omega licensed
    Nnat cap hN w z tau htau R hwidth weight rank hrank hR state hstate upper hsize
  have hlen := firstExitDepthFrontier_selected_length rank
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse Nnat cap w z) true 1 (by simp) state hstate
  have hexponent : ownedExponent records e chi m omega (Nnat : ℝ) licensed
      state.selectedPrefix + e = (rowAt records i).candidate
        (primeHistoryLogCoordinates (Nnat : ℝ) 4
          (rosserAncestor 4 state.selectedPrefix)) - e := by
    rw [ownedExponent_eq_positional_value records e chi m omega (Nnat : ℝ) licensed
      state.selectedPrefix (by omega), howner]
    simp only [slotValue, Fin.cases_succ, ProducerRow.bufferedCandidate]
    ring
  rwa [hexponent] at hfull

end
end ImbalancedChen.OriginalFourthOwnedEndpointBuffer20261026b
