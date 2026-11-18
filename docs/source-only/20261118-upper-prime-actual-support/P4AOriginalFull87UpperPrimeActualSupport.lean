import ImbalancedChen.P4AOriginalFull87StoppedGlobalPrimeLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An actual-support certificate for a NONZERO coefficient in the global
upper-half prime ledger, using the SAME sharedRankFour state List and
receiverTest-generated fifth/sixth event Lists.

The conclusion exhibits an actual fifthExclusive event, one of its original
sixth occurrences and the literal Rosser quotient. In particular, it
retains the strict power-filtered fifth-rank support
  X^5 < a^5 * selectedAfter.prod^6.
No use of smooth PP, invented geometric zero-error, or quantitative
smallness is made. This is a necessary condition, NOT an equivalence:
distinct signed occurrences may cancel even when witnesses exist.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperPrimeActualSupport
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedGlobalPrimeLedger
  (actualStoppedUpperPrimeCoefficient
   upperPrimeFibreEventValue upperPrimeFibreTerm)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87PlusBetaPowerFilter (largeFifthRosserIndices)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)

/-- Nonzero finite ordered List sum has an actual nonzero occurrence.
This does not pass to a Finset and cannot lose duplicate entries. -/
private theorem nonzero_map_sum_has_occurrence {α : Type*}
    (xs : List α) (f : α → ℝ)
    (h : (xs.map f).sum ≠ 0) :
    ∃ x ∈ xs, f x ≠ 0 := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      by_cases hx : f x = 0
      · have hrest : (xs.map f).sum ≠ 0 := by
          simpa [List.map_cons, List.sum_cons, hx] using h
        obtain ⟨y, hy, hnon⟩ := ih hrest
        exact ⟨y, by simp [hy], hnon⟩
      · exact ⟨x, by simp, hx⟩

/-- A nonzero global original P coefficient requires an ACTUAL admitted
fifthExclusive event and original sixth occurrence, not merely a
formal solution of a quotient equation.

The Rosser index a=(N-P)/b must be in the original plus-support and
must reproduce the complete modulus exactly, with b=(p::pre).prod.
Membership in the fifth-power filter gives the explicit strict
X^5 < a^5 * pre.prod^6. BOTH/sixthFromBoth cannot be witnesses to
this particular signed stopped coefficient, by its original valuation.
-/
theorem actual_upper_prime_nonzero_has_power_filtered_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X P : ℕ)
    (h : actualStoppedUpperPrimeCoefficient
      delta n e q om N cap w z L X P ≠ 0) :
    ∃ state : FirstExitDepthState ℕ,
      state ∈ sharedRankFour e q om N cap w z ∧
      ∃ fifth : FifthStoppedEvent ℕ,
        FifthSixthStoppedEvent.fifthExclusive fifth ∈
          actualFifthSixthWithoutBoth delta n e q om N cap w L X
            (receiverTest N) state ∧
        (fifth.kind = .rawOnly ∨ fifth.kind = .licensedOnly) ∧
        ∃ p : ℕ,
          p ∈ fifth.remainingAfter ∧
          2 * P < N ∧
          X < N - P ∧
          (N - P) / (p :: fifth.selectedAfter).prod ∈
            actualSmallRosserSupport N cap w ∧
          (N - P) / (p :: fifth.selectedAfter).prod ∈
            largeFifthRosserIndices N cap w X fifth.selectedAfter ∧
          ((N - P) / (p :: fifth.selectedAfter).prod) *
            (p :: fifth.selectedAfter).prod = N - P ∧
          X ^ 5 <
            ((N - P) / (p :: fifth.selectedAfter).prod) ^ 5 *
              fifth.selectedAfter.prod ^ 6 := by
  classical
  unfold actualStoppedUpperPrimeCoefficient at h
  obtain ⟨state, hstate, hstateNonzero⟩ :=
    nonzero_map_sum_has_occurrence
      (sharedRankFour e q om N cap w z)
      (fun state =>
        ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
          (receiverTest N) state).map
            (upperPrimeFibreEventValue N cap w L X P)).sum) h
  obtain ⟨ev, hev, hevNonzero⟩ :=
    nonzero_map_sum_has_occurrence
      (actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
      (upperPrimeFibreEventValue N cap w L X P) hstateNonzero
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [upperPrimeFibreEventValue] at hevNonzero
  | fifthExclusive fifth =>
      have hkind : fifth.kind = .rawOnly ∨
          fifth.kind = .licensedOnly := by
        cases hk : fifth.kind with
        | rawOnly => exact Or.inl hk
        | licensedOnly => exact Or.inr hk
        | both => simp [upperPrimeFibreEventValue, hk] at hevNonzero
      have hsum :
          (fifth.remainingAfter.map (fun p =>
            signedTreeCoefficient true fifth.massAfter *
              upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p)).sum ≠ 0 := by
        cases hk : fifth.kind with
        | rawOnly =>
            simpa [upperPrimeFibreEventValue, hk] using hevNonzero
        | licensedOnly =>
            simpa [upperPrimeFibreEventValue, hk] using hevNonzero
        | both =>
            simp [upperPrimeFibreEventValue, hk] at hevNonzero
      obtain ⟨p, hp, hpNonzero⟩ :=
        nonzero_map_sum_has_occurrence fifth.remainingAfter
          (fun p => signedTreeCoefficient true fifth.massAfter *
            upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p) hsum
      have hterm :
          upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p ≠ 0 := by
        intro hz
        apply hpNonzero
        simp [hz]
      have hgate :
          2 * P < N ∧ X < N - P ∧
          (N - P) / (p :: fifth.selectedAfter).prod ∈
            largeFifthRosserIndices N cap w X fifth.selectedAfter ∧
          ((N - P) / (p :: fifth.selectedAfter).prod) *
            (p :: fifth.selectedAfter).prod = N - P := by
        by_contra hnot
        apply hterm
        simp [upperPrimeFibreTerm, hnot]
      rcases hgate with ⟨hhalf, hX, hRosser, hfull⟩
      have hSmall :
          (N - P) / (p :: fifth.selectedAfter).prod ∈
            actualSmallRosserSupport N cap w :=
        (Finset.mem_filter.mp hRosser).1
      have hPower :
          X ^ 5 <
            ((N - P) / (p :: fifth.selectedAfter).prod) ^ 5 *
              fifth.selectedAfter.prod ^ 6 :=
        (Finset.mem_filter.mp hRosser).2
      exact ⟨state, hstate, fifth, hev, hkind, p, hp,
        hhalf, hX, hSmall, hRosser, hfull, hPower⟩

end
end ImbalancedChen.P4AOriginalFull87UpperPrimeActualSupport
