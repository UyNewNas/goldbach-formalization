import ImbalancedChen.P1CommonSixthCompactActualCaller

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original non-tent compact source cell is itself an attained winner of
the ACTUAL all-eleven finite maximum. This is stronger than being eligible.
The nine clipped rows have the same value; each eligible tent row
is below that value by its own literal priority guard and eta > 0.
No choice of an unrelated winner/mask, and no replacement policy, occurs.

The two tent source cells are deliberately not covered by this theorem.
Their eligibility alone does not bound a competing clipped winner by the
tent value, or transfer the source tent's compact margins to its mask.
-/

namespace ImbalancedChen.P1OriginalClippedSixthAttainedWinner

noncomputable section
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1CommonSixthCompactActualCaller
open P2CompactThirdHistorySelection P2OriginalSixthCommonScheduleAndFullQ
open P2OriginalSixthCompactArithmeticFibre P2OriginalFourthCapProducerInterface
open Certificates.P2OriginalSixthElevenLogSemantics

/-- All actually eligible rows, including both tent rows, lie below the
literal clipped value on their own source. This is a pointwise statement
about the original formulas and original priority guards. -/
theorem physical_newCap_le_clippedCap (c : Cell) (t : Physical)
    (hc : PhysicalCell c t) : newCap c t ≤ clippedCap t := by
  by_cases h : c.family = .tent33
  · have hp : ascending33 t < clippedCap t := by
      have hh := hc.priority
      cases c <;> simp_all [Cell.family, priority]
    rw [newCap, if_pos h]
    have he : 0 < eta := by norm_num [eta]
    linarith
  · rw [newCap, if_neg h]

/-- Eligibility of a non-tent row constructs its global dominance in the
actual finite maximum, hence its own mask really is a winner's mask. -/
theorem eligible_clipped_attains_actual_lambda6
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : Cell)
    (hc : c.family ≠ .tent33) (helig : eligibleSixth d N c pre) :
    lambda6 d N pre = newCap c (primeHistoryLogCoordinates N 6 pre) := by
  apply le_antisymm
  · unfold lambda6
    apply finiteMax_le
    · exact (eligibleSixth_actualParent_lt_newCap d N c pre helig).le
    · intro other _hother hother
      have hcc : newCap c (primeHistoryLogCoordinates N 6 pre) =
          clippedCap (primeHistoryLogCoordinates N 6 pre) := by
        rw [newCap, if_neg hc]
      rw [hcc]
      exact physical_newCap_le_clippedCap other _ hother.2.1
  · exact eligibleSixth_newCap_le_lambda6 d N c pre helig

/-- The independent ORIGINAL compact arithmetic caller supplies all the
guards before the winner conclusion is invoked. Neither eligibility nor
global dominance is an assumption on the caller. -/
theorem original_compact_clipped_cell_is_actual_winner
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh))
    (c : Cell) (hc : c.family ≠ .tent33)
    (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    eligibleSixth d (N : ℝ) c (tupleHistory6 p) ∧
      lambda6 d (N : ℝ) (tupleHistory6 p) = newCap c (actualPrimeTupleLog N p) := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  have hcaller := compact_original_tuple_common_sixth_admitted D N cap hN omega homega hcap
    rows4 licensedOriginal J5 rows5 c p hp
  refine ⟨hcaller.2.1, ?_⟩
  simpa only [tupleHistory6_log] using
    eligible_clipped_attains_actual_lambda6 d (N : ℝ) (tupleHistory6 p) c hc hcaller.2.1

end
end ImbalancedChen.P1OriginalClippedSixthAttainedWinner
