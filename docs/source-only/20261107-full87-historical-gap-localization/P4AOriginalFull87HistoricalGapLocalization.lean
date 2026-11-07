import ImbalancedChen.P4AOriginalFull87CapHistoricalCeiling
import ImbalancedChen.P4AOriginalFull87FourHistoryPhysicalTuple
import ImbalancedChen.P4AOriginalFull87HistoricalCapMargin
import ImbalancedChen.P4AOriginalFull87RankNineSingleWindowInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: the ORIGINAL odd-history tests are not merely below the actual
finite eighth cap. They remain below its physical half-mesh retreat.
Thus any parent-side inherited-square risk forces a STRICT, quantitatively
wide separation between the actual sixth parent and rounded eighth cap.
On states without that separation the rank-nine crossing is cubic-only.

No new parent, prime family, geometric mask, external asymptotic
input, signed monotonicity, or reserve debit is introduced.
-/

namespace ImbalancedChen.P4AOriginalFull87HistoricalGapLocalization
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87AllOwnedRealizedHistory
  (owned_eighth_history_primes_and_deletion)
open P4AOriginalFull87HistoricalCapMargin
  (owned_four_odd_history_exponents_rounded_margin)
open P4AOriginalFull87FourHistoryPhysicalTuple
  (rpow_original_four_history_actual_tuple)
open P4AOriginalFull87RankNineHistoryRisk
  (historyOddSquareCeiling)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNinePrimeCrossover (rankNineThresholdCrosses)
open P4AOriginalFull87RankNineSingleWindowInvoice
  (owned_rankNine_cross_iff_single_window)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)

/-- Unlike the previous plain J < cap statement, this preserves the
ENTIRE original half-cell mesh surplus inside the exponent.  Every
physical odd-square suffix is recovered from the SAME actual reversed
eight-prime prefix, and the original strict trim supplies the surplus.
No extra rounding or hypothesis J < cap is assumed. -/
theorem owned_history_ceiling_below_half_mesh_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    historyOddSquareCeiling s.selectedPrefix <
      (N : ℝ) ^ ((finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ) - width r / 2) := by
  obtain ⟨hlen, hsort, _hrem, _hboundary, _hcut⟩ :=
    owned87_eighth_state_exact_carrier
      (width r) n e q om N enumerationCap w z c s hs
  let P : Fin 8 → ℕ := primeHistoryTuple 8 s.selectedPrefix
  have hanti : StrictAnti P :=
    primeHistoryTuple_strictAnti hlen hsort
  have hword :
      s.selectedPrefix =
        [P ⟨7, by decide⟩, P ⟨6, by decide⟩,
         P ⟨5, by decide⟩, P ⟨4, by decide⟩,
         P ⟨3, by decide⟩, P ⟨2, by decide⟩,
         P ⟨1, by decide⟩, P ⟨0, by decide⟩] := by
    have hreverse := primeHistoryTuple_reverse_ofFn
      (k := 8) (history := s.selectedPrefix) hlen
    simpa [P, List.ofFn] using hreverse.symm
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (owned_eighth_history_primes_and_deletion
      r n e q om N enumerationCap w z c s hs p hp).1.pos
  have hgates : ∀ j : Fin 4,
      (∏ i ∈ Finset.univ.filter
        (fun i : Fin 8 => i.val ≤ 2 * j.val), (P i : ℝ)) *
      (P ⟨2 * j.val, by omega⟩ : ℝ) ^ 2 <
      (N : ℝ) ^ ((finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ) - width r / 2) := by
    intro j
    have hm := owned_four_odd_history_exponents_rounded_margin
      r n e q om N enumerationCap w z c s hn hs j
    have hcoordinate :
        point8 (N : ℝ) s.selectedPrefix =
          primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix := by
      simp only [point8,
        rosserAncestor_self_of_length 8 s.selectedPrefix hlen]
    rw [← hcoordinate] at hm
    have hexp :
        P4AOriginalRemainingEighthSources.history
          (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) j <
        (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ) -
          width r / 2 := by
      linarith
    have hpower := Real.rpow_lt_rpow_of_exponent_lt hN hexp
    rw [rpow_original_four_history_actual_tuple
      (N : ℝ) hN s.selectedPrefix hlen hpos j] at hpower
    simpa only [P] using hpower
  conv_lhs => rw [hword]
  exact P4AOriginalFull87CapHistoricalCeiling.
    ordered_tuple_gates_imply_eight_ceiling P hanti
      ((N : ℝ) ^ ((finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ) - width r / 2)) hgates

/-- An actual parent-side inherited-square crossing is impossible
unless the parent level lies STRICTLY below the HALF-MESH cap retreat.
This is a necessary geometric separation on the ORIGINAL owned source,
not an assertion that the wide-gap population has negligible mass. -/
theorem owned_parent_historical_risk_forces_wide_gap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hrisk : actualFrozenPost8Level n e q om N c s true ≤
      historyOddSquareCeiling s.selectedPrefix) :
    actualFrozenPost8Level n e q om N c s true <
      (N : ℝ) ^ ((finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ) - width r / 2) :=
  lt_of_le_of_lt hrisk
    (owned_history_ceiling_below_half_mesh_cap
      r n e q om N enumerationCap hN w z c s hn hs)

/-- In the complementary near-cap region, ALL actual ninth-prime
threshold crossings are cubic-annulus crossings. This does not assume
the parent passes a historical square; it deduces the strict inequality
J < parent from the original FOUR mesh-surplus gates. -/
theorem owned_near_cap_rankNine_cross_iff_cubic_annulus
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (hnear :
      (N : ℝ) ^ ((finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ) - width r / 2) ≤
        actualFrozenPost8Level n e q om N c s true)
    (p : ℕ) (hp : p ∈ s.remaining) :
    rankNineThresholdCrosses n e q om N c s p ↔
      actualFrozenPost8Level n e q om N c s true ≤
        (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 ∧
      (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
        actualFrozenPost8Level n e q om N c s false := by
  have hJ := owned_history_ceiling_below_half_mesh_cap
    r n e q om N enumerationCap hN w z c s hn hs
  have hbelow : historyOddSquareCeiling s.selectedPrefix <
      actualFrozenPost8Level n e q om N c s true :=
    lt_of_lt_of_le hJ hnear
  have hnot : ¬ actualFrozenPost8Level n e q om N c s true ≤
      historyOddSquareCeiling s.selectedPrefix :=
    not_le_of_gt hbelow
  simpa only [if_neg hnot] using
    (owned_rankNine_cross_iff_single_window
      r n e q om N enumerationCap hN hn w z c s hs hr p hp)

end
end ImbalancedChen.P4AOriginalFull87HistoricalGapLocalization
