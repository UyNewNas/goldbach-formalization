import ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
import ImbalancedChen.P4AOriginalFull87FiniteEighthCap
import ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: the four ORIGINAL odd-square history exponents, rather than the
weaker full-prefix square tests, are below the genuinely rounded
eighth cap with a strict mesh margin. The claim is first obtained
from the literal full87 Source, its original ideal third comparison,
and its actual strict trim; then instantiated on the ordered actual
owner/trim eighth frontier without replacing the physical history.

The finite Rosser historyOddSquareCeiling J has not yet been identified
in Lean with the maximum of these four N-powers. In particular this
packet does not assert a paid historical-shell loss, a small harmonic
sum, a physical signed-gain monotonicity or a saved archive fact.
-/

namespace ImbalancedChen.P4AOriginalFull87HistoricalCapMargin
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SourceDictionary
  (Cell Point Source source_histories_original_ideal
   source_original_ideal_le_comparison)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87FiniteEighthCap (finiteCap finiteCap_licensed)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier states_eq_owner_filter retainedOwner retainedOwner_some_iff)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)

/-- ORIGINAL odd historical tests: 3*t0, t0+t1+3*t2,
t0+...+t3+3*t4, t0+...+t5+3*t6. Each is a real
source theorem at the original ideal third parent, not the weaker
prefixSquareExpr with coefficient 2 on the current prime.

The source's ideal third bound and its actual comparison bound are
strictly below the SAME rounded finiteCap by the original delta/2
trim licence. Thus none of the four original historical inequalities
is lost in the sole rounding step. -/
theorem original_four_odd_history_exponents_rounded_margin
    (r n : ℕ) (hn : 4 * width n < width r)
    (c : Cell) (t : Point)
    (ht : t ∈ trim c (width r)) :
    ∀ j : Fin 4,
      P4AOriginalRemainingEighthSources.history t j + width r / 2 <
        (finiteCap n c t : ℝ) := by
  have hs : Source c t :=
    trim_subset_source c (width_pos r) ht
  have hcap : P4AOriginalFull87SourceDictionary.comparison c t +
        width r / 2 < (finiteCap n c t : ℝ) :=
    (finiteCap_licensed n (width_pos r) hn ht).2.1
  intro j
  have hh := (source_histories_original_ideal hs) j
  have hparent := source_original_ideal_le_comparison hs
  linarith

/-- The same four strict inequalities hold on EVERY genuinely owned
eighth occurrence, including repetitions in the original state list.
Neither source membership nor a frozen-cap licence is caller supplied.
This uses the original retainedOwner, its strict trim, and the REAL
selected prefix of that state, not an archive coordinate tuple. -/
theorem owned_four_odd_history_exponents_rounded_margin
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ j : Fin 4,
      P4AOriginalRemainingEighthSources.history
        (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) j +
          width r / 2 <
        (finiteCap n c
          (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) : ℝ) := by
  have hlen : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      (width r) n e q om N cap w z c s hs).1
  have hfiltered : s ∈
      (frontier n e q om N cap w z).filter (fun t =>
        decide (retainedOwner (width r) (N : ℝ)
          t.selectedPrefix = some c)) := by
    simpa only [states_eq_owner_filter] using hs
  have howner : retainedOwner (width r) (N : ℝ)
      s.selectedPrefix = some c :=
    of_decide_eq_true (List.mem_filter.mp hfiltered).2
  have htrim : point8 (N : ℝ) s.selectedPrefix ∈ trim c (width r) :=
    ((retainedOwner_some_iff (width r) (N : ℝ)
      s.selectedPrefix c).mp howner).2
  have ht : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ trim c (width r) := by
    simpa only [point8,
      rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using htrim
  exact original_four_odd_history_exponents_rounded_margin
    r n hn c _ ht

/-- Exact PHYSICAL level transport for each of the four original
historical odd-square exponents. The right-hand side is the unchanged
finiteCap branch of actualFrozenPost8Level; the parent branch is NOT
substituted for it. No premise that the eighth historical prefix had
passed this frozen cap is introduced. -/
theorem owned_four_original_history_power_below_actual_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ j : Fin 4,
      (N : ℝ) ^
        (P4AOriginalRemainingEighthSources.history
          (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) j +
            width r / 2) <
        actualFrozenPost8Level n e q om N c s false := by
  have hlen : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      (width r) n e q om N cap w z c s hs).1
  intro j
  have hgate := owned_four_odd_history_exponents_rounded_margin
    r n e q om N cap w z c s hn hs j
  have hpower := Real.rpow_lt_rpow_of_exponent_lt hN hgate
  change (N : ℝ) ^
      (P4AOriginalRemainingEighthSources.history
        (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) j +
          width r / 2) <
    (N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)
  simpa only [point8,
    rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using hpower

end
end ImbalancedChen.P4AOriginalFull87HistoricalCapMargin
