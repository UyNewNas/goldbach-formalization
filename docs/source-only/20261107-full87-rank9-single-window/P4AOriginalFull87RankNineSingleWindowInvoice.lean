import ImbalancedChen.P4AOriginalFull87CapHistoricalCeiling
import ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
import ImbalancedChen.P4AOriginalFull87RankNineActualLevelOrder
import ImbalancedChen.P4AOriginalFull87RankNineTwoSidedWindow
import ImbalancedChen.P4AOriginalFull87RankNinePrimeCrossover
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: on the ACTUAL original 87-cell owned eighth source, use the
previously established strict historical ceiling below the actual cap
and the pre-N common parent to reduce the ninth-prime crossing invoice
to ONE of two finite reciprocal windows. This is an exact finite
identity, not a prime distribution estimate or a reserve debit.

The parent-side historical obstruction remains possible. When it
occurs, the lower cubic cutoff is NOT imposed. The cap-side historical
invoice is zero. Every actual remaining prime occurrence, eighth
physical mass, source cell, and strict/weak endpoint is preserved.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineSingleWindowInvoice
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87RankNineHistoryRisk (historyOddSquareCeiling)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNinePrimeCrossover
  (rankNineThresholdCrosses rankNineReciprocalCrossingCost
   ownedRankNineReciprocalCost owned_rankNine_gap_abs_le_reciprocal_cost)
open P4AOriginalFull87RankNineTwoSidedWindow
  (actualCubicAnnulusCost cubicAnnulus)
open P4AOriginalFull87RankNineActualLevelOrder
  (owned_actual_frozen_parent_lt_cap
   owned_actual_rankNine_cross_iff_forward_windows)
open P4AOriginalFull87CapHistoricalCeiling
  (owned_actual_history_ceiling_below_cap)
open P4AOriginalFull87AllOwnedRealizedHistory
  (exists_shared_history_for_all_owned_eighth_states)
open P4AOriginalFull87CorrectionRankTerminal (ownedRankNineSigned)

/-- A genuine cap-side *cubic-only* truncated invoice. The selected
prefix and remaining list are those of the actual eighth state; this
never replaces the continuation by a different prime population. -/
def actualCapCubicCutoffCost
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  (s.remaining.map (fun p =>
    if (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
        actualFrozenPost8Level n e q om N c s false
    then 1 / ((p : ℝ) - 1) else 0)).sum

/-- The *single* applicable prime window is selected by the actual
historical-square ceiling versus the actual smaller frozen parent.
The first branch is a cap-truncated upper interval, NOT a cubic band.
The second is the original strict-right, weak-left cubic annulus. -/
def actualSingleWindowCost
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  if actualFrozenPost8Level n e q om N c s true ≤
       historyOddSquareCeiling s.selectedPrefix
  then actualCapCubicCutoffCost n e q om N c s
  else actualCubicAnnulusCost n e q om N c s

/-- The previous two-window formula collapses at EACH ACTUAL prime
occurrence because J(H)<R_cap. When J>=R_parent, all cap-eligible
cubic primes cross, including those BELOW the parent cubic cutoff.
When J<R_parent only the genuine cubic annulus can cross. -/
theorem owned_rankNine_cross_iff_single_window
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (p : ℕ) (hp : p ∈ s.remaining) :
    rankNineThresholdCrosses n e q om N c s p ↔
      (if actualFrozenPost8Level n e q om N c s true ≤
            historyOddSquareCeiling s.selectedPrefix
       then (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
              actualFrozenPost8Level n e q om N c s false
       else actualFrozenPost8Level n e q om N c s true ≤
              (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 ∧
            (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
              actualFrozenPost8Level n e q om N c s false) := by
  have hcap := owned_actual_history_ceiling_below_cap
    r n e q om N enumerationCap hN w z c s hn hs
  have hsplit := owned_actual_rankNine_cross_iff_forward_windows
    r n e q om N enumerationCap hN hn w z c s hs hr p hp
  by_cases hparent : actualFrozenPost8Level n e q om N c s true ≤
      historyOddSquareCeiling s.selectedPrefix
  · simp only [if_pos hparent]
    rw [hsplit]
    have hno : ¬ historyOddSquareCeiling s.selectedPrefix <
        actualFrozenPost8Level n e q om N c s true :=
      not_lt_of_ge hparent
    simp [hparent, hno, hcap]
  · simp only [if_neg hparent]
    rw [hsplit]
    have hbelow : historyOddSquareCeiling s.selectedPrefix <
        actualFrozenPost8Level n e q om N c s true :=
      lt_of_not_ge hparent
    simp [hparent, hbelow]

/-- Exact finite reciprocal equality for the ORIGINAL ordered prime
occurrences, not an absolute bound counted once on each side.
No conditional history certificate is packed into a new structure. -/
theorem owned_rankNine_reciprocal_cost_eq_single_window
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N enumerationCap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    rankNineReciprocalCrossingCost n e q om N c s =
      actualSingleWindowCost n e q om N c s := by
  by_cases hparent : actualFrozenPost8Level n e q om N c s true ≤
      historyOddSquareCeiling s.selectedPrefix
  · unfold rankNineReciprocalCrossingCost actualSingleWindowCost
      actualCapCubicCutoffCost
    simp only [if_pos hparent]
    congr 1
    apply List.map_congr_left
    intro p hp
    have heq := owned_rankNine_cross_iff_single_window
      r n e q om N enumerationCap hN hn w z c s hs hr p hp
    simp only [if_pos hparent] at heq
    by_cases hc : (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
        actualFrozenPost8Level n e q om N c s false
    · have hx : rankNineThresholdCrosses n e q om N c s p :=
        heq.mpr hc
      simp [hc, hx]
    · have hx : ¬ rankNineThresholdCrosses n e q om N c s p :=
        fun h => hc (heq.mp h)
      simp [hc, hx]
  · unfold rankNineReciprocalCrossingCost actualSingleWindowCost
      actualCubicAnnulusCost
    simp only [if_neg hparent]
    congr 1
    apply List.map_congr_left
    intro p hp
    have heq := owned_rankNine_cross_iff_single_window
      r n e q om N enumerationCap hN hn w z c s hs hr p hp
    simp only [if_neg hparent] at heq
    have hlevel := owned_actual_frozen_parent_lt_cap
      r n e q om N enumerationCap hN hn w z c s hs hr
    have hbelow : historyOddSquareCeiling s.selectedPrefix <
        actualFrozenPost8Level n e q om N c s true :=
      lt_of_not_ge hparent
    have hband : cubicAnnulus s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false) ↔
        (actualFrozenPost8Level n e q om N c s true ≤
          (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 ∧
         (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
           actualFrozenPost8Level n e q om N c s false) := by
      simp [cubicAnnulus, min_eq_left hlevel.le,
        max_eq_right hlevel.le, hbelow]
    have heq' : rankNineThresholdCrosses n e q om N c s p ↔
        cubicAnnulus s.selectedPrefix p
          (actualFrozenPost8Level n e q om N c s true)
          (actualFrozenPost8Level n e q om N c s false) :=
      heq.trans hband.symm
    by_cases hc : cubicAnnulus s.selectedPrefix p
        (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false)
    · have hx : rankNineThresholdCrosses n e q om N c s p :=
        heq'.mpr hc
      simp [hc, hx]
    · have hx : ¬ rankNineThresholdCrosses n e q om N c s p :=
        fun h => hc (heq'.mp h)
      simp [hc, hx]

/-- All original 87-cell owned states are counted, WITH multiplicity,
in a single physical invoice. There is no new occurrence filter,
independently selected prime set or second cap-side bill. -/
def ownedRankNineSingleWindowInvoice
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N enumerationCap : ℕ) (w z : ℝ) (c : Cell) : ℝ :=
  ((states (width r) n e q om N enumerationCap w z
    (fun _ : ℕ => (1 : ℝ)) c).map (fun s =>
      |s.mass * (s.selectedPrefix.map halfProductDensity).prod| *
        actualSingleWindowCost n e q om N c s)).sum

/-- The original fixed-before-N history parameters prove the ONE-window
physical invoice bound for all 87 cells and all their actual ordered
occurrences. The EVEN-target restriction is exactly the preceding
half-product prime-density supplier's hypothesis. No bound claiming
that the invoice is small, and no reserve payment, is introduced. -/
theorem exists_shared_full87_one_window_signed_invoice
    (r n : ℕ) (hn : 4 * width n < width r) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ (1 / 100 : ℝ) →
      ∀ N : ℕ, 1 < (N : ℝ) → 2 ∣ N →
      ∀ enumerationCap : ℕ, ∀ w z : ℝ, ∀ c : Cell,
        |ownedRankNineSigned r n e q om N enumerationCap w z c true -
         ownedRankNineSigned r n e q om N enumerationCap w z c false| ≤
          ownedRankNineSingleWindowInvoice
            r n e q om N enumerationCap w z c := by
  obtain ⟨e0, he0, hchoose⟩ :=
    exists_shared_history_for_all_owned_eighth_states r
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hh⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq om hom N hN hEven enumerationCap w z c
  calc
    |ownedRankNineSigned r n e q om N enumerationCap w z c true -
       ownedRankNineSigned r n e q om N enumerationCap w z c false| ≤
        ownedRankNineReciprocalCost r n e q om N enumerationCap w z c :=
          owned_rankNine_gap_abs_le_reciprocal_cost
            r n e q om N enumerationCap hEven w z c
    _ = ownedRankNineSingleWindowInvoice
          r n e q om N enumerationCap w z c := by
      unfold ownedRankNineReciprocalCost
        ownedRankNineSingleWindowInvoice
      congr 1
      apply List.map_congr_left
      intro s hs
      have hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c :=
        hh q hq om hom N hN n enumerationCap w z c s hs
      rw [owned_rankNine_reciprocal_cost_eq_single_window
        r n e q om N enumerationCap hN hn w z c s hs hr]

end
end ImbalancedChen.P4AOriginalFull87RankNineSingleWindowInvoice
