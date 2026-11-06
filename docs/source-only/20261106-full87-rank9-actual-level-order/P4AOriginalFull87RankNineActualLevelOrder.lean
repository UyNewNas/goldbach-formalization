import ImbalancedChen.P4AOriginalFull87RankNineTwoSidedWindow
import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: the prior exact two-sided ninth-rank crossing windows are
not two arbitrary frozen levels on the ACTUAL owned 87-cell source.
Under the existing manuscript-common RealizedHistory supplier and
original cap-resolution condition, the old exponent is the licensed
sixth parent and is STRICTLY BELOW the original rounded eighth cap.

Consequently the actual rank-nine crossover has only the
PARENT-REJECT / CAP-ACCEPT direction, and the exact historical-shell
and cubic-annulus bills are orientable at the same original state.
No new policy, archive fact, prime bound, external premise, or payment.
The conditional RealizedHistory is NOT discharged for all owned states.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineActualLevelOrder
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier retainedOwner retainedOwner_some_iff states_eq_owner_filter)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelIntegration
  (actualParent actual_eighth_kernel_transport)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNinePrimeCrossover
  (rankNineChoiceThreshold rankNineThresholdCrosses
   actual_rankNine_first_choice_iff_threshold)
open P4AOriginalFull87RankNineTwoSidedWindow
  (historicalShell cubicAnnulus actual_cross_iff_two_disjoint_windows)
open P4AOriginalFull87RankNineHistoryRisk (historyOddSquareCeiling)

/-- The STRICT parent/cap orientation comes from the original owned
trim and the existing actual sixth-parent transport, NOT from cap
monotonicity or a newly assumed comparison licence. The only outstanding
hypothesis is the genuine manuscript-common history at THIS state. -/
theorem owned_actual_parent_exponent_lt_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    actualParent n e q om (N : ℝ) s.selectedPrefix <
      (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ) := by
  have hlen : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      (width r) n e q om N cap w z c s hs).1
  have hmem : s ∈
      (frontier n e q om N cap w z).filter (fun t =>
        decide (retainedOwner (width r) (N : ℝ)
          t.selectedPrefix = some c)) := by
    simpa only [states_eq_owner_filter] using hs
  have howner : retainedOwner (width r) (N : ℝ)
      s.selectedPrefix = some c :=
    of_decide_eq_true (List.mem_filter.mp hmem).2
  have htrim : point8 (N : ℝ) s.selectedPrefix ∈
      trim c (width r) :=
    ((retainedOwner_some_iff (width r) (N : ℝ)
      s.selectedPrefix c).mp howner).2
  have ht : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ trim c (width r) := by
    simpa only [point8,
      rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using htrim
  obtain ⟨_, _, hp, hm, _, _⟩ :=
    actual_eighth_kernel_transport r n hn e q om (N : ℝ)
      s.selectedPrefix hlen c ht hr
  have hgap := lt_of_le_of_lt hp hm
  simpa only [point8,
    rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using hgap

/-- The two actual REAL Rosser levels are strictly ordered for N>1.
Exponentiation here uses the actual N, not an invented common base. -/
theorem owned_actual_frozen_parent_lt_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    actualFrozenPost8Level n e q om N c s true <
      actualFrozenPost8Level n e q om N c s false := by
  unfold actualFrozenPost8Level
  simp only [ite_true, ite_false]
  exact Real.rpow_lt_rpow_of_exponent_lt hN
    (owned_actual_parent_exponent_lt_cap
      r n e q om N cap hn w z c s hs hr)

/-- Under the real common-history supplier the parent is the only
possible rejecting side of a rank-nine crossing. In particular the
reverse case, parent-accept/cap-reject, is mathematically impossible. -/
theorem owned_actual_rankNine_cross_iff_forward
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (p : ℕ) :
    rankNineThresholdCrosses n e q om N c s p ↔
      actualFrozenPost8Level n e q om N c s true ≤
        rankNineChoiceThreshold s.selectedPrefix p ∧
      rankNineChoiceThreshold s.selectedPrefix p <
        actualFrozenPost8Level n e q om N c s false := by
  have hlevel := owned_actual_frozen_parent_lt_cap
    r n e q om N cap hN hn w z c s hs hr
  unfold rankNineThresholdCrosses
  dsimp only
  constructor
  · rintro (⟨hpass, hreject⟩ | ⟨hpass, hreject⟩)
    · exact ((not_lt_of_ge hreject) (hpass.trans hlevel)).elim
    · exact ⟨hreject, hpass⟩
  · rintro ⟨hreject, hpass⟩
    exact Or.inr ⟨hpass, hreject⟩

/-- Orientation-resolved, occurrence-preserving two-window formula.
The genuine historical square obstruction survives; it may cross the
sixth-parent level even when the cubic term does not. The two cases
are still disjoint, and both use the original rounded eighth cap. -/
theorem owned_actual_rankNine_cross_iff_forward_windows
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (p : ℕ) (hp : p ∈ s.remaining) :
    rankNineThresholdCrosses n e q om N c s p ↔
      ((actualFrozenPost8Level n e q om N c s true ≤
          historyOddSquareCeiling s.selectedPrefix ∧
        historyOddSquareCeiling s.selectedPrefix <
          actualFrozenPost8Level n e q om N c s false ∧
        (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
          actualFrozenPost8Level n e q om N c s false) ∨
       (historyOddSquareCeiling s.selectedPrefix <
          actualFrozenPost8Level n e q om N c s true ∧
        actualFrozenPost8Level n e q om N c s true ≤
          (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 ∧
        (s.selectedPrefix.prod : ℝ) * (p : ℝ) ^ 3 <
          actualFrozenPost8Level n e q om N c s false)) := by
  have hlevel := owned_actual_frozen_parent_lt_cap
    r n e q om N cap hN hn w z c s hs hr
  rw [actual_cross_iff_two_disjoint_windows
    (width r) n e q om N cap w z c s hs p hp]
  simp only [historicalShell, cubicAnnulus,
    min_eq_left hlevel.le, max_eq_right hlevel.le]

/-- The original parent choosing a ninth prime implies its original
cap also chooses it. This uses actual prime-carrier membership and
the existing literal Rosser threshold, not a new branch mask. -/
theorem owned_actual_rankNine_parent_pass_implies_cap_pass
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (hn : 4 * width n < width r)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (p : ℕ) (hp : p ∈ s.remaining)
    (hpass : ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s true)
      false (p :: s.selectedPrefix) = true) :
    ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s false)
      false (p :: s.selectedPrefix) = true := by
  have hparent := (actual_rankNine_first_choice_iff_threshold
    (width r) n e q om N cap w z c s hs true p hp).mp hpass
  apply (actual_rankNine_first_choice_iff_threshold
    (width r) n e q om N cap w z c s hs false p hp).mpr
  exact hparent.trans
    (owned_actual_frozen_parent_lt_cap
      r n e q om N cap hN hn w z c s hs hr)

end
end ImbalancedChen.P4AOriginalFull87RankNineActualLevelOrder
