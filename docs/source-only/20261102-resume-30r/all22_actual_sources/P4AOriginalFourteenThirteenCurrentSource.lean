import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
import ImbalancedChen.P4AOriginalSaving19BankFrontier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing ORIGINAL thirteen bank keeps exactly the same occurrence
list after the literal fourteen action, and every selected thirteen
continuation still uses the actual sixth parent. The opposite original
D23/A23 halfspaces prove this fact for the entire signed continuation,
with arbitrary terminal test and positive-presieve remaining carrier.

No alternate thirteen policy, new source field, moment proof, arithmetic
endpoint, full87 dispatch or All22 ledger is introduced.
-/

namespace ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalCommonRefinedConstructor
open P4AOriginalArchiveFourteenPositivePresieve
open P1Pair12RetainedSignedSource
open P2OriginalAscendingEighthCapDictionary
open OriginalAscendingThirteenCellOwnership
open P4AOriginalLive171819PrimeBank P4AOriginalLive171819CommonParent
open P4AOriginalSaving19BankExhaustion P4AOriginalSaving19BankFrontier

/-- The original selected thirteen has the opposite strict D23 halfspace
from every original ascending-fourteen CellGuard. -/
theorem original_thirteen_excludes_fourteen {i : Fin 13} {t : Fin 8 → ℝ}
    (ht : StrictRows i t) :
    ¬SelectedFamilyGuard P4AOriginalAscending14Literal42.literalPattern t := by
  rintro ⟨j, _hj, hcell⟩
  have hdescending := (old_descending_iff t).mp hcell.old_descending
  change mu < t 1 + t 2 at hdescending
  exact (not_lt_of_ge ht.ascendingThird.le) hdescending

/-- The literal fourteen cap actually inherits on the original thirteen
source. Neither an assumed cap equality nor a claimed separation field. -/
theorem fourteen_level_inherits_on_thirteen
    (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) (i : Fin 13)
    (ht : StrictRows i (primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre))) :
    familyNextLevel N (lambda6 (data e q omega) N)
        P4AOriginalAscending14Literal42.literalPattern (rosserAncestor 8 pre) =
      N ^ lambda6 (data e q omega) N (rosserAncestor 6 pre) := by
  unfold familyNextLevel familyNextExponent
  dsimp only
  rw [if_neg (fun hg => original_thirteen_excludes_fourteen ht hg.1)]
  simp only [inheritedExponent, rosserAncestor_nested 6 8 (by omega)]

/-- A later test reads the same original rank-eight ancestor, so the
whole fourteen-policy decision equals actual policy6 on this source. -/
theorem fourteen_decision_eq_current_on_thirteen
    (e : ℚ) (q : ℕ) (omega N : ℝ) (positive : Bool) (pre : List ℕ)
    (hlen : 8 < pre.length) (i : Fin 13)
    (ht : StrictRows i (primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre))) :
    fourteenPolicy e q omega N positive pre = policy6 (data e q omega) N positive pre := by
  change firstExitDepthSplicePolicy 8 (policy6 (data e q omega) N)
      (frozenParityRosserPolicy false 8
        (familyNextLevel N (lambda6 (data e q omega) N)
          P4AOriginalAscending14Literal42.literalPattern)) positive pre = _
  rw [firstExitDepthSplicePolicy, if_neg (not_le.mpr hlen)]
  change ordinaryParityRosserPolicy false
    (familyNextLevel N (lambda6 (data e q omega) N)
      P4AOriginalAscending14Literal42.literalPattern (rosserAncestor 8 pre)) positive pre = _
  rw [fourteen_level_inherits_on_thirteen e q omega N pre i ht]
  simp only [policy6, firstExitDepthSplicePolicy,
    if_neg (by omega : ¬pre.length ≤ 6), frozenParityRosserPolicy,
    ancestorFrozenPolicy, level6]

/-- Complete signed continuation preservation, including terminal leaves,
incoming mass/sign and arbitrary nonmultiplicative test. -/
theorem fourteen_signed_continuation_eq_current_on_thirteen
    (e : ℚ) (q : ℕ) (omega N : ℝ) (i : Fin 13)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length)
    (ht : StrictRows i (primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre)))
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (fourteenPolicy e q omega N) h T pre positive mass remaining =
      signedTest (policy6 (data e q omega) N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hnext : 8 < (p :: pre).length := by simp only [List.length_cons]; omega
    have ht' : StrictRows i
        (primeHistoryLogCoordinates N 8 (rosserAncestor 8 (p :: pre))) := by
      rwa [rosserAncestor_cons 8 p pre hlen]
    simp only [signedTest,
      fourteen_decision_eq_current_on_thirteen e q omega N (!positive) (p :: pre) hnext i ht']
    rw [ih (pre := pre) (hlen := hlen) (ht := ht) (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := hnext.le) (ht := ht')
        (positive := !positive) (mass := mass * h p)]

/-- Equality of complete List frontiers, before any conversion to a set
or sum; repeated occurrences and their metadata are retained. -/
theorem fourteen_frontier_eight_eq_current
    (e : ℚ) (q : ℕ) (omega N : ℝ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (fourteenPolicy e q omega N) h pre positive mass carrier =
      firstExitDepthFrontier 8 (policy6 (data e q omega) N) h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl _ _ h pre carrier positive mass

/-- The already-defined original thirteen prime bank selects exactly the
same List on the concrete parent and after the fourteen action, for any w. -/
theorem original_thirteen_selected_list_preserved
    (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    selected (.ascending19 i) (data e q omega).e (data e q omega).chi
        (data e q omega).m (data e q omega).omega N cap w z
        (fourteenPolicy e q omega (N : ℝ)) =
      selected (.ascending19 i) (data e q omega).e (data e q omega).chi
        (data e q omega).m (data e q omega).omega N cap w z
        (policy6 (data e q omega) (N : ℝ)) := by
  unfold selected
  rw [fourteen_frontier_eight_eq_current]

/-- Original selected-bank membership supplies its own thirteen source
and rank. Its reciprocal-prime incoming mass and subsequent weights are
kept together. The general theorem above separately permits physical
full-q attachment with unit prime weights; the two weights are not mixed. -/
theorem original_thirteen_bank_continuation_preserved
    (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (w z : ℝ) (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
      (data e q omega).m (data e q omega).omega N cap w z
      (fourteenPolicy e q omega (N : ℝ))) :
    signedTest (fourteenPolicy e q omega (N : ℝ)) (fun p => 1 / ((p : ℝ) - 1))
        T s.selectedPrefix s.positive s.mass s.remaining =
      signedTest (policy6 (data e q omega) (N : ℝ)) (fun p => 1 / ((p : ℝ) - 1))
        T s.selectedPrefix s.positive s.mass s.remaining := by
  obtain ⟨hfront, hregion⟩ := (selected_iff_frontier_bankRegion i
    (data e q omega).e (data e q omega).chi (data e q omega).m (data e q omega).omega
    N cap hN w z (fourteenPolicy e q omega (N : ℝ)) s).mp hs
  have hlen : s.selectedPrefix.length = 8 :=
    firstExitDepthFrontier_selected_length 8 _ _ [] (roughPrimeUniverse N cap w z)
      true 1 (by simp) s hfront
  have hsource := bankRegion_subset_original i (data e q omega).e (data e q omega).chi
    (data e q omega).m (data e q omega).omega hregion
  apply fourteen_signed_continuation_eq_current_on_thirteen e q omega (N : ℝ) i
    (fun p => 1 / ((p : ℝ) - 1)) T s.selectedPrefix hlen.ge
  simpa only [rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using hsource

/-- The physical counterpart uses unit prime weights, so its incoming
mass is the physical one. Selection is by the SAME original13 bankRegion;
all rough primes, target deletion, signs and List occurrences are retained. -/
def originalThirteenPhysicalList (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  (firstExitDepthFrontier 8 (fourteenPolicy e q omega (N : ℝ)) (fun _ => 1)
    [] true 1 (roughPrimeUniverse N cap w z)).filter fun s => decide
      (point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i (data e q omega).e
        (data e q omega).chi (data e q omega).m (data e q omega).omega)

/-- Geometric-bank selection on a physical frontier is the actual
original half-open prime-box selection. This discharges target exclusion
and prime membership from the genuine unit-weight frontier. -/
theorem original_physical_list_iff_prime_bank
    (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N)
    (w z : ℝ) (s : FirstExitDepthState ℕ) :
    s ∈ originalThirteenPhysicalList i e q omega N cap w z ↔
      s ∈ firstExitDepthFrontier 8 (fourteenPolicy e q omega (N : ℝ)) (fun _ => 1)
        [] true 1 (roughPrimeUniverse N cap w z) ∧
      ∃ j ∈ bank (.ascending19 i) (data e q omega).e (data e q omega).chi
          (data e q omega).m (data e q omega).omega,
        primeHistoryTuple 8 s.selectedPrefix ∈
          P4AOriginalCell0HalfOpenPrimeCarrier.primeBox (data e q omega).m N j := by
  simp only [originalThirteenPhysicalList, List.mem_filter, decide_eq_true_eq]
  apply and_congr_right
  intro hs
  have hp (k : Fin 8) := primeHistoryTuple_frontier_mem 8
    (fourteenPolicy e q omega (N : ℝ)) (fun _ => 1) N cap w z s hs k
  have hbox (j : P4AOriginalCell0HalfOpenPrimeCarrier.BoxIndex (data e q omega).m) :
      primeHistoryTuple 8 s.selectedPrefix ∈
          P4AOriginalCell0HalfOpenPrimeCarrier.primeBox (data e q omega).m N j ↔
        point8 (N : ℝ) s.selectedPrefix ∈
          logPrimeMeshCell 0 (19 / 96) (data e q omega).m j := by
    change primeHistoryTuple 8 s.selectedPrefix ∈ actualPrimeBoxTuples N _ _ ↔ _
    rw [mem_actualPrimeBoxTuples_log_iff hN]
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨fun k => ⟨mem_roughPrimeUniverse_prime (hp k),
        mem_roughPrimeUniverse_not_dvd (hp k)⟩, ht⟩
  change (∃ j ∈ bank (.ascending19 i) _ _ _ _,
    point8 (N : ℝ) s.selectedPrefix ∈ logPrimeMeshCell 0 (19 / 96) _ j) ↔ _
  constructor
  · rintro ⟨j, hj, ht⟩
    exact ⟨j, hj, (hbox j).mpr ht⟩
  · rintro ⟨j, hj, hp'⟩
    exact ⟨j, hj, (hbox j).mp hp'⟩

theorem original_thirteen_physical_list_preserved
    (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    originalThirteenPhysicalList i e q omega N cap w z =
      (firstExitDepthFrontier 8 (policy6 (data e q omega) (N : ℝ)) (fun _ => 1)
        [] true 1 (roughPrimeUniverse N cap w z)).filter (fun s => decide
          (point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i (data e q omega).e
            (data e q omega).chi (data e q omega).m (data e q omega).omega)) := by
  unfold originalThirteenPhysicalList
  rw [fourteen_frontier_eight_eq_current]

/-- Same original13 physical selected sum and arbitrary complete-modulus
test. No reciprocal-prime factor is inserted into the unit-weight source.
The old sixth continuation occurs exactly once at every original state. -/
theorem original_thirteen_full_q_continuation_sum_preserved
    (i : Fin 13) (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    ((originalThirteenPhysicalList i e q omega N cap w z).map (fun s =>
      signedTest (fourteenPolicy e q omega (N : ℝ)) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining)).sum =
      ((originalThirteenPhysicalList i e q omega N cap w z).map (fun s =>
        signedTest (policy6 (data e q omega) (N : ℝ)) (fun _ => 1)
          (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining)).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hmem : s ∈ firstExitDepthFrontier 8 (fourteenPolicy e q omega (N : ℝ))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
    point8 (N : ℝ) s.selectedPrefix ∈ bankRegion i (data e q omega).e
      (data e q omega).chi (data e q omega).m (data e q omega).omega := by
    simpa only [originalThirteenPhysicalList, List.mem_filter, decide_eq_true_eq] using hs
  have hlen : s.selectedPrefix.length = 8 :=
    firstExitDepthFrontier_selected_length 8 _ _ [] (roughPrimeUniverse N cap w z)
      true 1 (by simp) s hmem.1
  have hsource := bankRegion_subset_original i (data e q omega).e (data e q omega).chi
    (data e q omega).m (data e q omega).omega hmem.2
  apply fourteen_signed_continuation_eq_current_on_thirteen e q omega (N : ℝ) i
    (fun _ => 1) (attachedLeafTest N cap 1 w L G) s.selectedPrefix hlen.ge
  simpa only [rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using hsource

end
end ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource
