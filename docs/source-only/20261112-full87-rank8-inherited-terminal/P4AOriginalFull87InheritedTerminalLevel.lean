import ImbalancedChen.P4AActualSixthFrozenEighthAdmission
import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Post-eight retained TERMINAL products, on the actual rank-eight state
of the ORIGINAL full87 licensed-sixth/eighth policy.

The theorem below is for the genuinely inherited eighth continuation:
`selectedCap = none`. The entire remaining prime carrier is traversed,
with skipped labels and retained occurrences intact. The inherited
policy is shown equal to the same ordinary parity-safe sixth continuation
on EVERY nonempty extension of that very rank-eight history. Its
complete prefix admission is propagated to terminal leaves, rather than
asserting that an even-rank Boolean alone bounds a product.

The selected-eighth branch still needs a separately certified level
comparison at the actual selectedCap; it is not silently covered here.
No full physical small/rough q or PP input is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87InheritedTerminalLevel
noncomputable section
open scoped Classical

/-- Complete Rosser admissibility survives the exact retained-leaf
recursion, including parity-safe even steps, for an ordered prime suffix.
The prefix must really be admissible at this SAME ordinary level. -/
theorem ordinary_terminal_admissible
    (Q : ℝ) (weight : ℕ → ℝ)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : ordinaryRosserPrefixAdmissible false Q pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ remaining, p.Prime)
    (hsort : (remaining.reverse ++ pre).Pairwise (· < ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false Q) weight
      pre positive mass remaining) :
    ordinaryRosserPrefixAdmissible false Q leaf.selected := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact hpre
  | cons p ps ih =>
      have hsort' : (ps.reverse ++ p :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc,
          List.singleton_append] using hsort
      have hskipSort : (ps.reverse ++ pre).Pairwise (· < ·) :=
        hsort'.sublist ((List.Sublist.refl ps.reverse).append
          ((List.Sublist.refl pre).cons p))
      have hprime' : ∀ q ∈ ps, q.Prime :=
        fun q hq => hprime q (List.mem_cons_of_mem p hq)
      by_cases ht : ordinaryParityRosserPolicy false Q
          (!positive) (p :: pre) = true
      · rw [firstExitRetainedLeaves, if_pos ht, List.mem_append] at hleaf
        rcases hleaf with hskip | htake
        · exact ih pre positive mass hpre hsign hprime'
            hskipSort leaf hskip
        · have hpolicy :=
            ordinaryParityRosserPolicy_eq_full_on_valid_prefix
              false Q pre positive p hpre hsign
              (hprime p (by simp)) (by simp)
              (List.pairwise_append.mp hsort').2.1
          rw [hpolicy] at ht
          have hnext : ordinaryRosserPrefixAdmissible false Q
              (p :: pre) := of_decide_eq_true ht
          have hsign' : (!positive) = evenListLength (p :: pre) := by
            rw [hsign]
            rfl
          exact ih (p :: pre) (!positive) (mass * weight p)
            hnext hsign' hprime' hsort' leaf htake
      · rw [firstExitRetainedLeaves, if_neg ht, List.append_nil] at hleaf
        exact ih pre positive mass hpre hsign hprime'
          hskipSort leaf hleaf

/-- A policy substitution on all NONEMPTY extensions preserves the
literal retained-leaf list. No signed mass, leaf or occurrence is
reindexed or deduplicated by this equality. -/
theorem retained_leaves_congr_nonempty
    (R S : Bool → List ℕ → Bool) (weight : ℕ → ℝ)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (heq : ∀ later : List ℕ, later ≠ [] →
      ∀ b : Bool, R b (later ++ pre) = S b (later ++ pre)) :
    firstExitRetainedLeaves R weight pre positive mass remaining =
      firstExitRetainedLeaves S weight pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hhere : R (!positive) (p :: pre) =
          S (!positive) (p :: pre) := by
        simpa using heq [p] (by simp) (!positive)
      have htakeEq : ∀ later : List ℕ, later ≠ [] →
          ∀ b : Bool, R b (later ++ (p :: pre)) =
            S b (later ++ (p :: pre)) := by
        intro later hne b
        have hh := heq (later ++ [p]) (by simp) b
        simpa only [List.append_assoc, List.singleton_append] using hh
      by_cases ht : S (!positive) (p :: pre) = true
      · simp only [firstExitRetainedLeaves, hhere, if_pos ht]
        rw [ih pre positive mass heq,
          ih (p :: pre) (!positive) (mass * weight p) htakeEq]
      · simp only [firstExitRetainedLeaves, hhere, if_neg ht,
          List.append_nil]
        exact ih pre positive mass heq

/-- Every nonempty descendant of a genuine rank-eight state with no
selected eighth action uses exactly its original frozen sixth level.
This is a policy equality at the true history, not merely a cap bound. -/
private theorem inherited_extension_eq_ordinary
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (pre later : List ℕ) (hlen : 8 ≤ pre.length)
    (hnone : P4AOriginalFull87FiniteEighthPolicy.selectedCap
      delta n (N : ℝ) pre = none)
    (hne : later ≠ []) (b : Bool) :
    P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ) b (later ++ pre) =
    ordinaryParityRosserPolicy false
      ((N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) (rosserAncestor 6 pre))
      b (later ++ pre) := by
  have hpositiveLength : 0 < later.length := by
    cases later with
    | nil => exact (hne rfl).elim
    | cons p ps => simp
  have hdeep8 : ¬ (later ++ pre).length ≤ 8 := by
    simp only [List.length_append]
    omega
  have hdeep6 : ¬ (later ++ pre).length ≤ 6 := by omega
  simp only [P4AOriginalFull87LicensedSixthPolicy.policy,
    firstExitDepthSplicePolicy, if_neg hdeep8,
    P4AOriginalFull87LicensedSixthPolicy.eighthContinuation,
    P4AOriginalFull87FiniteEighthPolicy.selectedCap_append
      delta n (N : ℝ) later pre hlen,
    hnone,
    P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
    firstExitDepthSplicePolicy, if_neg hdeep6,
    frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_append 6 later pre (by omega)]

/-- The ACTUAL eighth frontier is admitted at its own sixth frozen
level and has the literal strictly decreasing remaining prime carrier.
Every terminal leaf of its SAME inherited ordinary continuation thus
has complete Rosser validity, not only a valid rank-eight prefix. -/
private theorem inherited_ordinary_leaf_admissible
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^
          P4AOriginalFull87LicensedSixthPolicy.level6Exponent
            n e q om (N : ℝ) (rosserAncestor 6 s.selectedPrefix)))
      weight s.selectedPrefix s.positive s.mass s.remaining) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) (rosserAncestor 6 s.selectedPrefix))
      leaf.selected := by
  have hSix : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
        n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only
      [P4AOriginalFull87LicensedSixthPolicy.frontier_eq_new_sixth]
      using hs
  have hActual : s ∈ firstExitDepthFrontier 8
      (P4AActualSixthFrozenEighthAdmission.sixthPolicy
        (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
          n e q om (N : ℝ))
        (fun history => (N : ℝ) ^
          P4AOriginalFull87LicensedSixthPolicy.level6Exponent
            n e q om (N : ℝ) history))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [P4AActualSixthFrozenEighthAdmission.sixthPolicy,
      P4AOriginalFull87LicensedSixthPolicy.sixthPolicy] using hSix
  have hadm :=
    P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
      (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
        n e q om (N : ℝ))
      (fun history => (N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) history)
      N cap w z weight s hActual
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    8 (P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)) weight
    (roughPrimeUniverse N cap w z) s hs
  have hsub : s.selectedPrefix.reverse ++ s.remaining <+
      roughPrimeUniverse N cap w z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist
      8 (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] (roughPrimeUniverse N cap w z) true 1 s hs
  have hprime : ∀ p ∈ s.remaining, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime
      (hsub.subset (List.mem_append_right _ hp))
  have horder : (s.selectedPrefix.reverse ++ s.remaining).Pairwise
      (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hsort : (s.remaining.reverse ++ s.selectedPrefix).Pairwise
      (· < ·) := by
    simpa only [List.reverse_append, List.reverse_reverse,
      List.pairwise_reverse] using horder
  exact ordinary_terminal_admissible
    _ weight s.selectedPrefix s.remaining s.positive s.mass
    hadm hsign hprime hsort leaf hleaf

/-- All original post-eight TERMINAL leaves on the inherited (unselected)
eighth continuation satisfy the fixed 299/500 rough product bound.
Unlike a rank-eight prefix bound, this includes every subsequently
selected prime in the genuine same-history retained tree. -/
theorem actual_inherited_terminal_product_lt_fixed_power
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hnone : P4AOriginalFull87FiniteEighthPolicy.selectedCap
      delta n (N : ℝ) s.selectedPrefix = none)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight s.selectedPrefix s.positive s.mass s.remaining) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have hlen : 8 ≤ s.selectedPrefix.length := by
    have hh := firstExitDepthFrontier_selected_length
      8 (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] (roughPrimeUniverse N cap w z) true 1
      (by simp) s hs
    omega
  have hmatch := retained_leaves_congr_nonempty
    (P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ))
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) (rosserAncestor 6 s.selectedPrefix)))
    weight s.selectedPrefix s.remaining s.positive s.mass
    (fun later hne b =>
      inherited_extension_eq_ordinary
        delta n e q om N s.selectedPrefix later hlen hnone hne b)
  rw [hmatch] at hleaf
  have hadm := inherited_ordinary_leaf_admissible
    delta n e q om N cap w z weight s hs leaf hleaf
  have hceil :=
    P4AOriginalFull87WholeSixthCeiling.level6_power_le_initial_ceiling
      n e q om (N : ℝ) he hN.le
      (rosserAncestor 6 s.selectedPrefix)
  exact hadm.1.trans_le hceil

end
end ImbalancedChen.P4AOriginalFull87InheritedTerminalLevel
