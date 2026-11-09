import ImbalancedChen.P4AOriginalFull87FullRhoQBridge
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous FULL q coefficient identity kept the authentic rank-eight contribution
as a signedTest continuation. This file expands that continuation to its OWN
real first-exit terminal leaves and pairs each leaf occurrence with EVERY
original sign-specific small Rosser factor. Neither the frontier nor the
terminal list is deduplicated. q is always the COMPLETE a * selected.prod.

The same signed coefficient is then extracted by a positive-q Kronecker
probe. This is a FINITE reindexing of the existing actual physical rho,
not a second rho, a new analytic input, an o(H_N) error, or a reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87RankEightLeafQFibres
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
  (signedTest signedTest_eq_leaves attachedLeafTest)
open P4AOriginalFull87FullRhoQBridge
  (rootRankEightRho positiveQProbe positiveQProbe_eq_qProbe qProbe
   supportedPhysicalRho supported_rho_eq_stopped_add_real_rank_eight)
open P4AOriginalFull87StoppedModulusFibres (rootStoppedRho)

/-- The ORIGINAL rank-eight frontier is only an intermediate state list.
Continue EACH state with its SAME policy and literal post-candidate carrier,
retaining all terminal occurrences and their signed value. -/
def rankEightContinuationLeaves (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : List (FirstExitLeaf ℕ) :=
  (firstExitDepthFrontier 8 R (fun _ : ℕ => (1 : ℝ))
    [] true 1 (roughPrimeUniverse N cap w z)).flatMap
      (fun s => firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
        s.selectedPrefix s.positive s.mass s.remaining)

/-- Retain all repeated rank-eight frontier states before terminal expansion. -/
private theorem frontier_signed_continuation_eq_leaf_sum
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (states : List (FirstExitDepthState ℕ)) :
    (states.map (fun s =>
        signedTest R (fun _ : ℕ => (1 : ℝ)) T
          s.selectedPrefix s.positive s.mass s.remaining)).sum =
      ((states.flatMap (fun s =>
        firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
          s.selectedPrefix s.positive s.mass s.remaining)).map
            (fun leaf => leaf.value * T leaf.positive leaf.selected)).sum := by
  induction states with
  | nil => simp
  | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.map_append, List.sum_append]
      rw [signedTest_eq_leaves, ih]

/-- Each actual continuation leaf is paired with the ENTIRE real small
Rosser support. The List, not a Finset of leaves, owns multiplicities. -/
def rankEightFactorOccurrences (N cap : ℕ) (w : ℝ)
    (leaves : List (FirstExitLeaf ℕ)) :
    List (FirstExitLeaf ℕ × ℕ) :=
  leaves.flatMap (fun leaf =>
    (actualSmallRosserSupport N cap w).toList.map (fun a => (leaf, a)))

/-- Full physical modulus including the small Rosser factor. -/
def rankEightFullModulus (o : FirstExitLeaf ℕ × ℕ) : ℕ :=
  o.2 * o.1.selected.prod

/-- Original terminal signed value times the sign-specific original beta.
No absolute value is taken before equal complete moduli are added. -/
def rankEightFactorSignedWeight (N cap : ℕ) (w L : ℝ)
    (o : FirstExitLeaf ℕ × ℕ) : ℝ :=
  o.1.value *
    (if o.1.positive then actualSmallRosserPlus N cap w L o.2
     else actualSmallRosserMinus N cap w L o.2)

/-- Genuine signed rank-eight q fibre with occurrence multiplicities. -/
def rootRankEightOccurrenceFibre (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℝ :=
  ((rankEightFactorOccurrences N cap w
      (rankEightContinuationLeaves R N cap w z)).map (fun o =>
        if rankEightFullModulus o = q then
          rankEightFactorSignedWeight N cap w L o else 0)).sum

/-- At a single terminal the original Rosser attachment is literally a
sum of its complete-modulus factor occurrences. -/
private theorem leaf_attached_eq_factor_sum (N cap : ℕ)
    (w L : ℝ) (G : ℕ → ℝ) (leaf : FirstExitLeaf ℕ) :
    leaf.value * attachedLeafTest N cap 1 w L G
        leaf.positive leaf.selected =
      (((actualSmallRosserSupport N cap w).toList.map (fun a =>
        rankEightFactorSignedWeight N cap w L (leaf, a) *
          G (rankEightFullModulus (leaf, a)))).sum) := by
  unfold attachedLeafTest
  rw [Finset.mul_sum, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [rankEightFactorSignedWeight, rankEightFullModulus, one_mul]
  ring

/-- No loss of repeated leaves when the Rosser-factor List is flattened.
The terminal signs and original factors are not separately estimated. -/
private theorem leaf_population_eq_factor_population (N cap : ℕ)
    (w L : ℝ) (G : ℕ → ℝ) (leaves : List (FirstExitLeaf ℕ)) :
    (leaves.map (fun leaf =>
      leaf.value * attachedLeafTest N cap 1 w L G
        leaf.positive leaf.selected)).sum =
    ((rankEightFactorOccurrences N cap w leaves).map (fun o =>
      rankEightFactorSignedWeight N cap w L o *
        G (rankEightFullModulus o))).sum := by
  induction leaves with
  | nil => simp [rankEightFactorOccurrences]
  | cons leaf leaves ih =>
      change
        leaf.value * attachedLeafTest N cap 1 w L G
          leaf.positive leaf.selected +
          (leaves.map (fun t =>
            t.value * attachedLeafTest N cap 1 w L G
              t.positive t.selected)).sum =
        (((actualSmallRosserSupport N cap w).toList.map
          (fun a => (leaf, a)) ++
            rankEightFactorOccurrences N cap w leaves).map (fun o =>
              rankEightFactorSignedWeight N cap w L o *
                G (rankEightFullModulus o))).sum
      simp only [List.map_append, List.sum_append, List.map_map]
      rw [leaf_attached_eq_factor_sum, ih]

/-- The actual rank-eight signedTest continuation, for ANY terminal test,
is exactly the signed sum on its own genuine (leaf, small-factor) population.
This is stronger than a q-probe identity and preserves the original source. -/
theorem real_rank_eight_continuation_eq_full_factor_population
    (R : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    ((firstExitDepthFrontier 8 R (fun _ : ℕ => (1 : ℝ))
      [] true 1 (roughPrimeUniverse N cap w z)).map (fun s =>
        signedTest R (fun _ : ℕ => (1 : ℝ))
          (attachedLeafTest N cap 1 w L G)
          s.selectedPrefix s.positive s.mass s.remaining)).sum =
    ((rankEightFactorOccurrences N cap w
      (rankEightContinuationLeaves R N cap w z)).map (fun o =>
        rankEightFactorSignedWeight N cap w L o *
          G (rankEightFullModulus o))).sum := by
  calc
    _ = ((rankEightContinuationLeaves R N cap w z).map (fun leaf =>
        leaf.value * attachedLeafTest N cap 1 w L G
          leaf.positive leaf.selected)).sum := by
          exact frontier_signed_continuation_eq_leaf_sum R
            (attachedLeafTest N cap 1 w L G)
            (firstExitDepthFrontier 8 R (fun _ : ℕ => (1 : ℝ))
              [] true 1 (roughPrimeUniverse N cap w z))
    _ = _ := leaf_population_eq_factor_population N cap w L G
      (rankEightContinuationLeaves R N cap w z)

/-- Positive-q Kronecker probing identifies the PREVIOUS real rank-eight
coefficient with the occurrence-level signed q fibre. q=0 is excluded
because the original highQTest uses the strict X<q cutoff. -/
theorem real_rank_eight_q_probe_eq_occurrence_fibre
    (R : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    rootRankEightRho R N cap w z L q =
      rootRankEightOccurrenceFibre R N cap w z L q := by
  calc
    _ = ((rankEightFactorOccurrences N cap w
      (rankEightContinuationLeaves R N cap w z)).map (fun o =>
        rankEightFactorSignedWeight N cap w L o *
          positiveQProbe q (rankEightFullModulus o))).sum := by
          exact real_rank_eight_continuation_eq_full_factor_population
            R N cap w z L (positiveQProbe q)
    _ = rootRankEightOccurrenceFibre R N cap w z L q := by
          rw [positiveQProbe_eq_qProbe q hq]
          simp [rootRankEightOccurrenceFibre, qProbe, mul_ite]

/-- The ORIGINAL complete physical q coefficient now has BOTH components
as genuine original List occurrence fibres: early stops and actual
rank-eight continuations. This uses the existing full physical rho,
not an independently defined surrogate and not a sieve estimate. -/
theorem supported_full_rho_eq_stops_add_rank_eight_occurrences
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    supportedPhysicalRho R N cap w z L q =
      rootStoppedRho R N cap w z L q +
        rootRankEightOccurrenceFibre R N cap w z L q := by
  rw [supported_rho_eq_stopped_add_real_rank_eight
    R heven N cap w z L q hq,
    real_rank_eight_q_probe_eq_occurrence_fibre R N cap w z L q hq]

/-- Two policies need NOT agree on their rank-eight frontiers, stopped
populations, or admission histories. Only the actual full modulus q is
shared before taking signed differences. -/
theorem two_policy_full_rho_difference_by_real_occurrences
    (R S : Bool → List ℕ → Bool)
    (hR : ∀ pre, R true pre = true)
    (hS : ∀ pre, S true pre = true)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    supportedPhysicalRho R N cap w z L q -
      supportedPhysicalRho S N cap w z L q =
    (rootStoppedRho R N cap w z L q -
      rootStoppedRho S N cap w z L q) +
    (rootRankEightOccurrenceFibre R N cap w z L q -
      rootRankEightOccurrenceFibre S N cap w z L q) := by
  rw [supported_full_rho_eq_stops_add_rank_eight_occurrences
        R hR N cap w z L q hq,
      supported_full_rho_eq_stops_add_rank_eight_occurrences
        S hS N cap w z L q hq]
  ring

/-- Instantiate the TWO REAL fifth/sixth admission producers, keeping
the true separate post-candidate carrier trees and any repeated leaves. -/
theorem actual_raw_licensed_full_rho_difference_by_real_occurrences
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) (hd : 0 < d) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d =
    (rootStoppedRho R N cap w z L d -
      rootStoppedRho S N cap w z L d) +
    (rootRankEightOccurrenceFibre R N cap w z L d -
      rootRankEightOccurrenceFibre S N cap w z L d) := by
  dsimp only
  apply two_policy_full_rho_difference_by_real_occurrences
  · intro pre
    exact P4AOriginalFull87CompleteSixthDispatch.policy_even
      e q om (N : ℝ) pre
  · intro pre
    exact P4AOriginalFull87LicensedSixthPolicy.policy_even
      delta n e q om (N : ℝ) pre
  · exact hd

end
end ImbalancedChen.P4AOriginalFull87RankEightLeafQFibres
