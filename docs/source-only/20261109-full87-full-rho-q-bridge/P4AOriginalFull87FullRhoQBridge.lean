import ImbalancedChen.P4AOriginalFull87StoppedModulusFibres
import ImbalancedChen.P4AOriginalFull87EarlyStopPhysicalGap
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The original stopped q-fibres are NOT the whole physical rho.  This packet
extracts the genuine supported coefficient at each POSITIVE complete modulus
from the existing physical finite sum, and splits it at the actual rank-eight
frontier.  The source is the SAME original policy, root carrier, Rosser
attachment and rank-eight occurrence list on each side.  No analytic estimate,
saved numerical gain, or reserve payment is inferred.
-/

namespace ImbalancedChen.P4AOriginalFull87FullRhoQBridge
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest stoppedTest attachedLeafTest)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87EarlyStopPhysicalGap (physical_eq_stopped_plus_rank8_frontier)
open P4AOriginalFull87StoppedModulusFibres
  (rootStoppedPopulation rootStoppedRho stoppedModulusSupport
   stoppedModulusFibre stopped_terminal_sum_eq_full_modulus_fibres)
open P4AOriginalFull87StoppedTerminalPopulation
  (stoppedPhysicalTerm actual_stopped_eq_physical_terminal_sum)

/-- A coefficient probe at ONE complete modulus.  It does not forget
small Rosser factors, since the probe is applied AFTER their attachment. -/
def qProbe (q d : ℕ) : ℝ := if d = q then 1 else 0

/-- The same probe through the actual strict full-q high cutoff X=0.
Only positive full moduli are extracted; nothing is asserted at q=0. -/
def positiveQProbe (q d : ℕ) : ℝ := highQTest 0 (qProbe q) d

theorem positiveQProbe_eq_qProbe (q : ℕ) (hq : 0 < q) :
    positiveQProbe q = qProbe q := by
  funext d
  by_cases hz : d = 0
  · subst d
    have hne : (0 : ℕ) ≠ q := by omega
    simp [positiveQProbe, qProbe, highQTest, hne]
  · have hd : 0 < d := Nat.pos_of_ne_zero hz
    simp [positiveQProbe, qProbe, highQTest, hd]

/-- Literal full physical coefficient, zero off its original support.
It is NOT a new signed input: the value is the already defined
actualSmallRoughRho for the SAME policy and complete modulus. -/
def supportedPhysicalRho (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℝ :=
  if q ∈ actualSmallRoughModuli (R false) N cap w z then
    actualSmallRoughRho (R false) N cap w z L q else 0

/-- A single complete-modulus probe retrieves the original physical
coefficient, without assuming that it lies in the support. -/
theorem physical_positive_probe_eq_supported_rho
    (R : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    physical R N cap w z L (positiveQProbe q) =
      supportedPhysicalRho R N cap w z L q := by
  rw [positiveQProbe_eq_qProbe q hq]
  change (∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
      actualSmallRoughRho (R false) N cap w z L d *
        (if d = q then (1 : ℝ) else 0)) =
    (if q ∈ actualSmallRoughModuli (R false) N cap w z then
       actualSmallRoughRho (R false) N cap w z L q else 0)
  calc
    _ = ∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
          (if d = q then actualSmallRoughRho (R false) N cap w z L d
           else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> ring
    _ = _ := by simp

/-- The preceding stopped List x small-factor pushforward is evaluated at
one complete q.  The artificially adjoined label {q} is ONLY an index in a
Finset; it cannot create a terminal occurrence or a nonzero coefficient. -/
theorem root_stopped_positive_probe_eq_fibre
    (R : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (positiveQProbe q))
        [] true 1 (roughPrimeUniverse N cap w z) =
      rootStoppedRho R N cap w z L q := by
  let ts := rootStoppedPopulation R N cap w z
  let Q : Finset ℕ := stoppedModulusSupport N cap w ts ∪ {q}
  have hterm := actual_stopped_eq_physical_terminal_sum
    R (fun _ : ℕ => (1 : ℝ)) N cap w L 0 (qProbe q)
    [] true 1 (roughPrimeUniverse N cap w z)
  have hfibre := stopped_terminal_sum_eq_full_modulus_fibres
    N cap w L 0 (qProbe q) ts Q Finset.subset_union_left
  calc
    _ = (ts.map (stoppedPhysicalTerm N cap w L 0 (qProbe q))).sum := by
          exact hterm
    _ = ∑ d ∈ Q, stoppedModulusFibre N cap w L ts d *
          positiveQProbe q d := by
          exact hfibre
    _ = rootStoppedRho R N cap w z L q := by
          rw [positiveQProbe_eq_qProbe q hq]
          change (∑ d ∈ Q, stoppedModulusFibre N cap w L ts d *
              (if d = q then (1 : ℝ) else 0)) =
            stoppedModulusFibre N cap w L ts q
          calc
            _ = ∑ d ∈ Q,
                (if d = q then stoppedModulusFibre N cap w L ts d
                 else 0) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  split_ifs <;> ring
            _ = _ := by
                  have hqQ : q ∈ Q := by simp [Q]
                  simp [hqQ]

/-- The rank-eight coefficient is obtained from the genuine first-exit
frontier's OWN continuation, not a surrogate raw frontier, generic cap,
or an independently specified coefficient.  Its finite probe includes
every original occurrence and every complete small x rough modulus. -/
def rootRankEightRho (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℝ :=
  ((firstExitDepthFrontier 8 R (fun _ : ℕ => (1 : ℝ))
      [] true 1 (roughPrimeUniverse N cap w z)).map
    (fun state =>
      signedTest R (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (positiveQProbe q))
        state.selectedPrefix state.positive state.mass state.remaining)).sum

/-- Exact positive-q coefficient identity for the ORIGINAL full physical
rho.  The already-proved stopped plus rank-eight split is probed at the
same q.  There is no appeal to an asymptotic AP or sieve estimate. -/
theorem supported_rho_eq_stopped_add_real_rank_eight
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    supportedPhysicalRho R N cap w z L q =
      rootStoppedRho R N cap w z L q +
        rootRankEightRho R N cap w z L q := by
  have hsplit := physical_eq_stopped_plus_rank8_frontier
    R heven N cap w z L 0 (qProbe q)
  change physical R N cap w z L (positiveQProbe q) =
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (positiveQProbe q))
      [] true 1 (roughPrimeUniverse N cap w z) +
        rootRankEightRho R N cap w z L q at hsplit
  rw [physical_positive_probe_eq_supported_rho R N cap w z L q hq,
      root_stopped_positive_probe_eq_fibre R N cap w z L q hq] at hsplit
  exact hsplit

/-- Same full-q comparison.  The stopped subcoefficient alone cannot
inherit a manuscript estimate for the complete physical rho. -/
theorem two_policy_full_rho_difference_at_same_q
    (R S : Bool → List ℕ → Bool)
    (hR : ∀ pre, R true pre = true)
    (hS : ∀ pre, S true pre = true)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) (hq : 0 < q) :
    supportedPhysicalRho R N cap w z L q -
      supportedPhysicalRho S N cap w z L q =
    (rootStoppedRho R N cap w z L q -
      rootStoppedRho S N cap w z L q) +
    (rootRankEightRho R N cap w z L q -
      rootRankEightRho S N cap w z L q) := by
  rw [supported_rho_eq_stopped_add_real_rank_eight R hR N cap w z L q hq,
      supported_rho_eq_stopped_add_real_rank_eight S hS N cap w z L q hq]
  ring

/-- Specialization to the two ACTUAL P1.4 producers, with distinct fifth
and sixth admission histories and their own genuine rank-eight frontiers.
No common eighth frontier is assumed or smuggled into this statement. -/
theorem actual_raw_licensed_full_rho_difference_at_same_q
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) (hd : 0 < d) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    supportedPhysicalRho R N cap w z L d -
      supportedPhysicalRho S N cap w z L d =
    (rootStoppedRho R N cap w z L d -
      rootStoppedRho S N cap w z L d) +
    (rootRankEightRho R N cap w z L d -
      rootRankEightRho S N cap w z L d) := by
  dsimp only
  apply two_policy_full_rho_difference_at_same_q
  · intro pre
    exact P4AOriginalFull87CompleteSixthDispatch.policy_even e q om (N : ℝ) pre
  · intro pre
    exact P4AOriginalFull87LicensedSixthPolicy.policy_even delta n e q om (N : ℝ) pre
  · exact hd

end
end ImbalancedChen.P4AOriginalFull87FullRhoQBridge
