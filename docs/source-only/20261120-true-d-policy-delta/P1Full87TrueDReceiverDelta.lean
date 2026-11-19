import ImbalancedChen.P1Full87TrueDPolicyDelta
import ImbalancedChen.P4AOriginalFull87TruePhysicalPrimeDivisor
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
STAGING REQUIRED: the two imported source-only packets must first be
mapped to their indicated ImbalancedChen/ module paths in an isolated
fixed-pin worktree. They are NOT currently installed project modules.

This combines the previous true-d receiver Fubini identity with the
single coefficient on the union of the two genuine physical supports.
No independent rho is chosen, no Q=ab shell is substituted, and no
smooth PP theorem is invoked. The final frozen full87 occurrence
pushforward remains UNMATCHED.
-/

namespace ImbalancedChen.P1Full87TrueDReceiverDelta

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta
open P4AOriginalFull87TruePhysicalPrimeDivisor

/-- An exact signed physical difference of the two receiver divisor
tests is the one original-support delta rho tested on true AP-minus-centre
fibres. The same prime receiver source is used on both sides. -/
theorem trueD_delta_receiver_eq_single_AP
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    (∑ n ∈ chenPrimeReceiverSource N,
      (physicalDivisorSum
          (actualSmallRoughModuli fresh N cap w z)
          (actualSmallRoughRho fresh N cap w z L) n -
       physicalDivisorSum
          (actualSmallRoughModuli old N cap w z)
          (actualSmallRoughRho old N cap w z L) n)) =
      ∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        trueDDeltaRho old fresh N cap w z L d *
          (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d) := by
  rw [Finset.sum_sub_distrib]
  rw [actual_physical_prime_receiver_eq_signed_AP fresh N cap w z L,
      actual_physical_prime_receiver_eq_signed_AP old N cap w z L]
  exact (trueDDeltaRho_test old fresh N cap w z L
    (fun d => chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)).symm

/-- Consequently the true physical receiver difference uses ONE signed
delta coefficient in its exact density, primitive discrepancy, and
negative modulus-prime correction. This does NOT apply manuscript PP. -/
theorem trueD_delta_receiver_primitive_invoice
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hN : Even N) :
    (∑ n ∈ chenPrimeReceiverSource N,
      (physicalDivisorSum
          (actualSmallRoughModuli fresh N cap w z)
          (actualSmallRoughRho fresh N cap w z L) n -
       physicalDivisorSum
          (actualSmallRoughModuli old N cap w z)
          (actualSmallRoughRho old N cap w z L) n)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum
          (trueDDeltaSupport old fresh N cap w z)
          (trueDDeltaRho old fresh N cap w z L) +
      (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        trueDDeltaRho old fresh N cap w z L d *
          finitePrimitiveDiscrepancy
            (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
      (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        trueDDeltaRho old fresh N cap w z L d *
          (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
  rw [trueD_delta_receiver_eq_single_AP]
  exact trueDDeltaRho_primitive_invoice old fresh N cap w z L hN

end
end ImbalancedChen.P1Full87TrueDReceiverDelta
