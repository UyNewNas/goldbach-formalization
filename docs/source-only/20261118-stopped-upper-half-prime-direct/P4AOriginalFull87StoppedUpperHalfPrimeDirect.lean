import ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
import ImbalancedChen.P4AOriginalFull87UpperHalfPrimeSwitch
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The preceding upper-endpoint audit established that rho0=19/96 is NOT
a license to set the lower rough endpoint w=N^rho0. We do not use any
such cutoff here.

Instead we settle an exact, different part of the remaining stopped
high-q arithmetic invoice. When the FULL original modulus d satisfies
N<2*d, the actual receiver N-P can only be d itself. The upper-half
receiver is therefore the indicator of the ORIGINAL prime P=N-d,
with the centre deletion and strict X<d unchanged. Every occurrence
of the actual fifth producer and sixth suffix is retained.

This packet does NOT derive an o(H_N) upper bound. In particular, the
lower half and all primitive/modulus-prime/centre and reserve payments
remain open. No external PP is invoked.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeDirect

noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87UpperHalfPrimeSwitch (receiver_upper_half_indicator)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel (commonLargeSixthKernel)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail actual_fixed_fifth_tail_linear)

/-- Membership of the ORIGINAL target-deleted receiver is exactly
membership of the complementary ORIGINAL additive prime. We do not
replace the original prime source by a new, hypothetical carrier. -/
theorem receiver_mem_iff_complement_prime (N d : ℕ) :
    d ∈ chenPrimeReceiverSource N ↔
      d ≤ N ∧ (N - d).Prime ∧ Nat.Coprime (N - d) N := by
  classical
  unfold chenPrimeReceiverSource
  constructor
  · intro hd
    obtain ⟨P, hP, hshift⟩ := Finset.mem_image.mp hd
    obtain ⟨hPN, hp, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hP
    have hdN : d ≤ N := by omega
    have hback : N - d = P := by omega
    exact ⟨hdN, by simpa only [hback] using hp,
      by simpa only [hback] using hcop⟩
  · rintro ⟨hdN, hp, hcop⟩
    apply Finset.mem_image.mpr
    refine ⟨N - d, mem_chenAdditivePrimeCarrier.mpr
      ⟨Nat.sub_le N d, hp, hcop⟩, ?_⟩
    omega

/-- The original receiver split at the half-open full-modulus boundary;
the equality case 2*d=N belongs only to the lower half. -/
def upperHalfReceiver (N d : ℕ) : ℝ :=
  if N < 2 * d then receiverTest N d else 0

def lowerHalfReceiver (N d : ℕ) : ℝ :=
  if 2 * d ≤ N then receiverTest N d else 0

/-- A completely explicit original-prime test. The d≤N guard is essential:
a large integer modulus must not create an artificial prime via truncated
natural subtraction. Coprimality is the original centre-prime deletion. -/
def upperHalfComplementPrime (N d : ℕ) : ℝ :=
  if N < 2 * d ∧ d ≤ N ∧ (N - d).Prime ∧ Nat.Coprime (N - d) N
  then 1 else 0

theorem upper_half_receiver_eq_complement_prime (N d : ℕ) :
    upperHalfReceiver N d = upperHalfComplementPrime N d := by
  classical
  by_cases hh : N < 2 * d
  · rw [upperHalfReceiver, if_pos hh,
      receiver_upper_half_indicator N d hh]
    simp [upperHalfComplementPrime, hh, receiver_mem_iff_complement_prime]
  · simp [upperHalfReceiver, upperHalfComplementPrime, hh]

theorem receiver_exact_half_partition (N d : ℕ) :
    receiverTest N d =
      upperHalfReceiver N d + lowerHalfReceiver N d := by
  by_cases hh : N < 2 * d
  · have hl : ¬ 2 * d ≤ N := by omega
    simp [upperHalfReceiver, lowerHalfReceiver, hh, hl]
  · have hl : 2 * d ≤ N := by omega
    simp [upperHalfReceiver, lowerHalfReceiver, hh, hl]

/-- A high-q PLUS-beta term above N/2 is exactly a signed indicator of
the original prime N-d, not an AP main term. The strict X<d cutoff is
kept in addition to the strict half boundary N<2*d. -/
theorem upper_half_beta_factor (N X d : ℕ) (beta : ℝ) :
    beta * highQTest X (upperHalfReceiver N) d =
      if X < d ∧ N < 2 * d ∧ d ≤ N ∧ (N - d).Prime ∧
          Nat.Coprime (N - d) N
      then beta else 0 := by
  rw [upper_half_receiver_eq_complement_prime]
  unfold highQTest upperHalfComplementPrime
  by_cases hx : X < d
  · simp [hx, and_assoc]
  · simp [hx]

/-- Exact ORIGINAL full a*(p::pre).prod invoice. The existing filtered
Rosser index finset and its signed beta are unchanged; no distinct
sixth-prime occurrences are merged, and neither rho nor density is
substituted into this arithmetic identity. -/
theorem large_fifth_upper_half_prime_invoice
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    largeFifthPlusAttachment N cap w L X (upperHalfReceiver N) pre p =
      ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        if X < a * (p :: pre).prod ∧
            N < 2 * (a * (p :: pre).prod) ∧
            a * (p :: pre).prod ≤ N ∧
            (N - a * (p :: pre).prod).Prime ∧
            Nat.Coprime (N - a * (p :: pre).prod) N
        then actualSmallRosserPlus N cap w L a else 0 := by
  unfold largeFifthPlusAttachment
  apply Finset.sum_congr rfl
  intro a ha
  exact upper_half_beta_factor N X (a * (p :: pre).prod)
    (actualSmallRosserPlus N cap w L a)

/-- The real stopped sixth carrier is the same ordered List. This
transports the exact prime invoice without cancelling signs or imposing
an unrelated mask on any inherited branch. -/
theorem common_sixth_upper_half_prime_invoice
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    commonLargeSixthKernel N cap w L X (upperHalfReceiver N) fifth =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ a ∈ largeFifthRosserIndices N cap w X fifth.selectedAfter,
            if X < a * (p :: fifth.selectedAfter).prod ∧
                N < 2 * (a * (p :: fifth.selectedAfter).prod) ∧
                a * (p :: fifth.selectedAfter).prod ≤ N ∧
                (N - a * (p :: fifth.selectedAfter).prod).Prime ∧
                Nat.Coprime (N - a * (p :: fifth.selectedAfter).prod) N
            then actualSmallRosserPlus N cap w L a else 0))).sum := by
  unfold commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [large_fifth_upper_half_prime_invoice]

/-- The actual fifth-exclusive stopped receiver is partitioned ONCE into
an exact original-prime upper-half invoice and the still-open lower-half
receiver. The existing sharedRankFour states and original fifth-exclusive
event List are fixed independently of the arithmetic test F. -/
theorem actual_stopped_receiver_prime_upper_half_split
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (receiverTest N) =
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (upperHalfComplementPrime N) +
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (lowerHalfReceiver N) := by
  have hsource : receiverTest N =
      (fun d => (1 : ℝ) * upperHalfReceiver N d +
        (1 : ℝ) * lowerHalfReceiver N d) := by
    funext d
    simpa only [one_mul] using receiver_exact_half_partition N d
  have hprime : upperHalfReceiver N = upperHalfComplementPrime N := by
    funext d
    exact upper_half_receiver_eq_complement_prime N d
  calc
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (receiverTest N) =
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (fun d => (1 : ℝ) * upperHalfReceiver N d +
          (1 : ℝ) * lowerHalfReceiver N d) := by
            exact congrArg
              (actualFixedSignedFifthTail delta n e q om N cap w z L X)
              hsource
    _ = actualFixedSignedFifthTail delta n e q om N cap w z L X
          (upperHalfReceiver N) +
        actualFixedSignedFifthTail delta n e q om N cap w z L X
          (lowerHalfReceiver N) := by
            simpa only [one_mul] using
              (actual_fixed_fifth_tail_linear delta n e q om
                N cap w z L X (upperHalfReceiver N)
                (lowerHalfReceiver N) 1 1)
    _ = _ := by rw [hprime]

end
end ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeDirect
