import ImbalancedChen.P4AOriginalFull87AnchoredJumpPrimitivePrefix
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Convert the original anchored PLUS-beta jump discrepancy into an ACTUAL
reflected-prime quotient INTERVAL, then split the inclusive prime prefix
into the original additive carrier and the exact centre-divisor correction.
No prime distribution input or certified reference mean is assumed.
The correction is NOT zero on an arbitrary quotient interval even when
the actual weighted support itself has no centre-prime contribution.
-/

namespace ImbalancedChen.P4AOriginalFull87CentreIntervalBridge
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87AnchoredJumpPrimitivePrefix
  (originalFullRoomLowerGate originalAnchoredReflectedPrefix
   original_actual_prime_error_le_anchored_jump_input)
open P4AOriginalFull87ReflectedPrefixAbel
  (reflectedPrimeStep reflectedPrimePrefixDiscrepancy
   actualRoomBetaWeight originalRoomBetaVariation)
open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom)

/-- Original prime source after removing centre divisors, evaluated at
the same reflected quotient N-a*b, with the COMPLETE modulus b. -/
def originalCarrierReflectedStep (N : ℕ) (pre : List ℕ)
    (p a : ℕ) : ℝ :=
  if N - a * (p :: pre).prod ∈ chenAdditivePrimeCarrier N then 1 else 0

/-- Exact centre-divisor correction on the inclusive prime prefix. -/
def originalCentreReflectedStep (N : ℕ) (pre : List ℕ)
    (p a : ℕ) : ℝ :=
  if N - a * (p :: pre).prod ∈ chenPrimePrefix N ∧
      N - a * (p :: pre).prod ∣ N then 1 else 0

/-- Primitive-source interval discrepancy, with the original arbitrary
full-modulus reference mean (not an externally certified density). -/
def originalCarrierIntervalDiscrepancy (N : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico lo hi,
    (originalCarrierReflectedStep N pre p a - mean (p :: pre).prod)

/-- Every centre prime in the actual reflected interval is retained. -/
def originalCentreIntervalCount (N : ℕ) (pre : List ℕ)
    (p lo hi : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico lo hi, originalCentreReflectedStep N pre p a

/-- The prime-prefix indicator is EXACTLY the disjoint union of the
original additive carrier and centre prime divisors. -/
theorem original_reflected_step_eq_carrier_add_centre
    (N : ℕ) (pre : List ℕ) (p a : ℕ) :
    reflectedPrimeStep N pre p a =
      originalCarrierReflectedStep N pre p a +
        originalCentreReflectedStep N pre p a := by
  classical
  unfold reflectedPrimeStep originalCarrierReflectedStep
    originalCentreReflectedStep
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  by_cases hp : N - a * (p :: pre).prod ∈ chenPrimePrefix N
  · by_cases hd : N - a * (p :: pre).prod ∣ N
    · simp [hp, hd]
    · simp [hp, hd]
  · simp [hp]

/-- Exact interval subtraction, with the same natural-number endpoints
and full-modulus reference mean on both prefix sums. -/
private theorem reflected_prefix_sub_eq_interval
    (N : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ)
    (lo hi : ℕ) (hlo : lo ≤ hi) :
    reflectedPrimePrefixDiscrepancy N pre p mean hi -
      reflectedPrimePrefixDiscrepancy N pre p mean lo =
    ∑ a ∈ Finset.Ico lo hi,
      (reflectedPrimeStep N pre p a - mean (p :: pre).prod) := by
  unfold reflectedPrimePrefixDiscrepancy
  exact (Finset.sum_Ico_eq_sub
    (fun a => reflectedPrimeStep N pre p a - mean (p :: pre).prod) hlo).symm

/-- The ORIGINAL lower-gate anchored discrepancy is an interval
primitive-source AP discrepancy PLUS the exact centre-divisor count.
This is a finite equality, not a replacement by a guessed AP density. -/
theorem original_anchored_eq_carrier_interval_plus_centre
    (N X : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ)
    (k : ℕ) (hk : originalFullRoomLowerGate N X pre p ≤ k) :
    originalAnchoredReflectedPrefix N X pre p mean k =
      originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) k +
      originalCentreIntervalCount N pre p
        (originalFullRoomLowerGate N X pre p) k := by
  unfold originalAnchoredReflectedPrefix
  rw [reflected_prefix_sub_eq_interval N pre p mean
    (originalFullRoomLowerGate N X pre p) k hk]
  unfold originalCarrierIntervalDiscrepancy originalCentreIntervalCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [original_reflected_step_eq_carrier_add_centre]
  ring

/-- A centre count is nonnegative; it must not be silently discarded. -/
theorem original_centre_interval_nonneg
    (N : ℕ) (pre : List ℕ) (p lo hi : ℕ) :
    0 ≤ originalCentreIntervalCount N pre p lo hi := by
  unfold originalCentreIntervalCount
  apply Finset.sum_nonneg
  intro a ha
  unfold originalCentreReflectedStep
  split_ifs <;> norm_num

/-- No original PLUS-beta weight occurs BELOW the strict original gate. -/
private theorem actual_beta_weight_below_lower_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p a : ℕ) (ha : a < originalFullRoomLowerGate N X pre p) :
    actualRoomBetaWeight N cap w L X pre p a = 0 := by
  have hn : a ∉ actualPrimitiveRosserRoom N cap w L X pre p := by
    intro h
    have hr := (Finset.mem_filter.mp h).1
    change a ∈ Finset.Ico
      ((N / (2 * (p :: pre).prod) + 1).max
        (X / (p :: pre).prod + 1))
      ((Nat.ceil L).min (N / (p :: pre).prod + 1)) at hr
    have hlow := (Finset.mem_Ico.mp hr).1
    have hl : originalFullRoomLowerGate N X pre p ≤ a := by
      simpa [originalFullRoomLowerGate] using hlow
    omega
  simp [actualRoomBetaWeight, hn]

/-- Every genuinely nonzero beta jump has endpoint at or ABOVE the
original lower gate, including the crossing jump t=lo-1. -/
theorem original_true_jump_endpoint_ge_lower
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p t : ℕ)
    (hj : actualRoomBetaWeight N cap w L X pre p t ≠
          actualRoomBetaWeight N cap w L X pre p (t + 1)) :
    originalFullRoomLowerGate N X pre p ≤ t + 1 := by
  by_contra hh
  have ht : t < originalFullRoomLowerGate N X pre p := by omega
  have ht1 : t + 1 < originalFullRoomLowerGate N X pre p := by omega
  have h0 := actual_beta_weight_below_lower_zero
    N cap w L X pre p t ht
  have h1 := actual_beta_weight_below_lower_zero
    N cap w L X pre p (t + 1) ht1
  exact hj (by rw [h0, h1])

/-- All actual jump endpoints in the bounded original quotient room
lie in the SAME residue class N mod b, with no modulus replacement.
This is about the interval geometry, not a prime-distribution theorem. -/
theorem original_reflected_interval_in_full_AP
    (N X : ℕ) (pre : List ℕ) (p k a : ℕ)
    (hb : 0 < (p :: pre).prod)
    (hk : k ≤ N / (p :: pre).prod + 1)
    (ha : a ∈ Finset.Ico (originalFullRoomLowerGate N X pre p) k) :
    Nat.ModEq (p :: pre).prod
      (N - a * (p :: pre).prod) N := by
  have ha_lt := (Finset.mem_Ico.mp ha).2
  have ha_div : a ≤ N / (p :: pre).prod := by omega
  have hamul : a * (p :: pre).prod ≤ N :=
    (Nat.le_div_iff_mul_le hb).mp ha_div
  have hsub : N - (N - a * (p :: pre).prod) =
      a * (p :: pre).prod := by omega
  apply (dvd_sub_iff_modEq_of_le
    (Nat.sub_le N (a * (p :: pre).prod))).mp
  rw [hsub]
  exact ⟨a, by simp [Nat.mul_comm]⟩

/-- The genuine primitive carrier interval and the genuine centre
divisors yield an explicit, SINGLE correction payment at beta jumps.
No assumption hides a bound on the weighted target itself. -/
theorem original_prime_error_le_carrier_interval_plus_centre
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E C : ℝ)
    (hCarrier : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤ E)
    (hCentre : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      originalCentreIntervalCount N pre p
        (originalFullRoomLowerGate N X pre p) (t + 1) ≤ C) :
    |(∑ a ∈ (actualPrimitiveRosserRoom N cap w L X pre p).filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
          actualSmallRosserPlus N cap w L a) -
      mean (p :: pre).prod *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
          actualSmallRosserPlus N cap w L a)| ≤
    (E + C) * originalRoomBetaVariation N cap w L X pre p := by
  have hE : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalAnchoredReflectedPrefix N X pre p mean (t + 1)| ≤ E + C := by
    intro t ht hj
    have hlo := original_true_jump_endpoint_ge_lower
      N cap w L X pre p t hj
    rw [original_anchored_eq_carrier_interval_plus_centre
      N X pre p mean (t + 1) hlo]
    calc
      |originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1) +
        originalCentreIntervalCount N pre p
          (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
        |originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1)| +
        |originalCentreIntervalCount N pre p
          (originalFullRoomLowerGate N X pre p) (t + 1)| :=
            abs_add_le _ _
      _ = |originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1)| +
        originalCentreIntervalCount N pre p
          (originalFullRoomLowerGate N X pre p) (t + 1) := by
            rw [abs_of_nonneg (original_centre_interval_nonneg N pre p _ _)]
      _ ≤ E + C := add_le_add (hCarrier t ht hj) (hCentre t ht hj)
  exact original_actual_prime_error_le_anchored_jump_input
    N cap w L X pre p mean (E + C) hE

end
end ImbalancedChen.P4AOriginalFull87CentreIntervalBridge
