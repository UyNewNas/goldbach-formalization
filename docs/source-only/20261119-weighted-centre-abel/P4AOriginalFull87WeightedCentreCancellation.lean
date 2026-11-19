import ImbalancedChen.P4AOriginalFull87CentreIntervalBridge
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The unweighted reflected interval can contain centre primes.  But each
ORIGINAL PLUS-beta room weight includes coprimality of the complete modulus
`a * (p :: pre).prod` with N.  Thus the centre correction vanishes only AFTER
summing against this actual room weight, not pointwise as an interval count.
Finite Abel then removes the centre C from the signed weighted primitive AP
invoice, without treating the unweighted interval count as zero.
-/

namespace ImbalancedChen.P4AOriginalFull87WeightedCentreCancellation
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87CentreIntervalBridge
  (originalCentreReflectedStep originalCentreIntervalCount
   originalCarrierIntervalDiscrepancy original_anchored_eq_carrier_interval_plus_centre
   original_true_jump_endpoint_ge_lower)
open P4AOriginalFull87AnchoredJumpPrimitivePrefix
  (originalFullRoomLowerGate originalAnchoredReflectedPrefix
   originalRoomAnchoredCorrection original_room_abel_eq_anchored_correction
   original_actual_beta_jumps_sum_zero)
open P4AOriginalFull87ReflectedPrefixAbel
  (actualRoomBetaWeight originalRoomAbelCorrection originalRoomBetaVariation
   actual_room_reflected_prime_abel)
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)

/-- A genuine quotient-room weight cannot meet a centre-dividing reflected
prime. The prime prefix is needed for positivity under Nat subtraction. -/
theorem original_room_weight_centre_step_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p a : ℕ) :
    actualRoomBetaWeight N cap w L X pre p a *
      originalCentreReflectedStep N pre p a = 0 := by
  classical
  by_cases ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p
  · have hcop : Nat.Coprime (a * (p :: pre).prod) N :=
      (Finset.mem_filter.mp ha).2.2
    have hnot : ¬ (N - a * (p :: pre).prod ∈ chenPrimePrefix N ∧
        N - a * (p :: pre).prod ∣ N) := by
      rintro ⟨hp, hd⟩
      have hprime : Nat.Prime (N - a * (p :: pre).prod) :=
        (mem_chenPrimePrefix.mp hp).2
      have hle : a * (p :: pre).prod ≤ N := by
        have := hprime.two_le
        omega
      have hreflected : Nat.Coprime (N - a * (p :: pre).prod) N :=
        (Nat.coprime_self_sub_left hle).mpr hcop
      exact (hprime.coprime_iff_not_dvd.mp hreflected) hd
    simp [actualRoomBetaWeight, ha, originalCentreReflectedStep, hnot]
  · simp [actualRoomBetaWeight, ha]

/-- Actual upper endpoint (not the ceil L boundary) is excluded. -/
private theorem original_weight_terminal_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) :
    actualRoomBetaWeight N cap w L X pre p
      (N / (p :: pre).prod + 1) = 0 := by
  have hn : N / (p :: pre).prod + 1 ∉
      actualPrimitiveRosserRoom N cap w L X pre p := by
    intro ha
    have hr := (Finset.mem_filter.mp ha).1
    change N / (p :: pre).prod + 1 ∈ Finset.Ico
      ((N / (2 * (p :: pre).prod) + 1).max
        (X / (p :: pre).prod + 1))
      ((Nat.ceil L).min (N / (p :: pre).prod + 1)) at hr
    have hhi := (Finset.mem_Ico.mp hr).2
    have hmin := min_le_right (Nat.ceil L) (N / (p :: pre).prod + 1)
    omega
  simp [actualRoomBetaWeight, hn]

/-- Finite integration by parts; no distribution assumption. The
corresponding helper in the earlier source-only file is private. -/
private theorem centre_range_abel (v u : ℕ → ℝ) (m : ℕ) :
    (∑ a ∈ Finset.range m, v a * u a) =
    v m * (∑ a ∈ Finset.range m, u a) +
      ∑ t ∈ Finset.range m, (v t - v (t + 1)) *
        (∑ a ∈ Finset.range (t + 1), u a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hU : (∑ a ∈ Finset.range (m + 1), u a) =
          (∑ a ∈ Finset.range m, u a) + u m := by
        rw [Finset.sum_range_succ]
      have hT :
          (∑ t ∈ Finset.range (m + 1), (v t - v (t + 1)) *
            (∑ a ∈ Finset.range (t + 1), u a)) =
          (∑ t ∈ Finset.range m, (v t - v (t + 1)) *
            (∑ a ∈ Finset.range (t + 1), u a)) +
            (v m - v (m + 1)) *
              ((∑ a ∈ Finset.range m, u a) + u m) := by
        rw [Finset.sum_range_succ, hU]
      rw [Finset.sum_range_succ, hU, hT, ih]
      ring

/-- The REAL centre correction is zero after weighting by every original
PLUS-beta jump, even though individual interval centre counts need not be
zero. No C*Var payment is needed on this same weighted room. -/
theorem original_weighted_centre_jump_sum_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) :
    (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (actualRoomBetaWeight N cap w L X pre p t -
        actualRoomBetaWeight N cap w L X pre p (t + 1)) *
      originalCentreIntervalCount N pre p
        (originalFullRoomLowerGate N X pre p) (t + 1)) = 0 := by
  classical
  let v := actualRoomBetaWeight N cap w L X pre p
  let u := originalCentreReflectedStep N pre p
  let m := N / (p :: pre).prod + 1
  let lo := originalFullRoomLowerGate N X pre p
  let C := fun k : ℕ => ∑ a ∈ Finset.range k, u a
  have hweighted : (∑ a ∈ Finset.range m, v a * u a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact original_room_weight_centre_step_zero N cap w L X pre p a
  have hend : v m = 0 := original_weight_terminal_zero N cap w L X pre p
  have hab := centre_range_abel v u m
  rw [hweighted, hend] at hab
  simp only [zero_mul, zero_add] at hab
  have hprefix :
      (∑ t ∈ Finset.range m,
        (v t - v (t + 1)) * C (t + 1)) = 0 := by
    simpa [C] using hab.symm
  have hjumps :
      (∑ t ∈ Finset.range m, (v t - v (t + 1))) = 0 :=
    original_actual_beta_jumps_sum_zero N cap w L X pre p
  have hterm (t : ℕ) (ht : t ∈ Finset.range m) :
      (v t - v (t + 1)) * originalCentreIntervalCount N pre p lo (t + 1) =
      (v t - v (t + 1)) * (C (t + 1) - C lo) := by
    by_cases hj : v t = v (t + 1)
    · simp [hj]
    · have hlo : lo ≤ t + 1 :=
        original_true_jump_endpoint_ge_lower N cap w L X pre p t hj
      have hI : originalCentreIntervalCount N pre p lo (t + 1) =
          C (t + 1) - C lo := by
        exact Finset.sum_Ico_eq_sub u hlo
      rw [hI]
  change (∑ t ∈ Finset.range m,
      (v t - v (t + 1)) * originalCentreIntervalCount N pre p lo (t + 1)) = 0
  calc
    _ = ∑ t ∈ Finset.range m,
        (v t - v (t + 1)) * (C (t + 1) - C lo) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hterm t ht
    _ = (∑ t ∈ Finset.range m,
        (v t - v (t + 1)) * C (t + 1)) -
        (∑ t ∈ Finset.range m, (v t - v (t + 1))) * C lo := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = 0 := by rw [hprefix, hjumps]; ring

/-- Primitive carrier AP interval correction with the SAME actual
PLUS-beta jumps, complete b, original strict lower gate and endpoints. -/
def originalRoomCarrierJumpCorrection
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
    (actualRoomBetaWeight N cap w L X pre p t -
      actualRoomBetaWeight N cap w L X pre p (t + 1)) *
    originalCarrierIntervalDiscrepancy N pre p mean
      (originalFullRoomLowerGate N X pre p) (t + 1)

/-- The full reflected-prime Abel error equals the primitive-carrier
jump invoice EXACTLY, with the centre sum cancelled only after weights.
This is NOT an unweighted centre-prime interval estimate. -/
theorem original_room_abel_eq_carrier_jump_correction
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) :
    originalRoomAbelCorrection N cap w L X pre p mean =
      originalRoomCarrierJumpCorrection N cap w L X pre p mean := by
  rw [original_room_abel_eq_anchored_correction]
  unfold originalRoomAnchoredCorrection originalRoomCarrierJumpCorrection
  have hc := original_weighted_centre_jump_sum_zero N cap w L X pre p
  calc
    (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (actualRoomBetaWeight N cap w L X pre p t -
        actualRoomBetaWeight N cap w L X pre p (t + 1)) *
      originalAnchoredReflectedPrefix N X pre p mean (t + 1)) =
    (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (actualRoomBetaWeight N cap w L X pre p t -
        actualRoomBetaWeight N cap w L X pre p (t + 1)) *
      (originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1) +
       originalCentreIntervalCount N pre p
        (originalFullRoomLowerGate N X pre p) (t + 1))) := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases hj : actualRoomBetaWeight N cap w L X pre p t =
              actualRoomBetaWeight N cap w L X pre p (t + 1)
          · simp [hj]
          · have hlo := original_true_jump_endpoint_ge_lower
              N cap w L X pre p t hj
            rw [original_anchored_eq_carrier_interval_plus_centre
              N X pre p mean (t + 1) hlo]
    _ = originalRoomCarrierJumpCorrection N cap w L X pre p mean +
      (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        (actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)) *
        originalCentreIntervalCount N pre p
          (originalFullRoomLowerGate N X pre p) (t + 1)) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rfl
    _ = _ := by rw [hc, add_zero]

/-- The input required for the actual weighted prime discrepancy can be
reduced from E+C to E. We still MUST authenticate and pay E*Var for all
actual fifth/sixth occurrences and all fixed parameters. -/
theorem original_actual_prime_error_le_carrier_jumps_alone
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hCarrier : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalCarrierIntervalDiscrepancy N pre p mean
        (originalFullRoomLowerGate N X pre p) (t + 1)| ≤ E) :
    |(∑ a ∈ (actualPrimitiveRosserRoom N cap w L X pre p).filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
          actualSmallRosserPlus N cap w L a) -
      mean (p :: pre).prod *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
          actualSmallRosserPlus N cap w L a)| ≤
    E * originalRoomBetaVariation N cap w L X pre p := by
  rw [actual_room_reflected_prime_abel]
  simp only [add_sub_cancel_left]
  rw [original_room_abel_eq_carrier_jump_correction]
  unfold originalRoomCarrierJumpCorrection originalRoomBetaVariation
  calc
    |∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        (actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)) *
        originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1)| ≤
      ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |(actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)) *
        originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)| *
        |originalCarrierIntervalDiscrepancy N pre p mean
          (originalFullRoomLowerGate N X pre p) (t + 1)| := by
            simp_rw [abs_mul]
    _ ≤ ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)| * E := by
            apply Finset.sum_le_sum
            intro t ht
            by_cases hj : actualRoomBetaWeight N cap w L X pre p t =
                actualRoomBetaWeight N cap w L X pre p (t + 1)
            · simp [hj]
            · exact mul_le_mul_of_nonneg_left
                (hCarrier t ht hj) (abs_nonneg _)
    _ = E * ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |actualRoomBetaWeight N cap w L X pre p t -
          actualRoomBetaWeight N cap w L X pre p (t + 1)| := by
            rw [← Finset.sum_mul]
            ring

end
end ImbalancedChen.P4AOriginalFull87WeightedCentreCancellation
