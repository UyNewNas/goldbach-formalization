import ImbalancedChen.P4AOriginalFull87ReflectedPrefixAbel
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual original full-modulus reflected PLUS-Rosser Abel correction
localized at the original strict lower quotient gate. Endpoint weight
vanishing causes ALL beta jumps to sum to zero. The analytic obligation
therefore only concerns ANCHORED prefix differences at genuine beta
jumps. This neither authenticates the AP mean nor pays the H_N budget.
-/

namespace ImbalancedChen.P4AOriginalFull87AnchoredJumpPrimitivePrefix
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87ReflectedPrefixAbel
  (actualRoomBetaWeight reflectedPrimePrefixDiscrepancy
   originalRoomAbelCorrection originalRoomBetaVariation
   actual_room_reflected_prime_abel)

/-- Literal strict lower gate of the original complete-modulus room. -/
def originalFullRoomLowerGate (N X : ℕ) (pre : List ℕ) (p : ℕ) : ℕ :=
  (N / (2 * (p :: pre).prod) + 1).max
    (X / (p :: pre).prod + 1)

/-- Anchored unweighted reflected-prime discrepancy, same center N. -/
def originalAnchoredReflectedPrefix (N X : ℕ) (pre : List ℕ)
    (p : ℕ) (mean : ℕ → ℝ) (k : ℕ) : ℝ :=
  reflectedPrimePrefixDiscrepancy N pre p mean k -
    reflectedPrimePrefixDiscrepancy N pre p mean
      (originalFullRoomLowerGate N X pre p)

/-- Genuine PLUS beta jump times anchored prefix. -/
def originalRoomAnchoredCorrection (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
    (actualRoomBetaWeight N cap w L X pre p t -
      actualRoomBetaWeight N cap w L X pre p (t + 1)) *
    originalAnchoredReflectedPrefix N X pre p mean (t + 1)

private theorem sum_weight_jumps (weight : ℕ → ℝ) (m : ℕ) :
    (∑ t ∈ Finset.range m, (weight t - weight (t + 1))) =
      weight 0 - weight m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Strict lower gate forces the zeroth beta weight to vanish. -/
private theorem actual_beta_weight_zero (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) :
    actualRoomBetaWeight N cap w L X pre p 0 = 0 := by
  have hn : 0 ∉ actualPrimitiveRosserRoom N cap w L X pre p := by
    intro ha
    have hr := (Finset.mem_filter.mp ha).1
    change (0 : ℕ) ∈ Finset.Ico
      ((N / (2 * (p :: pre).prod) + 1).max
        (X / (p :: pre).prod + 1))
      ((Nat.ceil L).min (N / (p :: pre).prod + 1)) at hr
    have hlo := (Finset.mem_Ico.mp hr).1
    have hp : (0 : ℕ) <
        (N / (2 * (p :: pre).prod) + 1).max
          (X / (p :: pre).prod + 1) :=
      lt_of_lt_of_le (Nat.zero_lt_succ _) (le_max_left _ _)
    omega
  simp [actualRoomBetaWeight, hn]

/-- Literal upper endpoint is excluded, including b=0. -/
private theorem actual_beta_weight_terminal_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) :
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
    have hmin := min_le_right (Nat.ceil L)
      (N / (p :: pre).prod + 1)
    omega
  simp [actualRoomBetaWeight, hn]

/-- The actual weight jump sum is EXACTLY zero. -/
theorem original_actual_beta_jumps_sum_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ) :
    (∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (actualRoomBetaWeight N cap w L X pre p t -
       actualRoomBetaWeight N cap w L X pre p (t + 1))) = 0 := by
  rw [sum_weight_jumps,
    actual_beta_weight_zero, actual_beta_weight_terminal_zero]
  ring

/-- Old correction equals the anchored correction; no second payment. -/
theorem original_room_abel_eq_anchored_correction
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) :
    originalRoomAbelCorrection N cap w L X pre p mean =
      originalRoomAnchoredCorrection N cap w L X pre p mean := by
  let weight := actualRoomBetaWeight N cap w L X pre p
  let Q := reflectedPrimePrefixDiscrepancy N pre p mean
  let lo := originalFullRoomLowerGate N X pre p
  let m := N / (p :: pre).prod + 1
  have hsum :
      (∑ t ∈ Finset.range m, (weight t - weight (t + 1))) = 0 :=
    original_actual_beta_jumps_sum_zero N cap w L X pre p
  have hrewrite :
      (∑ t ∈ Finset.range m,
        (weight t - weight (t + 1)) * (Q (t + 1) - Q lo)) =
      (∑ t ∈ Finset.range m,
        (weight t - weight (t + 1)) * Q (t + 1)) -
      (∑ t ∈ Finset.range m,
        (weight t - weight (t + 1))) * Q lo := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold originalRoomAbelCorrection
    originalRoomAnchoredCorrection originalAnchoredReflectedPrefix
  change (∑ t ∈ Finset.range m,
      (weight t - weight (t + 1)) * Q (t + 1)) =
    ∑ t ∈ Finset.range m,
      (weight t - weight (t + 1)) * (Q (t + 1) - Q lo)
  rw [hrewrite, hsum]
  ring

/-- Only actual beta jump locations require anchored AP error control.
No uniform bound on prefixes from zero is assumed. -/
theorem original_anchored_correction_abs_le_jump_variation
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hE : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalAnchoredReflectedPrefix N X pre p mean (t + 1)| ≤ E) :
    |originalRoomAbelCorrection N cap w L X pre p mean| ≤
      E * originalRoomBetaVariation N cap w L X pre p := by
  let weight := actualRoomBetaWeight N cap w L X pre p
  let Q := originalAnchoredReflectedPrefix N X pre p mean
  rw [original_room_abel_eq_anchored_correction]
  unfold originalRoomAnchoredCorrection originalRoomBetaVariation
  change |∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      (weight t - weight (t + 1)) * Q (t + 1)| ≤
    E * ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
      |weight t - weight (t + 1)|
  calc
    |∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        (weight t - weight (t + 1)) * Q (t + 1)| ≤
      ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |(weight t - weight (t + 1)) * Q (t + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |weight t - weight (t + 1)| * |Q (t + 1)| := by
      simp_rw [abs_mul]
    _ ≤ ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |weight t - weight (t + 1)| * E := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases heq : weight t = weight (t + 1)
      · simp [heq]
      · exact mul_le_mul_of_nonneg_left
          (hE t ht heq) (abs_nonneg _)
    _ = E * ∑ t ∈ Finset.range (N / (p :: pre).prod + 1),
        |weight t - weight (t + 1)| := by
      rw [← Finset.sum_mul]
      ring

/-- Actual weighted reflected PRIME error, unchanged source and mean. -/
theorem original_actual_prime_error_le_anchored_jump_input
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) (E : ℝ)
    (hE : ∀ t ∈ Finset.range (N / (p :: pre).prod + 1),
      actualRoomBetaWeight N cap w L X pre p t ≠
        actualRoomBetaWeight N cap w L X pre p (t + 1) →
      |originalAnchoredReflectedPrefix N X pre p mean (t + 1)| ≤ E) :
    |(∑ a ∈ (actualPrimitiveRosserRoom N cap w L X pre p).filter
        (fun a => N - a * (p :: pre).prod ∈ chenPrimePrefix N),
          actualSmallRosserPlus N cap w L a) -
      mean (p :: pre).prod *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
          actualSmallRosserPlus N cap w L a)| ≤
      E * originalRoomBetaVariation N cap w L X pre p := by
  rw [actual_room_reflected_prime_abel]
  simp only [add_sub_cancel_left]
  exact original_anchored_correction_abs_le_jump_variation
    N cap w L X pre p mean E hE

end
end ImbalancedChen.P4AOriginalFull87AnchoredJumpPrimitivePrefix
