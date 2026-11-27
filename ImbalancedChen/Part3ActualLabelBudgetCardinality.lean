import ImbalancedChen.Part3ActualModeCoefficientNormsCore
import ImbalancedChen.Part3ActualHardTailLabelBudget
import Mathlib.Data.Int.Interval

/-!
# Finite cardinality of the original actual-mode label budget

Three original counting theorems are recovered with unchanged statement and
proof bytes: the natural closed-interval bound, the factorCarrier bound,
and the signed nonzero-frequency count. Exact donor identities and offsets
are recorded in CARDINALITY_SOURCE_INTAKE.json for this P3.1 intake.

The new finite steps keep the complete signed f interval, including f=0,
and therefore retain its +1 endpoint allowance. The actual source scales
and quotient carrier use their existing owners. No positive D or delta
hypothesis is added, and total division at a zero denominator is retained.

This bounds the actual label budget explicitly in Q2, H and F. It does not
choose Z, identify the free completed C scale, sum outer modes, or assert
a uniform original-family error budget.
-/

noncomputable section

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
open Classical Finset

theorem card_nat_ceiling_floor_le_length_add_one {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  by_cases hcf : ⌈a⌉₊ ≤ ⌊b⌋₊
  · have hsub : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := by omega
    rw [Nat.card_Icc, Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hlo : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    have hhi : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (ha.trans hab)
    linarith
  · have hempty : (Icc ⌈a⌉₊ ⌊b⌋₊ : Finset ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨hcn, hnf⟩ := Finset.mem_Icc.mp hn
      exact hcf (hcn.trans hnf)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment

namespace ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly

theorem factorCarrier_card_le_add_one {Q : ℝ} (hQ : 1 ≤ Q) :
    ((factorCarrier Q).card : ℝ) ≤ Q + 1 := by
  have h := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
    (a := Q) (b := 2 * Q) (by linarith) (by linarith)
  change ((factorCarrier Q).card : ℝ) ≤ 2 * Q - Q + 1 at h
  linarith

end ImbalancedChen.Part3.GeneralDPhysicalTailCountSourceOnly

namespace ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
open Classical Finset CommonSmoothCutoff

theorem frequency_card_le (H : ℕ) :
    (poissonNonzeroFrequencyWindow H).card ≤ 2 * H := by
  have hu := card_union_le ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ)))
    ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ)))
  have hp : ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ))).card ≤ (Icc 1 H).card := card_image_le
  have hn : ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ))).card ≤ (Icc 1 H).card := card_image_le
  simpa only [poissonNonzeroFrequencyWindow, Nat.card_Icc, Nat.add_sub_cancel] using
    hu.trans (show ((Icc 1 H).image (fun n : ℕ ↦ (n : ℤ))).card +
      ((Icc 1 H).image (fun n : ℕ ↦ -(n : ℤ))).card ≤ 2 * (Icc 1 H).card by omega)

end ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly

namespace ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127
open Classical Finset CommonSmoothCutoff
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualCompletedHardTailMass20261026b

/-- Filtering original factors and taking their quotient image cannot increase
cardinality. This remains valid when the quotient parameter is zero. -/
theorem baseCarrier_card_le_add_one (e : MediumAtom) (hQ : 1 ≤ e.Q2) (q : ℕ) :
    ((baseCarrier e q).card : ℝ) ≤ e.Q2 + 1 := by
  have hi : (baseCarrier e q).card ≤
      ((factorCarrier e.Q2).filter (fun s => q ∣ s)).card := by
    unfold baseCarrier
    exact card_image_le
  have hf : ((factorCarrier e.Q2).filter (fun s => q ∣ s)).card ≤
      (factorCarrier e.Q2).card := card_le_card (filter_subset _ _)
  calc
    _ ≤ ((factorCarrier e.Q2).card : ℝ) := by exact_mod_cast hi.trans hf
    _ ≤ _ := GeneralDPhysicalTailCountSourceOnly.factorCarrier_card_le_add_one hQ

/-- The full signed closed interval contains zero; its endpoint allowance is one. -/
theorem full_signed_interval_card_le {F : ℝ} (hF : 0 ≤ F) :
    ((Icc (Int.ceil (-F)) (Int.floor F)).card : ℝ) ≤ 2 * F + 1 := by
  have hlo : Int.ceil (-F) ≤ (0 : ℤ) := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_zero] using (neg_nonpos.mpr hF)
  have hhi : (0 : ℤ) ≤ Int.floor F := by
    apply Int.le_floor.mpr
    simpa only [Int.cast_zero] using hF
  have hcard : ((Icc (Int.ceil (-F)) (Int.floor F)).card : ℤ) =
      Int.floor F + 1 - Int.ceil (-F) := by
    rw [Int.card_Icc]
    omega
  have hcardR : ((Icc (Int.ceil (-F)) (Int.floor F)).card : ℝ) =
      (Int.floor F : ℝ) + 1 - (Int.ceil (-F) : ℝ) := by
    exact_mod_cast hcard
  rw [hcardR]
  have hl := Int.le_ceil (-F)
  have hh := Int.floor_le F
  linarith

/-- The original f scale is nonnegative, including zero natural denominators. -/
theorem actual_scaleF_nonneg
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (D g : ℕ) :
    0 ≤ scaleF e D g := by
  have hU : 0 ≤ e.U := zero_le_one.trans he.1
  have hQ : 0 ≤ e.Q1 := zero_le_one.trans he.2.2.1
  unfold scaleF
  exact div_nonneg hU
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg g) hQ) (Nat.cast_nonneg D))

/-- All three counts come from the original actual carriers. No final mass or
family-error estimate is assumed, and no primary-block count is inserted. -/
theorem actual_rawLabelBudget_le
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (D delta g : ℕ) (Z : ℝ) :
    rawLabelBudget (baseCarrier e (D / delta))
      (e.sharedSmoothFrequencyBound Z D) (scaleF e D g) ≤
        (2 * scaleF e D g + 1) *
          ((e.Q2 + 1) * (2 * (e.sharedSmoothFrequencyBound Z D : ℝ))) ^ 2 := by
  let T := baseCarrier e (D / delta)
  let H := e.sharedSmoothFrequencyBound Z D
  let F := scaleF e D g
  have hF : 0 ≤ F := actual_scaleF_nonneg he D g
  have hT : (T.card : ℝ) ≤ e.Q2 + 1 :=
    baseCarrier_card_le_add_one e he.2.2.2.1 (D / delta)
  have hH : ((poissonNonzeroFrequencyWindow H).card : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast ActualCompletedZeroPaymentSourceOnly.frequency_card_le H
  have hQ : 0 ≤ e.Q2 + 1 := by linarith [he.2.2.2.1]
  have hp : (T.card : ℝ) * ((poissonNonzeroFrequencyWindow H).card : ℝ) ≤
      (e.Q2 + 1) * (2 * (H : ℝ)) :=
    mul_le_mul hT hH (Nat.cast_nonneg _) hQ
  have hp0 : 0 ≤ (T.card : ℝ) * ((poissonNonzeroFrequencyWindow H).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsq := pow_le_pow_left₀ hp0 hp 2
  unfold rawLabelBudget
  exact mul_le_mul (full_signed_interval_card_le hF) hsq (sq_nonneg _)
    (by linarith)

end ImbalancedChen.Part3.ActualLabelBudgetCardinality20261127

end
