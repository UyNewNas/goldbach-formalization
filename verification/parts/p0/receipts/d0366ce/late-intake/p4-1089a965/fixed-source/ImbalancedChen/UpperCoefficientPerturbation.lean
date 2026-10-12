import ImbalancedChen.ActualSmallRoughAttachment

/-!
# Compiling rough coefficients without changing the physical weight

A boxed rough coefficient need not be the coefficient of a prefix-closed
tree.  This file transports coefficientwise domination to the actual
sign-attached physical majorant, and bounds the change of that same
physical density by a reciprocal-totient weighted absolute coefficient
error.  The rough carrier may be any common finite carrier containing the
raw and compiled supports; it is not required to be a retained-leaf set.

No box-error estimate, support exponent, integral value, or distribution
estimate is asserted here.  Those are inputs still required from the
actual manuscript compiler and its certificate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

private theorem abs_mul_sub_mul_le_of_opposite_signs
    {c d lo hi M : ℝ} (hc : 0 ≤ c) (hd : d ≤ 0)
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |c * hi - d * lo| ≤ M * |c - d| := by
  have hcd : 0 ≤ c - d := sub_nonneg.mpr (hd.trans hc)
  calc
    |c * hi - d * lo| ≤ |c * hi| + |d * lo| := abs_sub _ _
    _ = c * |hi| + (-d) * |lo| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonpos hd]
    _ ≤ c * M + (-d) * M :=
      add_le_add (mul_le_mul_of_nonneg_left hhi hc)
        (mul_le_mul_of_nonneg_left hlo (neg_nonneg.mpr hd))
    _ = M * |c - d| := by rw [abs_of_nonneg hcd]; ring

/-- The attachment is continuous at coefficient zero, even if the lower
small density is negative.  Both slopes are controlled in absolute value. -/
theorem abs_signAttachedValue_sub_le
    {c d lo hi M : ℝ} (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signAttachedValue c lo hi - signAttachedValue d lo hi| ≤ M * |c - d| := by
  by_cases hc : 0 ≤ c <;> by_cases hd : 0 ≤ d
  · simp only [signAttachedValue, if_pos hc, if_pos hd]
    rw [← sub_mul, abs_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left hhi (abs_nonneg _)
  · simp only [signAttachedValue, if_pos hc, if_neg hd]
    exact abs_mul_sub_mul_le_of_opposite_signs hc (le_of_not_ge hd) hlo hhi
  · simp only [signAttachedValue, if_neg hc, if_pos hd]
    rw [abs_sub_comm (c * lo), abs_sub_comm c]
    exact abs_mul_sub_mul_le_of_opposite_signs hd (le_of_not_ge hc) hlo hhi
  · simp only [signAttachedValue, if_neg hc, if_neg hd]
    rw [← sub_mul, abs_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left hlo (abs_nonneg _)

theorem signSensitiveReciprocalTotientDensity_eq_sum_attached
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity rough c lo hi =
      ∑ d ∈ rough, signAttachedValue (c d) lo hi / (Nat.totient d : ℝ) := by
  unfold signSensitiveReciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d _
  by_cases hc : 0 ≤ c d <;> simp only [signAttachedValue, hc, if_true, if_false] <;> ring

/-- A compiler is charged by the absolute coefficient difference.  Signed
cancellation in a rough main density cannot pay for this perturbation. -/
theorem abs_signSensitiveReciprocalTotientDensity_sub_le
    (rough : Finset ℕ) (compiled raw : ℕ → ℝ) {lo hi M : ℝ}
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signSensitiveReciprocalTotientDensity rough compiled lo hi -
        signSensitiveReciprocalTotientDensity rough raw lo hi| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
  rw [signSensitiveReciprocalTotientDensity_eq_sum_attached,
    signSensitiveReciprocalTotientDensity_eq_sum_attached, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ rough, (signAttachedValue (compiled d) lo hi / (Nat.totient d : ℝ) -
        signAttachedValue (raw d) lo hi / (Nat.totient d : ℝ))| ≤
        ∑ d ∈ rough, |signAttachedValue (compiled d) lo hi / (Nat.totient d : ℝ) -
          signAttachedValue (raw d) lo hi / (Nat.totient d : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ rough, M * (|compiled d - raw d| / (Nat.totient d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      rw [← sub_div, abs_div,
        abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient d : ℝ) from Nat.cast_nonneg _)]
      calc
        |signAttachedValue (compiled d) lo hi - signAttachedValue (raw d) lo hi| /
            (Nat.totient d : ℝ) ≤ (M * |compiled d - raw d|) / (Nat.totient d : ℝ) :=
          div_le_div_of_nonneg_right (abs_signAttachedValue_sub_le hlo hhi)
            (Nat.cast_nonneg _)
        _ = M * (|compiled d - raw d| / (Nat.totient d : ℝ)) := by ring
    _ = M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
      rw [reciprocalTotientDensity, Finset.mul_sum]

/-- The perturbation is for two coefficients attached with the identical
small weights and the identical small/rough carrier. -/
theorem abs_physicalDensitySum_smallRoughRho_sub_le
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) {M : ℝ}
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M) :
    |physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough compiled betaMinus betaPlus) -
        physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough raw betaMinus betaPlus)| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) := by
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough,
    physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough]
  exact abs_signSensitiveReciprocalTotientDensity_sub_le rough compiled raw hminus hplus

/-- Coefficientwise outer compilation preserves the rough divisor bound
on a common carrier; no prefix-closure claim is made about the new support. -/
theorem supportedDivisorSum_le_of_coefficient_le
    (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d) (n : ℕ) :
    supportedDivisorSum rough raw n ≤ supportedDivisorSum rough compiled n := by
  classical
  unfold supportedDivisorSum
  exact Finset.sum_le_sum fun d hd => hdom d (Finset.mem_filter.mp hd).1

/-- The literal beta-minus/beta-plus attachment of a dominating compiled
rough coefficient majorizes the full rough indicator on every integer.
The raw majorant is a visible finite input; the beta bounds are supplied
by the actual Rosser-weight theorem, not postulated again. -/
theorem actualAttachedRho_majorant_of_rough_domination
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (hraw : ∀ n : ℤ, actualIntervalRoughIndicator N w z n ≤
      supportedDivisorSum rough raw n.natAbs)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough compiled
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) n.natAbs := by
  have hs := actualSmallRosser_sandwich N cap w L hL hwL (hwz.trans hzcap) n
  have hr := (hraw n).trans
    (supportedDivisorSum_le_of_coefficient_le rough raw compiled hdom n.natAbs)
  have h := productTarget_le_signSensitiveAttachment rough compiled n.natAbs
    (actualSmallRoughIndicator_nonneg N w n) hr hs.1 hs.2
  rw [actualSmallRoughIndicator_mul_interval N w z hwz n] at h
  exact h.trans_eq (signSensitiveAttachment_eq_smallRough_physicalDivisorSum
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    hrough compiled (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L) n.natAbs)

end

end ImbalancedChen
