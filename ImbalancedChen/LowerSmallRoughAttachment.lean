import ImbalancedChen.SmallRoughAttachment

/-!
# Reversed sign-sensitive attachment for lower physical weights

A nonnegative rough coefficient selects the lower small weight and a
negative rough coefficient selects the upper one. This is the existing
physical coefficient `smallRoughRho` with its two beta arguments swapped.
Neither the lower small polynomial nor the lower rough divisor sum is
assumed nonnegative. Only the small indicator multiplying the complete
rough inequality is nonnegative.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Reversing the small-weight choice gives the termwise lower inequality. -/
theorem signAttachedValue_swapped_le_mul
    {c I Bminus Bplus : ℝ}
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    signAttachedValue c Bplus Bminus ≤ c * I := by
  by_cases hc : 0 ≤ c
  · rw [signAttachedValue, if_pos hc]
    exact mul_le_mul_of_nonneg_left hminus hc
  · rw [signAttachedValue, if_neg hc]
    exact mul_le_mul_of_nonpos_left hplus (le_of_not_ge hc)

/-- Sum the lower attachment inequalities without dropping negative terms. -/
theorem signSensitiveAttachment_swapped_le_mul_supportedDivisorSum
    (rough : Finset ℕ) (c : ℕ → ℝ) (n : ℕ)
    {I Bminus Bplus : ℝ}
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    signSensitiveAttachment rough c Bplus Bminus n ≤
      I * supportedDivisorSum rough c n := by
  unfold supportedDivisorSum signSensitiveAttachment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _hd
  simpa only [mul_comm] using
    (signAttachedValue_swapped_le_mul (c := c d) hminus hplus)

/-- Multiply the complete rough lower inequality by its small indicator,
then attach the lower or upper beta value according to the rough sign. -/
theorem signSensitiveAttachment_swapped_le_productTarget
    (rough : Finset ℕ) (c : ℕ → ℝ) (n : ℕ)
    {I target Bminus Bplus : ℝ}
    (hI : 0 ≤ I)
    (hrough : supportedDivisorSum rough c n ≤ target)
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    signSensitiveAttachment rough c Bplus Bminus n ≤ I * target := by
  exact (signSensitiveAttachment_swapped_le_mul_supportedDivisorSum
    rough c n hminus hplus).trans (mul_le_mul_of_nonneg_left hrough hI)

/-- The lower pair expression is the divisor sum of the same physical rho.
All natural inputs, including zero, are admitted. Integer applications use
`n.natAbs`. No positivity of either lower polynomial is required. -/
theorem physicalDivisorSum_smallRoughRho_lower
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hroughSupport : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (c betaMinus betaPlus : ℕ → ℝ) (n : ℕ)
    {I target : ℝ} (hI : 0 ≤ I)
    (hrough : supportedDivisorSum rough c n ≤ target)
    (hminus : supportedDivisorSum small betaMinus n ≤ I)
    (hplus : I ≤ supportedDivisorSum small betaPlus n) :
    physicalDivisorSum (smallRoughModuli small rough)
        (smallRoughRho small rough c betaPlus betaMinus) n ≤ I * target := by
  rw [← signSensitiveAttachment_eq_smallRough_physicalDivisorSum
    hsmall hroughSupport c betaPlus betaMinus n]
  exact signSensitiveAttachment_swapped_le_productTarget rough c n hI hrough hminus hplus

end

end ImbalancedChen
