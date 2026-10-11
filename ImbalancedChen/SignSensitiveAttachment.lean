import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sign-sensitive attachment of the small-prime sieve

The manuscript's physical upper coefficient is not obtained by attaching one
small-prime weight to every rough coefficient.  A nonnegative rough
coefficient is paired with the upper fundamental-lemma weight `β⁺`, while a
negative rough coefficient is paired with the lower weight `β⁻`.  The order
reversal caused by the negative coefficient is essential.

This file proves the finite ordered-ring part of that construction.  It does
not assume a density estimate, a distribution theorem, or the desired
majorant as a field of a structure.  The later arithmetic layer must still
identify the pair-indexed expression below with a single coefficient
`ρ_N(q)` by the unique small/rough prime decomposition.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- A finite divisor sum, restricted to a displayed support. -/
def supportedDivisorSum (S : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ S with d ∣ n, w d

/-- Attach the upper small-prime value to a nonnegative coefficient and the
lower small-prime value to a negative coefficient. -/
def signAttachedValue (c Bminus Bplus : ℝ) : ℝ :=
  if 0 ≤ c then c * Bplus else c * Bminus

/-- The sign-sensitive choice preserves the pointwise upper inequality
`c * I ≤ attached(c)`.  The negative branch deliberately uses the lower
small-prime bound. -/
theorem mul_le_signAttachedValue
    {c I Bminus Bplus : ℝ}
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    c * I ≤ signAttachedValue c Bminus Bplus := by
  by_cases hc : 0 ≤ c
  · rw [signAttachedValue, if_pos hc]
    exact mul_le_mul_of_nonneg_left hplus hc
  · rw [signAttachedValue, if_neg hc]
    exact mul_le_mul_of_nonpos_left hminus (le_of_not_ge hc)

/-- The finite pair-indexed expression before the unique small/rough product
is reindexed as the physical coefficient `ρ_N(q)`. -/
def signSensitiveAttachment
    (rough : Finset ℕ) (c : ℕ → ℝ) (Bminus Bplus : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ rough with d ∣ n, signAttachedValue (c d) Bminus Bplus

/-- Sign-sensitive attachment transports the complete rough divisor sum,
not merely each positive summand. -/
theorem mul_supportedDivisorSum_le_signSensitiveAttachment
    (rough : Finset ℕ) (c : ℕ → ℝ) (n : ℕ)
    {I Bminus Bplus : ℝ}
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    I * supportedDivisorSum rough c n ≤
      signSensitiveAttachment rough c Bminus Bplus n := by
  unfold supportedDivisorSum signSensitiveAttachment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  simpa only [mul_comm] using
    (mul_le_signAttachedValue (c := c d) hminus hplus)

/-- The exact algebraic implication used in the manuscript: a nonnegative
small-prime indicator times a rough target remains majorized after attaching
`β⁺` to positive coefficients and `β⁻` to negative coefficients.

The two hypotheses on divisor sums are the local fundamental-lemma and rough
tree statements that later modules must prove for the actual finite weights;
no analytic density or distribution conclusion is hidden here. -/
theorem productTarget_le_signSensitiveAttachment
    (rough : Finset ℕ) (c : ℕ → ℝ) (n : ℕ)
    {I target Bminus Bplus : ℝ}
    (hI : 0 ≤ I)
    (hrough : target ≤ supportedDivisorSum rough c n)
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    I * target ≤ signSensitiveAttachment rough c Bminus Bplus n := by
  exact (mul_le_mul_of_nonneg_left hrough hI).trans
    (mul_supportedDivisorSum_le_signSensitiveAttachment
      rough c n hminus hplus)

/-- In particular the attached divisor expression is nonnegative whenever
the two indicator factors being majorized are nonnegative.  This includes
the zero argument used by outward prime-product smoothings. -/
theorem signSensitiveAttachment_nonneg
    (rough : Finset ℕ) (c : ℕ → ℝ) (n : ℕ)
    {I target Bminus Bplus : ℝ}
    (hI : 0 ≤ I) (htarget : 0 ≤ target)
    (hrough : target ≤ supportedDivisorSum rough c n)
    (hminus : Bminus ≤ I) (hplus : I ≤ Bplus) :
    0 ≤ signSensitiveAttachment rough c Bminus Bplus n := by
  exact (mul_nonneg hI htarget).trans
    (productTarget_le_signSensitiveAttachment
      rough c n hI hrough hminus hplus)

/-- One coefficient of the pair-indexed small/rough attachment. -/
def signAttachedCoefficient
    (c betaMinus betaPlus : ℝ) : ℝ :=
  c * if 0 ≤ c then betaPlus else betaMinus

/-- Once the small and rough coefficients are separately one-bounded, every
coefficient in their sign-sensitive product is one-bounded.  The later
unique-decomposition theorem may therefore transport this estimate to the
single physical coefficient `ρ_N(q)` without a multiplicity factor. -/
theorem abs_signAttachedCoefficient_le_one
    {c betaMinus betaPlus : ℝ}
    (hc : |c| ≤ 1) (hminus : |betaMinus| ≤ 1)
    (hplus : |betaPlus| ≤ 1) :
    |signAttachedCoefficient c betaMinus betaPlus| ≤ 1 := by
  have hbeta : |if 0 ≤ c then betaPlus else betaMinus| ≤ 1 := by
    split
    · exact hplus
    · exact hminus
  rw [signAttachedCoefficient, abs_mul]
  calc
    |c| * |if 0 ≤ c then betaPlus else betaMinus| ≤ 1 * 1 :=
      mul_le_mul hc hbeta (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

end

end ImbalancedChen
