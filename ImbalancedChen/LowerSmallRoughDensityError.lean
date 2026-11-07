import ImbalancedChen.LowerSmallRoughAttachment
import ImbalancedChen.SmallRoughDensityError

/-!
# Absolute density loss of the same physical lower attachment

Positive rough coefficients use beta-minus and negative rough coefficients
use beta-plus. Thus attachment lowers the small-Euler-factor times the
signed rough density. Its loss is bounded using absolute rough density,
even if either lower polynomial or the signed rough main term is negative.
These are finite inequalities; the actual small-density sandwich is a
separate proved supplier for the concrete application.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The reversed local attachment has a nonnegative, absolutely controlled loss. -/
theorem signAttachedValue_lower_density_error
    {c lo hi V delta : ℝ}
    (hlo : V - delta ≤ lo) (hloV : lo ≤ V)
    (hVhi : V ≤ hi) (hhi : hi ≤ V + delta) :
    0 ≤ c * V - signAttachedValue c hi lo ∧
      c * V - signAttachedValue c hi lo ≤ |c| * delta := by
  by_cases hc : 0 ≤ c
  · rw [signAttachedValue, if_pos hc, abs_of_nonneg hc]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hloV hc]
    · nlinarith [mul_le_mul_of_nonneg_left hlo hc]
  · have hc0 : c ≤ 0 := le_of_not_ge hc
    rw [signAttachedValue, if_neg hc, abs_of_nonpos hc0]
    constructor
    · nlinarith [mul_le_mul_of_nonpos_left hVhi hc0]
    · nlinarith [mul_le_mul_of_nonpos_left hhi hc0]

/-- Exact finite loss identity for the reversed small-density selection. -/
theorem signSensitiveReciprocalTotientDensity_lower_sub_eq
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi V : ℝ) :
    V * reciprocalTotientDensity rough c -
        signSensitiveReciprocalTotientDensity rough c hi lo =
      ∑ d ∈ rough, (c d * V - signAttachedValue (c d) hi lo) /
        (Nat.totient d : ℝ) := by
  unfold signSensitiveReciprocalTotientDensity reciprocalTotientDensity
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  unfold signAttachedValue
  by_cases hc : 0 ≤ c d <;> simp only [hc, if_true, if_false] <;> ring

/-- Absolute rough mass controls the lower-density loss; the signed main
term remains unchanged. No sign assumption is imposed on `lo` or `c`. -/
theorem signSensitiveReciprocalTotientDensity_lower_error
    (rough : Finset ℕ) (c : ℕ → ℝ) {lo hi V delta : ℝ}
    (hlo : V - delta ≤ lo) (hloV : lo ≤ V)
    (hVhi : V ≤ hi) (hhi : hi ≤ V + delta) :
    0 ≤ V * reciprocalTotientDensity rough c -
        signSensitiveReciprocalTotientDensity rough c hi lo ∧
      V * reciprocalTotientDensity rough c -
          signSensitiveReciprocalTotientDensity rough c hi lo ≤
        delta * reciprocalTotientDensity rough (fun d => |c d|) := by
  rw [signSensitiveReciprocalTotientDensity_lower_sub_eq]
  constructor
  · apply Finset.sum_nonneg
    intro d _hd
    exact div_nonneg (signAttachedValue_lower_density_error (c := c d) hlo hloV hVhi hhi).1
      (Nat.cast_nonneg _)
  · unfold reciprocalTotientDensity
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _hd
    calc
      (c d * V - signAttachedValue (c d) hi lo) / (Nat.totient d : ℝ) ≤
          (|c d| * delta) / (Nat.totient d : ℝ) :=
        div_le_div_of_nonneg_right
          (signAttachedValue_lower_density_error (c := c d) hlo hloV hVhi hhi).2
          (Nat.cast_nonneg _)
      _ = delta * (|c d| / (Nat.totient d : ℝ)) := by ring

/-- Transport the loss bound to the same physical rho used pointwise.
The beta arguments are swapped literally, not replaced by unrelated weights. -/
theorem physicalDensitySum_smallRoughRho_lower_error
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (c betaMinus betaPlus : ℕ → ℝ) {V delta : ℝ}
    (hlo : V - delta ≤ reciprocalTotientDensity small betaMinus)
    (hloV : reciprocalTotientDensity small betaMinus ≤ V)
    (hVhi : V ≤ reciprocalTotientDensity small betaPlus)
    (hhi : reciprocalTotientDensity small betaPlus ≤ V + delta) :
    0 ≤ V * reciprocalTotientDensity rough c -
        physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough c betaPlus betaMinus) ∧
      V * reciprocalTotientDensity rough c -
          physicalDensitySum (smallRoughModuli small rough)
            (smallRoughRho small rough c betaPlus betaMinus) ≤
        delta * reciprocalTotientDensity rough (fun d => |c d|) := by
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough]
  exact signSensitiveReciprocalTotientDensity_lower_error rough c hlo hloV hVhi hhi

end

end ImbalancedChen
