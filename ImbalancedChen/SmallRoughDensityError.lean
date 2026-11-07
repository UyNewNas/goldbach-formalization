import ImbalancedChen.SmallRoughMainTerm

/-!
# Absolute small-weight error in the same physical density

The sign-sensitive attachment increases the ideal small-Euler-factor times
the rough signed density. Its increase is bounded by the small-weight error
times the absolute rough density. In particular the signed rough density
alone is not an adequate error multiplier. This finite inequality supplies
no estimate for the absolute rough density or for the manuscript's K.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The local sign-sensitive error lies between zero and the absolute
coefficient times the common absolute small-density error. -/
theorem signAttachedValue_density_error
    {c lo hi V delta : ℝ}
    (hlo : V - delta ≤ lo) (hloV : lo ≤ V)
    (hVhi : V ≤ hi) (hhi : hi ≤ V + delta) :
    0 ≤ signAttachedValue c lo hi - c * V ∧
      signAttachedValue c lo hi - c * V ≤ |c| * delta := by
  by_cases hc : 0 ≤ c
  · rw [signAttachedValue, if_pos hc, abs_of_nonneg hc]
    constructor
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr hVhi)]
    · nlinarith [mul_le_mul_of_nonneg_left hhi hc]
  · have hc0 : c ≤ 0 := le_of_not_ge hc
    rw [signAttachedValue, if_neg hc, abs_of_nonpos hc0]
    constructor
    · nlinarith [mul_le_mul_of_nonpos_left hloV hc0]
    · nlinarith [mul_le_mul_of_nonpos_left hlo hc0]

/-- Exact error expression after factoring the ideal Euler density. -/
theorem signSensitiveReciprocalTotientDensity_sub_eq
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi V : ℝ) :
    signSensitiveReciprocalTotientDensity rough c lo hi -
        V * reciprocalTotientDensity rough c =
      ∑ d ∈ rough, (signAttachedValue (c d) lo hi - c d * V) /
        (Nat.totient d : ℝ) := by
  unfold signSensitiveReciprocalTotientDensity reciprocalTotientDensity
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold signAttachedValue
  by_cases hc : 0 ≤ c d <;> simp only [hc, if_true, if_false] <;> ring

/-- The small-density error is multiplied by absolute rough mass, even
though the main term retains the rough coefficients' signs. -/
theorem signSensitiveReciprocalTotientDensity_error
    (rough : Finset ℕ) (c : ℕ → ℝ) {lo hi V delta : ℝ}
    (hlo : V - delta ≤ lo) (hloV : lo ≤ V)
    (hVhi : V ≤ hi) (hhi : hi ≤ V + delta) :
    0 ≤ signSensitiveReciprocalTotientDensity rough c lo hi -
        V * reciprocalTotientDensity rough c ∧
      signSensitiveReciprocalTotientDensity rough c lo hi -
          V * reciprocalTotientDensity rough c ≤
        delta * reciprocalTotientDensity rough (fun d => |c d|) := by
  rw [signSensitiveReciprocalTotientDensity_sub_eq]
  constructor
  · apply Finset.sum_nonneg
    intro d hd
    exact div_nonneg (signAttachedValue_density_error (c := c d) hlo hloV hVhi hhi).1
      (Nat.cast_nonneg _)
  · unfold reciprocalTotientDensity
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    calc
      (signAttachedValue (c d) lo hi - c d * V) / (Nat.totient d : ℝ) ≤
          (|c d| * delta) / (Nat.totient d : ℝ) :=
        div_le_div_of_nonneg_right
          (signAttachedValue_density_error (c := c d) hlo hloV hVhi hhi).2
          (Nat.cast_nonneg _)
      _ = delta * (|c d| / (Nat.totient d : ℝ)) := by ring

/-- Transport the finite absolute-error bound to the very same physical rho. -/
theorem physicalDensitySum_smallRoughRho_error
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (c betaMinus betaPlus : ℕ → ℝ) {V delta : ℝ}
    (hlo : V - delta ≤ reciprocalTotientDensity small betaMinus)
    (hloV : reciprocalTotientDensity small betaMinus ≤ V)
    (hVhi : V ≤ reciprocalTotientDensity small betaPlus)
    (hhi : reciprocalTotientDensity small betaPlus ≤ V + delta) :
    0 ≤ physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough c betaMinus betaPlus) -
        V * reciprocalTotientDensity rough c ∧
      physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough c betaMinus betaPlus) -
          V * reciprocalTotientDensity rough c ≤
        delta * reciprocalTotientDensity rough (fun d => |c d|) := by
  rw [physicalDensitySum_smallRoughRho_eq_signSensitive hsmall hrough]
  exact signSensitiveReciprocalTotientDensity_error rough c hlo hloV hVhi hhi

end

end ImbalancedChen
