import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.PowerErrorBudget

/-!
# P5: explicit error transport in the original eleven-mean normalization

Source-only candidate. No analytic eleven-mean estimate is asserted.

The new finite statement is two-sided stability with unequal errors. It
uses the actual eleven means and their literal common selection mask.
The other statements PROVE that the explicit BV envelope C*N/log^3(N),
sublinear power-log envelopes and constants disappear in the literal
singularNormalization. These are reusable error transport lemmas, not
assumptions of a whole-weight lower bound or of hLower.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- The signed coefficient of the original eleven-term mean. -/
def p5z_elevenSignedCoefficient
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ) : ℝ :=
  3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀ - b₁₁

/-- Every error is charged with the absolute value of its ORIGINAL
coefficient. The coefficient-three and coefficient-minus-two terms are
not silently normalized to unit coefficients. -/
def p5z_elevenErrorBudget
    (e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ : ℝ) : ℝ :=
  3 * e₁ + e₂ + e₃ + e₄ + e₅ + e₆ + 2 * e₇ + e₈ + e₉ + e₁₀ + e₁₁

/-- Quantitative two-sided stability of the ACTUAL eleven-mean sum.
Errors need not be equal, positive leading coefficients are unnecessary,
and the same mask is used in both affected original terms. This retains
signed deviations until the final estimate; it does not replace the
analytic input by a lower-bound assumption on the assembled weight. -/
theorem p5z_currentChen_eleven_abs_residual_le
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ)
    (e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ : ℝ)
    (h₁ : |currentChenUpsilon1 N - b₁ * singularNormalization N| ≤ e₁)
    (h₂ : |currentChenUpsilon2 N - b₂ * singularNormalization N| ≤ e₂)
    (h₃ : |currentChenUpsilon3 N - b₃ * singularNormalization N| ≤ e₃)
    (h₄ : |currentChenUpsilon4 N - b₄ * singularNormalization N| ≤ e₄)
    (h₅ : |currentChenUpsilon5 N - b₅ * singularNormalization N| ≤ e₅)
    (h₆ : |currentChenUpsilon6 N E - b₆ * singularNormalization N| ≤ e₆)
    (h₇ : |currentChenUpsilon7 N - b₇ * singularNormalization N| ≤ e₇)
    (h₈ : |currentChenUpsilon8 N - b₈ * singularNormalization N| ≤ e₈)
    (h₉ : |currentChenUpsilon9 N - b₉ * singularNormalization N| ≤ e₉)
    (h₁₀ : |currentChenUpsilon10 N - b₁₀ * singularNormalization N| ≤ e₁₀)
    (h₁₁ : |currentChenUpsilon11 N E - b₁₁ * singularNormalization N| ≤ e₁₁) :
    |currentChenPairedPrimeSum N E -
        p5z_elevenSignedCoefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ *
          singularNormalization N| ≤
      p5z_elevenErrorBudget e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ := by
  have h₁' := abs_le.mp h₁
  have h₂' := abs_le.mp h₂
  have h₃' := abs_le.mp h₃
  have h₄' := abs_le.mp h₄
  have h₅' := abs_le.mp h₅
  have h₆' := abs_le.mp h₆
  have h₇' := abs_le.mp h₇
  have h₈' := abs_le.mp h₈
  have h₉' := abs_le.mp h₉
  have h₁₀' := abs_le.mp h₁₀
  have h₁₁' := abs_le.mp h₁₁
  rw [currentChenPairedPrimeSum_eq_upsilon]
  unfold p5z_elevenSignedCoefficient p5z_elevenErrorBudget
  apply abs_le.mpr
  constructor <;> nlinarith only [h₁'.1, h₁'.2, h₂'.1, h₂'.2,
    h₃'.1, h₃'.2, h₄'.1, h₄'.2, h₅'.1, h₅'.2, h₆'.1, h₆'.2,
    h₇'.1, h₇'.2, h₈'.1, h₈'.2, h₉'.1, h₉'.2,
    h₁₀'.1, h₁₀'.2, h₁₁'.1, h₁₁'.2]

/-- A PROVED logarithmic saving conversion, using the actual positive
singular-series lower constant. The coefficient C may be signed.
No upper bound or asymptotic for singularSeries is required. -/
theorem p5z_eventually_logCube_le_singularNormalization
    (C : ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤
        epsilon * singularNormalization N := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C / Real.log (N : ℝ) < epsilon * twinPrimeConstant :=
    (hlog.const_div_atTop C).eventually
      (eventually_lt_nhds (mul_pos hepsilon twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    C * (N : ℝ) / Real.log (N : ℝ) ^ 3 =
        (C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      field_simp [hlogpos.ne'] <;> ring
    _ ≤ (epsilon * twinPrimeConstant) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le
        (div_nonneg (Nat.cast_nonneg N) (sq_nonneg _))
    _ = epsilon *
        (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by ring
    _ ≤ epsilon * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) hepsilon.le

/-- Every fixed real constant is negligible in the literal normalization,
including constants of either sign. -/
theorem p5z_eventually_constant_le_singularNormalization
    (d epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, d ≤ epsilon * singularNormalization N := by
  have hlarge : ∀ᶠ N : ℕ in atTop,
      d / epsilon ≤ singularNormalization N :=
    tendsto_singularNormalization_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with N hN
  simpa only [mul_comm] using (div_le_iff₀ hepsilon).mp hN

/-- The complete explicit envelope is paid, not postulated negligible.
This includes the BV log-cubed cost, any fixed sublinear power-log cost,
and an arbitrary fixed receiver/rounding cost. -/
theorem p5z_eventually_explicit_envelope_le_singularNormalization
    (C c theta d : ℝ) (k : ℕ) (htheta : theta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ 3 +
          c * (N : ℝ) ^ theta * Real.log (N : ℝ) ^ k + d ≤
        epsilon * singularNormalization N := by
  have hthird : 0 < epsilon / 3 := by linarith
  filter_upwards
    [p5z_eventually_logCube_le_singularNormalization C (epsilon / 3) hthird,
      eventually_powerLog_le_singularNormalization c theta k htheta
        (epsilon / 3) hthird,
      p5z_eventually_constant_le_singularNormalization d (epsilon / 3) hthird]
    with N hlog hpower hconstant
  linarith only [hlog, hpower, hconstant]

/-- Error-only transport for an actual finite-source discrepancy. The
input is an explicit numerical envelope, not an assumed normalized o(1)
assertion, and the threshold remains valid on all sufficiently large
even N. This can be applied separately to any original mean residual. -/
theorem p5z_eventually_actual_residual_abs_le_normalized
    (r : ℕ → ℝ) (C c theta d : ℝ) (k : ℕ) (htheta : theta < 1)
    (hsource : ∀ᶠ N : ℕ in atTop, Even N →
      |r N| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 3 +
        c * (N : ℝ) ^ theta * Real.log (N : ℝ) ^ k + d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |r N| ≤ epsilon * singularNormalization N := by
  filter_upwards [hsource,
    p5z_eventually_explicit_envelope_le_singularNormalization C c theta d k
      htheta epsilon hepsilon] with N hsourceN hbudget
  intro hEven
  exact (hsourceN hEven).trans hbudget

end

end ImbalancedChen

