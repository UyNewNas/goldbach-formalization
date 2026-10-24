import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.CurrentChenLowerScale

/-!
Source-only P5 integration, 2026-10-24z.

This is the filter assembly for the literal original eleven entries.
It is intentionally conditional on their separate analytic suppliers.
It does not assert that the adopted coefficients or mask have been proved.
The mask may depend on N and is shared by entries six and eleven.
No upper bound for bad semiprimes (P4-B) is used.
-/

namespace ImbalancedChen
namespace P5OriginalElevenEventualAssembly

open Filter

noncomputable section

/-- The signed coefficient functional is fixed by the actual finite ledger. -/
def coefficient (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ) : ℝ :=
  3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀ - b₁₁

/-- Separate analytic suppliers combine on a common eventual set. Every
entry remains visible as its actual Upsilon, including both same-mask entries.
The loss `epsilon/14` per entry has the exact total cost `epsilon`. -/
theorem eventual_mean_of_eleven_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ)
    (h₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₁ - δ) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₂ - δ) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N ≤ (b₃ + δ) * singularNormalization N)
    (h₄ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon4 N ≤ (b₄ + δ) * singularNormalization N)
    (h₅ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₅ - δ) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₆ - δ) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h₇ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (b₇ + δ) * singularNormalization N)
    (h₈ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (b₈ + δ) * singularNormalization N)
    (h₉ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (b₉ + δ) * singularNormalization N)
    (h₁₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N ≤ (b₁₀ + δ) * singularNormalization N)
    (h₁₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon11 N (E N) ≤ (b₁₁ + δ) * singularNormalization N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ - ε) *
        singularNormalization N ≤ currentChenPairedPrimeSum N (E N) := by
  intro ε hε
  have hδ : 0 < ε / 14 := by linarith
  filter_upwards [h₁ (ε / 14) hδ, h₂ (ε / 14) hδ, h₃ (ε / 14) hδ,
    h₄ (ε / 14) hδ, h₅ (ε / 14) hδ, h₆ (ε / 14) hδ,
    h₇ (ε / 14) hδ, h₈ (ε / 14) hδ, h₉ (ε / 14) hδ,
    h₁₀ (ε / 14) hδ, h₁₁ (ε / 14) hδ]
      with N hN₁ hN₂ hN₃ hN₄ hN₅ hN₆ hN₇ hN₈ hN₉ hN₁₀ hN₁₁
  intro hEven
  have h := currentChenPairedPrimeSum_ge_of_normalized_term_bounds N (E N)
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ (ε / 14)
    (hN₁ hEven) (hN₂ hEven) (hN₃ hEven) (hN₄ hEven)
    (hN₅ hEven) (hN₆ hEven) (hN₇ hEven) (hN₈ hEven)
    (hN₉ hEven) (hN₁₀ hEven) (hN₁₁ hEven)
  convert h using 1 <;> dsimp [coefficient] <;> ring

/-- Consume a coefficient family that has already been assembled term by
term. This retains the numerical reserve above `4*currentC`; it does not
silently replace an adopted coefficient by the endpoint constant. -/
theorem eventual_current_mean_of_coefficient
    (E : ℕ → ℕ × ℕ → Prop) (B : ℝ) (hB : 4 * currentC ≤ B)
    (hTerms : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (B - ε) * singularNormalization N ≤ currentChenPairedPrimeSum N (E N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (4 * currentC - ε) * singularNormalization N ≤
        currentChenPairedPrimeSum N (E N) := by
  intro ε hε
  filter_upwards [hTerms ε hε] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hB ε) hH).trans (hN hEven)

/-- The existing selector-uniform count bridge is applied on the same
eventual set as the mean. This final transport pays two epsilon units on
the weight scale for each of its two losses, and divides by four once. -/
theorem eventual_D12_of_coefficient
    (E : ℕ → ℕ × ℕ → Prop) (B : ℝ) (hB : 4 * currentC ≤ B)
    (hTerms : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (B - ε) * singularNormalization N ≤ currentChenPairedPrimeSum N (E N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - ε) * singularNormalization N ≤ (D12 N : ℝ) := by
  intro ε hε
  have htwo : 0 < 2 * ε := by linarith
  have hmean := eventual_current_mean_of_coefficient E B hB hTerms (2 * ε) htwo
  filter_upwards [hmean,
    eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
      (2 * ε) htwo] with N hN hcount
  intro hEven
  exact currentChen_lower_scale_of_equal_finite_budgets (E N)
    (hN hEven) (hcount (E N))

/-- Original-scale terminal assembly from eleven independently stated
analytic suppliers. No whole-weight lower mean is a hypothesis of this
export. The numerical certificate and analytic suppliers must still be
proved at the adopted original coefficient values before this can be
instantiated as the manuscript's unconditional `current_D12_lower`. -/
theorem eventual_D12_of_eleven_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ)
    (h₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₁ - δ) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₂ - δ) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N ≤ (b₃ + δ) * singularNormalization N)
    (h₄ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon4 N ≤ (b₄ + δ) * singularNormalization N)
    (h₅ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₅ - δ) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₆ - δ) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h₇ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (b₇ + δ) * singularNormalization N)
    (h₈ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (b₈ + δ) * singularNormalization N)
    (h₉ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (b₉ + δ) * singularNormalization N)
    (h₁₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N ≤ (b₁₀ + δ) * singularNormalization N)
    (h₁₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon11 N (E N) ≤ (b₁₁ + δ) * singularNormalization N)
    (hCoefficient : 4 * currentC ≤ coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - ε) * singularNormalization N ≤ (D12 N : ℝ) := by
  apply eventual_D12_of_coefficient E
    (coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) hCoefficient
  exact eventual_mean_of_eleven_suppliers E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁

/-- Joint original last-two-term supplier. The sum is bounded directly;
no individual U10 or U11 endpoint is inferred from a joint certificate. -/
theorem eventual_mean_of_joint_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ : ℝ)
    (h₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₁ - δ) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₂ - δ) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N ≤ (b₃ + δ) * singularNormalization N)
    (h₄ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon4 N ≤ (b₄ + δ) * singularNormalization N)
    (h₅ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₅ - δ) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₆ - δ) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h₇ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (b₇ + δ) * singularNormalization N)
    (h₈ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (b₈ + δ) * singularNormalization N)
    (h₉ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (b₉ + δ) * singularNormalization N)
    (h₁₀₁₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (b₁₀₁₁ + 2 * δ) * singularNormalization N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ 0 - ε) *
        singularNormalization N ≤ currentChenPairedPrimeSum N (E N) := by
  intro ε hε
  have hδ : 0 < ε / 14 := by linarith
  filter_upwards [h₁ (ε / 14) hδ, h₂ (ε / 14) hδ, h₃ (ε / 14) hδ,
    h₄ (ε / 14) hδ, h₅ (ε / 14) hδ, h₆ (ε / 14) hδ,
    h₇ (ε / 14) hδ, h₈ (ε / 14) hδ, h₉ (ε / 14) hδ,
    h₁₀₁₁ (ε / 14) hδ]
      with N hN₁ hN₂ hN₃ hN₄ hN₅ hN₆ hN₇ hN₈ hN₉ hN₁₀₁₁
  intro hEven
  have h := currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds N (E N)
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ (ε / 14)
    (hN₁ hEven) (hN₂ hEven) (hN₃ hEven) (hN₄ hEven)
    (hN₅ hEven) (hN₆ hEven) (hN₇ hEven) (hN₈ hEven)
    (hN₉ hEven) (hN₁₀₁₁ hEven)
  convert h using 1 <;> dsimp [coefficient] <;> ring

/-- Terminal joint-certificate variant, retaining the same N-dependent
mask and exact original endpoint. The analytic inputs stay explicit. -/
theorem eventual_D12_of_joint_suppliers
    (E : ℕ → ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ : ℝ)
    (h₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₁ - δ) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₂ - δ) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon3 N ≤ (b₃ + δ) * singularNormalization N)
    (h₄ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon4 N ≤ (b₄ + δ) * singularNormalization N)
    (h₅ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₅ - δ) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      (b₆ - δ) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h₇ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon7 N ≤ (b₇ + δ) * singularNormalization N)
    (h₈ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon8 N ≤ (b₈ + δ) * singularNormalization N)
    (h₉ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤ (b₉ + δ) * singularNormalization N)
    (h₁₀₁₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon10 N + currentChenUpsilon11 N (E N) ≤
        (b₁₀₁₁ + 2 * δ) * singularNormalization N)
    (hCoefficient : 4 * currentC ≤
      coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Even N →
      (currentC - ε) * singularNormalization N ≤ (D12 N : ℝ) := by
  apply eventual_D12_of_coefficient E
    (coefficient b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ 0) hCoefficient
  exact eventual_mean_of_joint_suppliers E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀₁₁

end
end P5OriginalElevenEventualAssembly
end ImbalancedChen
