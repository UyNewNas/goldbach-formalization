import ImbalancedChen.P5OriginalElevenEventualAssembly
import ImbalancedChen.P6RealUpperTerminalAdapter

/-!
# Actual eleven-supplier P5 export into the two current P6 endpoints

The imports name the intended staged module paths of two source-only drafts.
Both endpoints call the actual P5 eleven-supplier assembly, then reuse the
existing terminal theorem. The N-dependent mask, original signed coefficient
inequality, and every individual Upsilon epsilon supplier remain parameters.
All analytic premises remain OPEN; no unconditional estimate is asserted.
-/

namespace ImbalancedChen.P6

noncomputable section

section ElevenSuppliers

variable
    (E : ℕ → ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℝ)
    (h₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (b₁ - δ) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (b₂ - δ) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon3 N ≤ (b₃ + δ) * singularNormalization N)
    (h₄ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon4 N ≤ (b₄ + δ) * singularNormalization N)
    (h₅ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (b₅ - δ) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (b₆ - δ) * singularNormalization N ≤ currentChenUpsilon6 N (E N))
    (h₇ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon7 N ≤ (b₇ + δ) * singularNormalization N)
    (h₈ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon8 N ≤ (b₈ + δ) * singularNormalization N)
    (h₉ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon9 N ≤ (b₉ + δ) * singularNormalization N)
    (h₁₀ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon10 N ≤ (b₁₀ + δ) * singularNormalization N)
    (h₁₁ : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, Even N →
      currentChenUpsilon11 N (E N) ≤ (b₁₁ + δ) * singularNormalization N)
    (hCoefficient : 4 * currentC ≤
      P5OriginalElevenEventualAssembly.coefficient
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁)

include h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hCoefficient

/-- Fixed-b Theorem 1.1 from the actual eleven original P5 suppliers and
the fixed-b real bad-count upper estimate. Every analytic premise is open. -/
theorem current_theorem_1_1_of_P5_eleven_suppliers
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop := by
  have hLower := P5OriginalElevenEventualAssembly.eventual_D12_of_eleven_suppliers
    E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hCoefficient
  exact current_theorem_1_1_of_manuscript_bounds hbLower hbUpper hLower hUpper

/-- The shared three-count current corollary from those same eleven original
P5 suppliers and the all-b real upper estimate. Its analytic inputs are open. -/
theorem current_corollary_simultaneous_of_P5_eleven_suppliers_and_all_real_upper
    (hUpper : ∀ b : ℝ, (1 : ℝ) / 2 < b → b < 1 →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in Filter.atTop, Even N →
          (RealB b N : ℝ) ≤
            (currentK * Real.log (1 / b) + epsilon) *
              singularNormalization N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ) := by
  have hLower := P5OriginalElevenEventualAssembly.eventual_D12_of_eleven_suppliers
    E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hCoefficient
  exact current_corollary_simultaneous_of_all_real_upper hLower hUpper

end ElevenSuppliers

end

end ImbalancedChen.P6
