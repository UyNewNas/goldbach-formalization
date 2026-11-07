import ImbalancedChen.P5OriginalElevenEventualAssembly
import ImbalancedChen.P4BActualOuterUpperAssembly
import ImbalancedChen.CurrentMainTheorem

/-!
# Actual P4B/P5 supplier call at the frozen original main endpoint

Source-only cross-group adapter. Every outstanding analytic input appears on
its actual Upsilon or its identical attached coefficient and outer source.
There is no hypothesis directly asserting the desired D12 lower bound or
RealB upper bound. This theorem remains conditional on all displayed analytic
suppliers and the original coefficient inequality; it is not the manuscript's
unconditional current_theorem_1_1.
-/

namespace ImbalancedChen.P6

open Filter
open scoped BigOperators
noncomputable section

theorem current_theorem_1_1_of_actual_P4B_outer_P5_eleven
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
    (hCoefficient : 4 * currentC ≤
      P5OriginalElevenEventualAssembly.coefficient
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁)
    {b kappa nu r : ℝ}
    (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (S : ℝ → ℕ → Finset ℕ) (weight : ℝ → ℕ → ℕ → ℝ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcover : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hgeometry : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∀ m ∈ S delta N, m ≤ N) ∧
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S delta N ∧
      (∀ m ∈ S delta N,
        (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
          then (1 : ℝ) else 0) ≤ weight delta N m))
    (hsurplus : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S delta N) (weight delta N) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (S delta N) (weight delta N) d -
              finiteSourceMass (S delta N) (weight delta N)) / (Nat.totient d : ℝ))| ≤
        delta * singularNormalization N)
    (hprimitive : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          finitePrimitiveDiscrepancy (S delta N) (weight delta N) N d| ≤
        delta * singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop := by
  have hb : 0 < b := lt_trans (by norm_num) hbLower
  have hLower := P5OriginalElevenEventualAssembly.eventual_D12_of_eleven_suppliers
    E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hCoefficient
  have hUpper := P4B.eventually_RealB_le_of_actual_outer_primitive_inputs
    hb hbUpper hkappa hnu hr hsieve epsilon retain cap S weight
    hepsilon hcover hgeometry hsurplus hdensity hcoprime hprimitive
  exact current_theorem_1_1_of_manuscript_bounds hbLower hbUpper hLower hUpper

end
end ImbalancedChen.P6
