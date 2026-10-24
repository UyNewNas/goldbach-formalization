import ImbalancedChen.CurrentMainTheorem
import ImbalancedChen.P5OriginalElevenEventualAssembly
import ImbalancedChen.P4BDirectPPUpperAssembly

/-!
# Conditional endpoint from the eleven actual means and the actual PP target

SOURCE ONLY / UNCOMPILED. The P5 and P4B imports are intended staging names
for the source drafts recorded in the companion CP; they are not claimed to
be installed modules in the present checkout.

This theorem consumes the real exports of those drafts. It retains eleven
separate actual Upsilon suppliers and their signed coefficient certificate.
The upper input is the genuine Unit-indexed, rank-two Part3 uniform
prime-product target for the actual attached coefficient and exact ordered
band, together with the actual same-rho density supplier and all attachment,
enumeration-cap and gap hypotheses. Positivity of b follows from b > 1/2.

The conclusion is conditional. The eleven analytic mean suppliers, their
adopted coefficient certificate, P4A's actual density estimate, and P3's PP
estimate and geometric licensing remain OPEN. In particular this theorem
does not license the discontinuous band as a P3 geometric family. It assumes
neither the terminal D12 lower estimate nor the terminal RealB upper estimate.
-/

namespace ImbalancedChen.P6

open Filter

noncomputable section

/-- Assemble the literal manuscript lower limit from the original eleven
actual mean suppliers and the actual rank-two uniform PP input. All analytic
obligations remain visible, including the identical precision-indexed rho
and modulus set on the density and PP sides. -/
theorem current_theorem_1_1_of_eleven_suppliers_actual_density_uniformPP
    {b kappa nu r : ℝ}
    (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
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
    (hkappa : 0 < kappa) (hnu : 0 < nu) (hr : 0 < r)
    (hsieve : nu * r < 1)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hUniformPP : ∀ delta : ℝ, 0 < delta →
      Part3.UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
        (fun N _ => P4BLabelledPairDictionary.W b N
          (manuscriptHalfProductCutoff kappa N))) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop := by
  have hb : 0 < b := by linarith
  apply current_theorem_1_1_of_manuscript_bounds hbLower hbUpper
  · exact P5OriginalElevenEventualAssembly.eventual_D12_of_eleven_suppliers
      E b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
      h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ hCoefficient
  · exact P4BDirectPPUpperAssembly.eventually_RealB_le_currentK_log_of_actual_density_uniformPP
      (b := b) (kappa := kappa) (nu := nu) (r := r)
      hb hbUpper hkappa hnu hr hsieve hgap
      epsilon retain cap hepsilon hcap hdensity hUniformPP

end

end ImbalancedChen.P6
