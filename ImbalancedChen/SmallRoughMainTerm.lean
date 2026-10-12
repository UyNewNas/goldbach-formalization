import ImbalancedChen.SmallRoughAttachment
import Mathlib.Tactic

/-!
# Exact main-term and error reindexing for the small/rough physical weight

This file factors the reciprocal-totient density of the literal physical
coefficient `smallRoughRho` into the sign-sensitive rough sum of the two
small-prime densities. It also pulls the two exact error terms back to the
same displayed small/rough pair carrier. No density or distribution estimate
is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Reciprocal-totient density of a coefficient on a displayed support. -/
def reciprocalTotientDensity (S : Finset ℕ) (beta : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S, beta d / (Nat.totient d : ℝ)

/-- A positive rough coefficient selects the upper small density; a negative
rough coefficient selects the lower small density. -/
def signSensitiveReciprocalTotientDensity
    (rough : Finset ℕ) (roughCoeff : ℕ → ℝ)
    (Dminus Dplus : ℝ) : ℝ :=
  ∑ b ∈ rough,
    roughCoeff b / (Nat.totient b : ℝ) *
      if 0 ≤ roughCoeff b then Dplus else Dminus

/-- First expose the physical density as the original pair-indexed density. -/
theorem physicalDensitySum_smallRoughRho_eq_pairSum
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) =
      ∑ x ∈ smallRoughPairs small rough,
        smallRoughPairCoefficient roughCoeff betaMinus betaPlus x /
          (Nat.totient (x.1 * x.2) : ℝ) := by
  simpa only [physicalDensitySum, div_eq_mul_inv] using
    (sum_smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus
      (fun q => (Nat.totient q : ℝ)⁻¹))

/-- Totient multiplicativity across the strict small/rough cutoff factors the
main density, while preserving the essential sign-sensitive β⁻/β⁺ choice. -/
theorem physicalDensitySum_smallRoughRho_eq_signSensitive
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) =
      signSensitiveReciprocalTotientDensity rough roughCoeff
        (reciprocalTotientDensity small betaMinus)
        (reciprocalTotientDensity small betaPlus) := by
  rw [physicalDensitySum_smallRoughRho_eq_pairSum hsmall hrough]
  unfold smallRoughPairs signSensitiveReciprocalTotientDensity
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hc : 0 ≤ roughCoeff b
  · rw [if_pos hc]
    unfold reciprocalTotientDensity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : a.Coprime b :=
      smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
        (hsmall a ha) (hrough b hb)
    rw [Nat.totient_mul hcop, Nat.cast_mul]
    simp only [smallRoughPairCoefficient, signAttachedCoefficient, if_pos hc]
    rw [mul_comm (Nat.totient a : ℝ) (Nat.totient b : ℝ)]
    exact (div_mul_div_comm _ _ _ _).symm
  · rw [if_neg hc]
    unfold reciprocalTotientDensity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : a.Coprime b :=
      smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
        (hsmall a ha) (hrough b hb)
    rw [Nat.totient_mul hcop, Nat.cast_mul]
    simp only [smallRoughPairCoefficient, signAttachedCoefficient, if_neg hc]
    rw [mul_comm (Nat.totient a : ℝ) (Nat.totient b : ℝ)]
    exact (div_mul_div_comm _ _ _ _).symm

/-- Exact pair-carrier form of the coprime-source correction for the same rho. -/
theorem physicalCoprimeCorrection_smallRoughRho_eq_pairSum
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ)
    (num den N : ℕ) (T : ℝ) :
    physicalCoprimeCorrection num den N T (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) =
      ∑ x ∈ smallRoughPairs small rough,
        smallRoughPairCoefficient roughCoeff betaMinus betaPlus x *
          ((halfProductCoprimeMass num den N T (x.1 * x.2) -
              ((halfProductSource num den N T).card : ℝ)) /
            (Nat.totient (x.1 * x.2) : ℝ)) := by
  unfold physicalCoprimeCorrection
  exact sum_smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus
    (fun q =>
      (halfProductCoprimeMass num den N T q -
        ((halfProductSource num den N T).card : ℝ)) /
          (Nat.totient q : ℝ))

/-- Exact pair-carrier form of the signed primitive-residue error for the same rho. -/
theorem physicalDistributionError_smallRoughRho_eq_pairSum
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (roughCoeff betaMinus betaPlus : ℕ → ℝ)
    (num den N : ℕ) (T : ℝ) :
    physicalDistributionError num den N T (smallRoughModuli small rough)
        (smallRoughRho small rough roughCoeff betaMinus betaPlus) =
      ∑ x ∈ smallRoughPairs small rough,
        smallRoughPairCoefficient roughCoeff betaMinus betaPlus x *
          (halfProductCongruenceMass num den N T (x.1 * x.2) -
            halfProductCoprimeMass num den N T (x.1 * x.2) /
              (Nat.totient (x.1 * x.2) : ℝ)) := by
  unfold physicalDistributionError
  exact sum_smallRoughRho_mul hsmall hrough roughCoeff betaMinus betaPlus
    (fun q =>
      halfProductCongruenceMass num den N T q -
        halfProductCoprimeMass num den N T q / (Nat.totient q : ℝ))

end

end ImbalancedChen
