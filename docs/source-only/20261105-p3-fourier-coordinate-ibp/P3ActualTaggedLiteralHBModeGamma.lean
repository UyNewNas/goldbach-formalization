import ImbalancedChen.P3ActualTaggedUnsortedSameRho
import ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre

/-!
P3.6: ORIGINAL-ID positional finite Fourier modes combined with the LITERAL
ordered rough-Heath--Brown fixed-product fibre, and the ORIGINAL
repeated-label factorial correction. SOURCE_ONLY / UNCOMPILED.

This is an explicit restricted, SEPARATED finite-mode source class:
  W(a,b,d,h) = sum_k amplitude(k) * primeMode_k(a,b,d) * hbMode_k(h).
It does NOT claim that an arbitrary genuine physical W_T already has a
finite or uniformly convergent separated representation. In particular
it does not supply Fourier inversion, the uniform L1/tail, any shifted
divisor moment, actual compiler exhaustiveness, or physical rho_N bounds.

Unlike merely factoring the rough-HB sum, the normalized three-gamma
identity below retains the entire ORIGINAL original-ID source, all
repeated fine-label multiplicities, same integer signed rho, and the
complete physical product primeProd * m in its exact coprime mean.
Pinned manuscript: chen-imbalanced-semiprimes
9731290e8f53cffda44129906cde6a965eaa869b
prime-product-completion sections 2 (HB), 3 (T), 4 (F).
-/

namespace ImbalancedChen.P3ActualTaggedLiteralHBModeGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualTaggedUnsortedSameRho
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
open ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Actual ordered rough-HB occurrence coefficient in one finite
separated Fourier mode; NO product Mobius and NO quotient by a fake
factorial of the HB positions. The integer m is the literal HB product. -/
def literalHBModeFibre {κ : Type*}
    (m j : ℕ) (z y : ℝ) (hbMode : κ → List ℕ → ℂ) (k : κ) : ℂ :=
  ∑ h ∈ factorTuples (2 * (j + 1)) m,
    hbMode k h * roughTupleWeight z y (roles j) h

/-- Fubini for finite separated mode sums and the genuine HB words.
The mode on prime positions is allowed to be an arbitrary complex value;
it need not be a symmetric function of the prime product. -/
theorem literalHB_finite_separated_fibre {κ : Type*}
    (K : Finset κ) (amp primeMode : κ → ℂ)
    (m j : ℕ) (z y : ℝ) (hbMode : κ → List ℕ → ℂ) :
    (∑ h ∈ factorTuples (2 * (j + 1)) m,
      (∑ k ∈ K, (amp k * primeMode k) * hbMode k h) *
        roughTupleWeight z y (roles j) h) =
    ∑ k ∈ K, (amp k * primeMode k) *
      literalHBModeFibre m j z y hbMode k := by
  calc
    _ = ∑ h ∈ factorTuples (2 * (j + 1)) m,
          ∑ k ∈ K, ((amp k * primeMode k) * hbMode k h) *
            roughTupleWeight z y (roles j) h := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_mul]
    _ = ∑ k ∈ K, ∑ h ∈ factorTuples (2 * (j + 1)) m,
          ((amp k * primeMode k) * hbMode k h) *
            roughTupleWeight z y (roles j) h := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold literalHBModeFibre
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

/-- A genuine one-bounded HB mode does not enlarge the ORIGINAL
ordered rough-HB absolute-mass bound. It is a finite coefficient estimate,
not a distribution input or an assertion about all W_T. -/
theorem literalHBModeFibre_norm_le_tau {κ : Type*}
    (m j : ℕ) (z y : ℝ) (hbMode : κ → List ℕ → ℂ) (k : κ)
    (hm : m ≠ 0) (hz : 0 ≤ z)
    (hmode : ∀ h ∈ factorTuples (2 * (j + 1)) m,
      ‖hbMode k h‖ ≤ 1) :
    ‖literalHBModeFibre m j z y hbMode k‖ ≤
      Real.log (m : ℝ) * ((m.divisors.card : ℝ) ^ (2 * (j + 1))) := by
  simpa [literalHBModeFibre, hbPositionalMass] using
    (hbPositionalMass_norm_le_tau m j z y
      (fun _ _ _ h => hbMode k h) [] [] [] 1 hm hz
      (by norm_num) (by simpa using hmode))

/-- Quantitative finite Fourier amplitude payment for the ACTUAL
ordered rough HB fibre, uniform in the finite mode count except through
its explicit L1 amplitude. No m(N) uniformity has been invented. -/
theorem literalHB_mode_amplitude_l1 {κ : Type*}
    (K : Finset κ) (amp : κ → ℂ)
    (m j : ℕ) (z y : ℝ) (hbMode : κ → List ℕ → ℂ)
    (hm : m ≠ 0) (hz : 0 ≤ z)
    (hmode : ∀ k ∈ K, ∀ h ∈ factorTuples (2 * (j + 1)) m,
      ‖hbMode k h‖ ≤ 1) :
    ‖∑ k ∈ K, amp k * literalHBModeFibre m j z y hbMode k‖ ≤
      (∑ k ∈ K, ‖amp k‖) *
        (Real.log (m : ℝ) *
          ((m.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
  calc
    _ ≤ ∑ k ∈ K, ‖amp k * literalHBModeFibre m j z y hbMode k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ K, ‖amp k‖ *
        ‖literalHBModeFibre m j z y hbMode k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul]
    _ ≤ ∑ k ∈ K, ‖amp k‖ *
        (Real.log (m : ℝ) *
          ((m.divisors.card : ℝ) ^ (2 * (j + 1)))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (literalHBModeFibre_norm_le_tau m j z y hbMode k
          hm hz (hmode k hk)) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- Exact normalized three-gamma tensor for original-ID PRIME positions,
combined with the ACTUAL literal rough-HB mode coefficient at fixed
product m. The original M_0*M_1*M_2/M_all restoring scalar remains in
the equation. The complete physical same-signed-rho kernel evaluates
primeProd*m (not primeProd alone); its count and coprime mean are untouched.

This applies ONLY to the finite separated mode class; extending physical
W_T through a quantitatively controlled Fourier integral is still open. -/
theorem tagged_literal_hb_modes_same_rho_tensor
    {n : ℕ} {κ : Type*}
    (K : Finset κ) (amp : κ → ℂ)
    (m j : ℕ) (z y : ℝ) (hbMode : κ → List ℕ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n))
    (eta : κ → Fin n → ℝ) (U : Fin n → ℝ)
    (c : ℂ) (Q : Finset ℕ) (rho : ℕ → ℤ) :
    let pLabel : Fin 3 → ℕ := fun t => label (p t)
    let tailLabel := tail.map label
    let blocks := canonicalFineBlocks
      (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    let S₀ := actualPrimeSlotBox B (ids.1.map label)
    let S₁ := actualPrimeSlotBox B (ids.2.1.map label)
    let S₂ := actualPrimeSlotBox B (ids.2.2.map label)
    (c / (actualPrimeLabelBlocksFactorial blocks : ℂ)) *
      (∑ a ∈ S₀, ∑ b ∈ S₁, ∑ d ∈ S₂,
        (∑ k ∈ K, (amp k * literalHBModeFibre m j z y hbMode k) *
          (positionalGroupMode (eta k) U ids.1 a *
            (positionalGroupMode (eta k) U ids.2.1 b *
              positionalGroupMode (eta k) U ids.2.2 d))) *
        sameRhoFixedProductResponse N (a.prod * b.prod * d.prod) m Q rho) =
    (c * (((actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 0) : ℂ) *
      (actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 1) : ℂ) *
      (actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 2) : ℂ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          (∑ k ∈ K, (amp k * literalHBModeFibre m j z y hbMode k) *
            (physicalComplexLabelGamma B (ids.1.map label)
              (splitBlocks blocks size 0)
              (positionalGroupMode (eta k) U ids.1) a *
             (physicalComplexLabelGamma B (ids.2.1.map label)
              (splitBlocks blocks size 1)
              (positionalGroupMode (eta k) U ids.2.1) b *
              physicalComplexLabelGamma B (ids.2.2.map label)
              (splitBlocks blocks size 2)
              (positionalGroupMode (eta k) U ids.2.2) d))) *
          sameRhoFixedProductResponse N (a * b * d) m Q rho) := by
  exact actual_tagged_unsorted_finite_modes_tensor
    K (fun k => amp k * literalHBModeFibre m j z y hbMode k)
    N τ D A yz upperLabel label p tail eta U c
    (fun r => sameRhoFixedProductResponse N r m Q rho)

end
end ImbalancedChen.P3ActualTaggedLiteralHBModeGamma
