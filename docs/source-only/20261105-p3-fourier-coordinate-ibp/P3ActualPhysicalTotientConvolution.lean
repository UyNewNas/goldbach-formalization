import ImbalancedChen.P3ActualWholeProductMixedTauTransfer
import ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3(T),4(F): a genuine arithmetic improvement
over the previous unestimated physical reciprocal-totient mass.

For a FINITE original small/rough modulus PAIR source, the push-forward
signed coefficient can have multiple representations of one physical q.
No injectivity, positivity of coefficients, squarefreeness, or claimed
factorization of the still-unknown COMPLETE compiler rho_N is assumed.

The pinned Mathlib theorem Nat.totient_super_multiplicative proves that
1/phi(a*b) <= 1/(phi(a)*phi(b)) for positive a,b. Together with exact
noninjective fibre L1 transfer it gives a MULTIPLICATIVE upper bound on
the physical reciprocal-totient mass of such an actual pair convolution.

This is a proper manuscript-INTERNAL finite arithmetic lemma; actual
compiler source admission, the exact same rho_N dictionary, bounds on
each factor mass and any arbitrary-log PP saving remain YELLOW.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualPhysicalTotientConvolution
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWholeProductMixedTauTransfer

/-- The physical modulus is the INTEGER PRODUCT, not an auxiliary
Fourier frequency or independently chosen density level. -/
def pairModulus (x : ℕ × ℕ) : ℕ := x.1 * x.2

/-- True exact signed fibre coefficient, with all pair representations
retained even when the product map is noninjective. -/
def pairConvolution (S : Finset (ℕ × ℕ))
    (c : (ℕ × ℕ) → ℂ) (q : ℕ) : ℂ :=
  ∑ x ∈ S.filter (fun x => pairModulus x = q), c x

/-- This positive mass has the original Euler totient of the FULL
physical modulus q, never a surrogate density coefficient. -/
def physicalComplexTotientMass
    (Q : Finset ℕ) (rho : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖rho q‖ * (Nat.totient q : ℝ)⁻¹

/-- Elementary but substantive factor-modulus arithmetic: the
reciprocal totient is submultiplicative on positive integer factors.
Only the pinned Nat.totient_super_multiplicative is used. -/
theorem reciprocal_totient_product_le
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (Nat.totient (a * b) : ℝ)⁻¹ ≤
      (Nat.totient a : ℝ)⁻¹ * (Nat.totient b : ℝ)⁻¹ := by
  have haφ : 0 < (Nat.totient a : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr ha)
  have hbφ : 0 < (Nat.totient b : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hb)
  have hmul : (Nat.totient a : ℝ) * (Nat.totient b : ℝ) ≤
      (Nat.totient (a * b) : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  have hInv : (Nat.totient (a * b) : ℝ)⁻¹ ≤
      ((Nat.totient a : ℝ) * (Nat.totient b : ℝ))⁻¹ :=
    one_div_le_one_div_of_le (mul_pos haφ hbφ) hmul
  simpa only [mul_inv_rev] using hInv

/-- An actual signed pair source is bounded by its ORIGINAL positive
pair mass after pushing forward to the whole physical modulus. The
only hypotheses are positivity of the literal source moduli; this
does not assume a distribution theorem or a desired error estimate. -/
theorem pair_convolution_physical_mass_le
    (S : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (hpos : ∀ x ∈ S, 0 < x.1 ∧ 0 < x.2) :
    physicalComplexTotientMass (S.image pairModulus)
        (pairConvolution S c) ≤
      ∑ x ∈ S, ‖c x‖ *
        ((Nat.totient x.1 : ℝ)⁻¹ *
         (Nat.totient x.2 : ℝ)⁻¹) := by
  classical
  unfold physicalComplexTotientMass pairConvolution
  calc
    (∑ q ∈ S.image pairModulus,
       ‖∑ x ∈ S.filter (fun x => pairModulus x = q), c x‖ *
         (Nat.totient q : ℝ)⁻¹) ≤
      ∑ x ∈ S, ‖c x‖ *
        (Nat.totient (pairModulus x) : ℝ)⁻¹ :=
      weighted_full_product_fibre_l1_le
        S pairModulus c (fun q => (Nat.totient q : ℝ)⁻¹)
        (by intro q hq; positivity)
    _ ≤ ∑ x ∈ S, ‖c x‖ *
          ((Nat.totient x.1 : ℝ)⁻¹ *
           (Nat.totient x.2 : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pairModulus] using
          reciprocal_totient_product_le x.1 x.2
            (hpos x hx).1 (hpos x hx).2)
        (norm_nonneg _)

/-- When the physical pair coefficient really SEPARATES as alpha(a)
times beta(b), the physical rho/phi mass is bounded by the product of
the two ORIGINAL component totient masses. This is a quantitative
estimate, not another equivalent finite regrouping. -/
theorem separated_physical_totient_mass_le
    (A B : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    physicalComplexTotientMass ((A.product B).image pairModulus)
      (pairConvolution (A.product B)
        (fun x => alpha x.1 * beta x.2)) ≤
      physicalComplexTotientMass A alpha *
        physicalComplexTotientMass B beta := by
  have hpair (x : ℕ × ℕ) (hx : x ∈ A.product B) :
      0 < x.1 ∧ 0 < x.2 := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
    exact ⟨hA x.1 ha, hB x.2 hb⟩
  calc
    _ ≤ ∑ x ∈ A.product B, ‖alpha x.1 * beta x.2‖ *
        ((Nat.totient x.1 : ℝ)⁻¹ *
         (Nat.totient x.2 : ℝ)⁻¹) :=
      pair_convolution_physical_mass_le (A.product B)
        (fun x => alpha x.1 * beta x.2) hpair
    _ = ∑ a ∈ A, ∑ b ∈ B,
        (‖alpha a‖ * (Nat.totient a : ℝ)⁻¹) *
        (‖beta b‖ * (Nat.totient b : ℝ)⁻¹) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [norm_mul]
      ring
    _ = _ := by
      unfold physicalComplexTotientMass
      calc
        (∑ a ∈ A, ∑ b ∈ B,
          (‖alpha a‖ * (Nat.totient a : ℝ)⁻¹) *
          (‖beta b‖ * (Nat.totient b : ℝ)⁻¹)) =
          ∑ a ∈ A,
            (‖alpha a‖ * (Nat.totient a : ℝ)⁻¹) *
              (∑ b ∈ B, ‖beta b‖ * (Nat.totient b : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_mul]

end
end ImbalancedChen.P3ActualPhysicalTotientConvolution
