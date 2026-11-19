import ImbalancedChen.P3ActualU6LowerModulusPrimeSplit
import ImbalancedChen.P3ActualEvenLowerIntegerRho
import Mathlib.Tactic

/-!
P3.6, frozen manuscript UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §1 (PP) and manuscript-body.tex eq:current-PP.

After the exact prefix-versus-quotient modulus-prime split, split the
REMAINING quotient correction across the actual SMALL Rosser and EVEN
first-exit ROUGH factors. This uses the original P5 U6 three-block
coprimality, actual signed integer LOWER coefficient, and original pair
labels; it does not treat q as a prime, replace phi(b*q) by phi(q), or
assume a cancellation estimate. The final finite positive pair moment
is an explicit internal budget still to be controlled, not an external
input, a logarithmic saving, or a completed PP bound.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LowerQuotientPrimeMoments

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6LowerModulusPrimeSplit

/-- Every *original* U6 lower pair has a disjoint three-factor prime
support at its genuine physical modulus. The result is NOT asserted for
arbitrary HB grouped words or for the final causal rho_N. -/
theorem original_U6_lower_threeblock_prime_count
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    {x : ℕ × ℕ}
    (hx : x ∈ P5CausalRhoFactorization.pairs (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N)) :
    chenPrimeDivisorCount N (((t.1 * t.2) * x.1) * x.2) =
      chenPrimeDivisorCount N (t.1 * t.2) +
        chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2 := by
  have hblocks := P5CausalRhoFactorization.original_U6_three_block_data
    ht (policy t) (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (w t) hwz hx
  have hbr : Nat.Coprime ((t.1 * t.2) * x.1) x.2 :=
    Nat.coprime_mul_iff_left.mpr ⟨hblocks.2.1, hblocks.2.2.1⟩
  rw [prime_divisor_count_coprime_mul N ((t.1 * t.2) * x.1) x.2 hbr,
    prime_divisor_count_coprime_mul N (t.1 * t.2) x.1 hblocks.1]

/-- The *unpaid* quotient-prime term on the ORIGINAL integer U6 LOWER
rho is exactly two signed source moments, one for the active small
Rosser factor and one for the even retained rough factor. The full
physical phi(b*s*r), original retention policy, labels and multiplicity
are unchanged. No absolute value has been inserted before the equality. -/
theorem actual_U6_lower_quotient_prime_correction_pair_split
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    (∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))) =
    ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
        ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
          (Nat.totient ((b * x.1) * x.2) : ℝ)) := by
  have hsplit := actual_U6_lower_modulus_prime_correction_split
    N t ht policy w L hwz
  have hfull := actualEvenLowerIntegerRho_prefix_fubini
    (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N)
    (L t) (fun d => chenPrimeDivisorCount N d / (Nat.totient d : ℝ))
  have hmean := actualEvenLowerIntegerRho_prefix_fubini
    (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N)
    (L t) (fun d => (Nat.totient d : ℝ)⁻¹)
  dsimp at hsplit hfull hmean ⊢
  simp_rw [div_eq_mul_inv] at hsplit hfull hmean ⊢
  calc
    (∑ q ∈ actualLowerSmallRoughModuli (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
      (P5CausalRhoQuotientBridge.cutoff N),
      (actualEvenLowerIntegerRho (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
        (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
        (chenPrimeDivisorCount N q *
          (Nat.totient ((t.1 * t.2) * q) : ℝ)⁻¹)) =
      (∑ q ∈ actualLowerSmallRoughModuli (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
        (P5CausalRhoQuotientBridge.cutoff N),
        (actualEvenLowerIntegerRho (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
          (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
          (chenPrimeDivisorCount N ((t.1 * t.2) * q) *
            (Nat.totient ((t.1 * t.2) * q) : ℝ)⁻¹)) -
        chenPrimeDivisorCount N (t.1 * t.2) *
          (∑ q ∈ actualLowerSmallRoughModuli (policy t) N
            (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
            (P5CausalRhoQuotientBridge.cutoff N),
            (actualEvenLowerIntegerRho (policy t) N
              (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (w t)
              (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
              (Nat.totient ((t.1 * t.2) * q) : ℝ)⁻¹) := by
        rw [hsplit]
        ring
    _ =
      (∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N),
          (actualEvenLowerPairInt (policy t) N
            (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
            (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ) *
            (chenPrimeDivisorCount N (((t.1 * t.2) * x.1) * x.2) *
              (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ)⁻¹)) -
        chenPrimeDivisorCount N (t.1 * t.2) *
          (∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N
            (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
            (w t) (P5CausalRhoQuotientBridge.cutoff N),
            (actualEvenLowerPairInt (policy t) N
              (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
              (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ) *
              (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ)⁻¹) := by
        rw [hfull, hmean]
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [original_U6_lower_threeblock_prime_count
        N t ht policy w hwz hx]
      ring

/-- A genuinely positive, finite, fully labelled moment budget for
this particular quotient-prime correction. Unlike an arithmetic
PP saving, this is only a noncancelling absolute-value bound. -/
theorem actual_U6_lower_quotient_prime_correction_abs_le_pair_moment
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    |∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
    ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
        (Nat.totient ((b * x.1) * x.2) : ℝ) := by
  rw [actual_U6_lower_quotient_prime_correction_pair_split
    N t ht policy w L hwz]
  dsimp
  calc
    |∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N),
      (actualEvenLowerPairInt (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ) *
        ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
          (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ))| ≤
        ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N),
        |(actualEvenLowerPairInt (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ) *
          ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
            (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have hcoeff := P5CausalRhoFactorization.coefficient_abs_le_one
        (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) hx
      rw [← actualEvenLowerPairInt_eq_P5_coefficient] at hcoeff
      have hpos : 0 ≤
          (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
            (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ) := by
        unfold chenPrimeDivisorCount
        positivity
      rw [abs_mul, abs_of_nonneg hpos]
      calc
        |(actualEvenLowerPairInt (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) x : ℝ)| *
          ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
            (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ)) ≤
          1 * ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
            (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff hpos
        _ = _ := by ring

end
end ImbalancedChen.P3ActualU6LowerQuotientPrimeMoments
