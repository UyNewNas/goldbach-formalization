import ImbalancedChen.P3ActualU6LowerPairMomentFactor
import ImbalancedChen.P3ActualRawActiveLevelTotientCap
import Mathlib.Tactic

/-!
P3.6, frozen manuscript UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b, PP-completion
§1 (PP), §3 (T), §4 (F), manuscript-body.tex eq:current-PP.

The displayed small Rosser divisor carrier includes inactive terms
above the STRICT level L. The preceding positive quotient-prime moment
factorization used the entire carrier; it therefore cannot import the
active-level totient cap. Here the original INTEGER even-first-exit LOWER
pair coefficient is proved to vanish outside that strict level. We then
restrict its SIGNED physical correction (before absolute values) to the
true active small carrier, retaining the original rough retention policy,
integer rho, original pair labels, b*s*r and the same phi(b*s*r).
Only AFTER that exact restriction do we bound the signed sum by a
positive active small / actual retained rough moment. No estimate for
the resulting moments, arbitrary-log PP discrepancy saving or final
global causal rho_N identification is asserted.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerActivePairPrimeMoment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualU6LowerQuotientPrimeMoments
open ImbalancedChen.P3ActualU6LowerPairMomentFactor

/-- A nonzero ORIGINAL even-exit LOWER integer pair coefficient has
its actual small Rosser factor strictly below L. Both sign branches
are checked against their own literal lower/upper active theorems. -/
theorem actual_even_lower_pair_small_strict_of_ne_zero
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (s r : ℕ)
    (h : actualEvenLowerPairInt retainEven N cap w z L (s, r) ≠ 0) :
    (s : ℝ) < L := by
  have hr : (actualEvenLowerPairInt retainEven N cap w z L (s, r) : ℝ) ≠ 0 := by
    exact_mod_cast h
  rw [actualEvenLowerPairInt_cast] at hr
  unfold smallRoughPairCoefficient signAttachedCoefficient at hr
  have hbeta := (mul_ne_zero_iff.mp hr).2
  by_cases hsign : 0 ≤ fixedEvenRoughCoefficient retainEven N cap w z r
  · have hminus : actualSmallRosserMinus N cap w L s ≠ 0 := by
      simpa [hsign] using hbeta
    exact (actualSmallRosserMinus_active hminus).2.1
  · have hplus : actualSmallRosserPlus N cap w L s ≠ 0 := by
      simpa [hsign] using hbeta
    exact (actualSmallRosserPlus_active hplus).2.1

/-- This equality is of SIGNED sums, not just bounds. In particular
all displayed small factors s>=L disappear because the actual pair
coefficient is zero; no displayed-support level hypothesis is added.
F may depend on BOTH original labels, not only on their product. -/
theorem actual_even_lower_signed_pairs_eq_active
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (F : ℕ × ℕ → ℝ) :
    (∑ x ∈ P5CausalRhoFactorization.pairs retainEven N cap w z,
      (actualEvenLowerPairInt retainEven N cap w z L x : ℝ) * F x) =
    ∑ x ∈ (activeSmallRosserByLevel N cap w L).product
        (fixedEvenRoughSupport retainEven N cap w z),
      (actualEvenLowerPairInt retainEven N cap w z L x : ℝ) * F x := by
  classical
  let S := actualSmallRosserSupport N cap w
  let A := activeSmallRosserByLevel N cap w L
  let R := fixedEvenRoughSupport retainEven N cap w z
  have hsub : A.product R ⊆
      P5CausalRhoFactorization.pairs retainEven N cap w z := by
    change A.product R ⊆ S.product R
    exact Finset.product_mono (Finset.filter_subset _ _) (Finset.Subset.rfl)
  have hzero :
      ∀ x ∈ P5CausalRhoFactorization.pairs retainEven N cap w z,
        x ∉ A.product R →
        (actualEvenLowerPairInt retainEven N cap w z L x : ℝ) * F x = 0 := by
    intro x hx hnot
    have hmem : x ∈ S.product R := hx
    have hcoeff : actualEvenLowerPairInt retainEven N cap w z L x = 0 := by
      by_contra hnz
      have hlt := actual_even_lower_pair_small_strict_of_ne_zero
        retainEven N cap w z L x.1 x.2 hnz
      apply hnot
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).1, hlt⟩,
         (Finset.mem_product.mp hmem).2⟩
    simp [hcoeff]
  exact (Finset.sum_subset hsub hzero).symm

/-- The actual U6 signed quotient-prime remainder, with the same
integer LOWER rho and full physical b*q, has an EXACT restriction to
the genuinely active small factor. No modulus, label or mean is changed. -/
theorem actual_U6_lower_quotient_prime_correction_active
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
    ∑ x ∈ (activeSmallRosserByLevel N cap (w t) (L t)).product
        (fixedEvenRoughSupport (policy t) N cap (w t) z),
      (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
        ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
          (Nat.totient ((b * x.1) * x.2) : ℝ)) := by
  rw [actual_U6_lower_quotient_prime_correction_pair_split
    N t ht policy w L hwz]
  exact actual_even_lower_signed_pairs_eq_active
    (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t)
    (fun x => (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
      (Nat.totient (((t.1 * t.2) * x.1) * x.2) : ℝ))

/-- Unlike the previous full displayed-support positive moment, this
exact active-domain upper bound has only s<L in both small moments.
The actual retained rough first moment remains unmodified, and the
physical prefix b is still divided out only by genuine three-block
coprimality. This is a finite bound, not a log-saving estimate. -/
theorem actual_U6_lower_quotient_prime_correction_abs_le_active_moments
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let A := activeSmallRosserByLevel N cap (w t) (L t)
    let R := fixedEvenRoughSupport (policy t) N cap (w t) z
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    |∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
    (Nat.totient b : ℝ)⁻¹ *
      ((∑ s ∈ A, chenPrimeDivisorCount N s *
          (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, (Nat.totient r : ℝ)⁻¹) +
       (∑ s ∈ A, (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, chenPrimeDivisorCount N r *
          (Nat.totient r : ℝ)⁻¹)) := by
  rw [actual_U6_lower_quotient_prime_correction_active
    N t ht policy w L hwz]
  dsimp
  let z := P5CausalRhoQuotientBridge.cutoff N
  let cap := Nat.ceil z
  let b := t.1 * t.2
  let A := activeSmallRosserByLevel N cap (w t) (L t)
  let R := fixedEvenRoughSupport (policy t) N cap (w t) z
  have hsub : A.product R ⊆
      P5CausalRhoFactorization.pairs (policy t) N cap (w t) z := by
    change A.product R ⊆
      (actualSmallRosserSupport N cap (w t)).product R
    exact Finset.product_mono (Finset.filter_subset _ _) (Finset.Subset.rfl)
  have hblocks : ∀ s ∈ A, ∀ r ∈ R,
      Nat.Coprime b s ∧ Nat.Coprime b r ∧ Nat.Coprime s r := by
    intro s hs r hr
    have hp : (s,r) ∈
        P5CausalRhoFactorization.pairs (policy t) N cap (w t) z :=
      hsub (Finset.mem_product.mpr ⟨hs, hr⟩)
    have h := P5CausalRhoFactorization.original_U6_three_block_data
      ht (policy t) cap (w t) hwz hp
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hpositive :
      |∑ x ∈ A.product R,
        (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
          ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
            (Nat.totient ((b * x.1) * x.2) : ℝ))| ≤
      ∑ x ∈ A.product R,
        (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
          (Nat.totient ((b * x.1) * x.2) : ℝ) := by
    calc
      _ ≤ ∑ x ∈ A.product R,
            |(actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
              ((chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
                (Nat.totient ((b * x.1) * x.2) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hc := P5CausalRhoFactorization.coefficient_abs_le_one
          (policy t) N cap (w t) z (L t) (hsub hx)
        rw [← actualEvenLowerPairInt_eq_P5_coefficient] at hc
        have hpos : 0 ≤
            (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
              (Nat.totient ((b * x.1) * x.2) : ℝ) := by
          unfold chenPrimeDivisorCount
          positivity
        rw [abs_mul, abs_of_nonneg hpos]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hpos
  calc
    _ ≤ ∑ x ∈ A.product R,
      (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
        (Nat.totient ((b * x.1) * x.2) : ℝ) := hpositive
    _ = _ := by
      simpa only [Finset.sum_product, div_eq_mul_inv] using
        (coprime_threeblock_pair_prime_moment N b A R hblocks)

end
end ImbalancedChen.P3ActualEvenLowerActivePairPrimeMoment
