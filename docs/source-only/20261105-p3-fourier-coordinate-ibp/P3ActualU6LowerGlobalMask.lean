import ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean
import ImbalancedChen.CurrentChenP5CausalRhoFactorization
import Mathlib.Tactic

/-!
P3.6 — source-specific global squarefree/target-coprime mask for the
literal sixth-row even-first-exit LOWER integer coefficient.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§1,3(T),4(F), including (C) global collisions.

The manuscript warns that squarefree within individual HB groups does
not imply global squarefree.  This file proves a strictly narrower fact:
for the actual P5 U6 prefix b=t.1*t.2 and the retained LOWER quotient
source, original production lemmas provide pairwise coprimality of all
THREE physical factors and target N.  Hence the global squarefree and
N-coprimality mask is identically true on this particular source, before
ANY sum is taken. No corresponding claim is made about generic HB groups,
the global final compiler rho_N, or its other source families.

The exact integer LOWER rho, original pair labels, full physical b*q,
complete-product B filter, and true phi(b*q) are preserved.  No PP
count-minus-mean/discrepancy estimate is inferred. No new classic input.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LowerGlobalMask

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean
open ImbalancedChen.P3ActualEvenLowerEulerMass
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment

/-- The full literal U6 arithmetic modulus is squarefree and coprime
with N for every original even-exit LOWER quotient label, not merely
for those whose integer rho coefficient is nonzero. This is specific
to the original U6 three-block source, NOT to arbitrary HB blocks. -/
theorem actual_u6_lower_full_modulus_global_mask
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ}
    (hq : q ∈ actualLowerSmallRoughModuli (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N)) :
    Squarefree ((t.1 * t.2) * q) ∧
      Nat.Coprime ((t.1 * t.2) * q) N := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, r⟩, hpair, rfl⟩
  have hsource :=
    P5CausalRhoFactorization.original_U6_three_block_data
      ht (policy t) (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) hwz hpair
  constructor
  · simpa only [Nat.mul_assoc] using hsource.2.2.2.1
  · simpa only [Nat.mul_assoc] using hsource.2.2.2.2

/-- Keeping the two global masks in the ORIGINAL signed physical
count does not change the U6 lower row.  The signed integer rho and
all literal quotient labels are unchanged. The test F is arbitrary;
there is no distribution or smoothness assumption. -/
theorem actual_u6_lower_masked_signed_count_eq_pairs
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    (F : ℕ → ℝ) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    (∑ q ∈ Q,
      if Squarefree (b * q) ∧ Nat.Coprime (b * q) N then
        (rho q : ℝ) * F (b * q) else 0) =
    ∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
        F ((b * x.1) * x.2) := by
  dsimp
  calc
    (∑ q ∈ actualLowerSmallRoughModuli (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N),
      if Squarefree ((t.1 * t.2) * q) ∧
          Nat.Coprime ((t.1 * t.2) * q) N then
        (actualEvenLowerIntegerRho (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
          F ((t.1 * t.2) * q) else 0) =
      ∑ q ∈ actualLowerSmallRoughModuli (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N),
        (actualEvenLowerIntegerRho (policy t) N
          (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
          (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q : ℝ) *
          F ((t.1 * t.2) * q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact if_pos (actual_u6_lower_full_modulus_global_mask
          N t ht policy w hwz hq)
    _ = _ :=
      actualEvenLowerIntegerRho_prefix_fubini
        (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N)
        (L t) F

/-- The exact complete-product B coprime mean can also retain BOTH
global masks without a correction on the original U6 LOWER support.
The B filter remains (B,b*q)=1, not merely (B,q)=1. -/
theorem actual_u6_lower_masked_prefixed_mean_eq
    (N B : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    prefixedPrimitiveMean B b Q rho =
      ∑ q ∈ Q.filter (fun q => Nat.Coprime B (b * q)),
        if Squarefree (b * q) ∧ Nat.Coprime (b * q) N then
          (rho q : ℂ) * (((Nat.totient (b * q) : ℝ)⁻¹ : ℝ) : ℂ)
        else 0 := by
  dsimp [prefixedPrimitiveMean]
  apply Finset.sum_congr rfl
  intro q hq
  have hqQ := (Finset.mem_filter.mp hq).1
  exact (if_pos (actual_u6_lower_full_modulus_global_mask
    N t ht policy w hwz hqQ)).symm

end
end ImbalancedChen.P3ActualU6LowerGlobalMask
