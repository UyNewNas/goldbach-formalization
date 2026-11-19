import ImbalancedChen.P3ActualU6LowerQuotientPrimeMoments
import Mathlib.Tactic

/-!
P3.6, frozen manuscript UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §1 (PP), §3 (T), §4 (F),
and manuscript-body.tex eq:current-PP.

Factor the precise noncancelling ORIGINAL U6 even-first-exit LOWER
quotient-prime moment from the previous packet into TWO separately
weighted actual small/rough supports. The full arithmetic modulus
remains (t.1*t.2)*s*r. Original production three-block coprimality,
not arbitrary independence, supplies exact multiplicativity of phi.
No estimate, arbitrary-log saving, rho_N identification, or external
hypothesis is inferred from the factorization.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LowerPairMomentFactor
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6LowerQuotientPrimeMoments

/-- Finite three-block weighted totient factorization. This is exact
only on the stated PAIRWISE coprime domain; in particular no formula
with phi(b*s*r)=phi(b)*phi(s)*phi(r) is asserted for collisions. -/
theorem coprime_threeblock_pair_prime_moment
    (N b : ℕ) (S R : Finset ℕ)
    (hblocks : ∀ s ∈ S, ∀ r ∈ R,
      Nat.Coprime b s ∧ Nat.Coprime b r ∧ Nat.Coprime s r) :
    (∑ s ∈ S, ∑ r ∈ R,
      (chenPrimeDivisorCount N s + chenPrimeDivisorCount N r) *
        (Nat.totient ((b * s) * r) : ℝ)⁻¹) =
    (Nat.totient b : ℝ)⁻¹ *
      ((∑ s ∈ S, chenPrimeDivisorCount N s *
          (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, (Nat.totient r : ℝ)⁻¹) +
       (∑ s ∈ S, (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, chenPrimeDivisorCount N r *
          (Nat.totient r : ℝ)⁻¹)) := by
  classical
  have hphi (s : ℕ) (hs : s ∈ S) (r : ℕ) (hr : r ∈ R) :
      (Nat.totient ((b * s) * r) : ℝ)⁻¹ =
        (Nat.totient b : ℝ)⁻¹ *
          (Nat.totient s : ℝ)⁻¹ *
          (Nat.totient r : ℝ)⁻¹ := by
    have hb := hblocks s hs r hr
    have hbsr : Nat.Coprime (b * s) r :=
      Nat.coprime_mul_iff_left.mpr ⟨hb.2.1, hb.2.2⟩
    simp only [Nat.totient_mul hbsr, Nat.totient_mul hb.1,
      Nat.cast_mul, mul_inv_rev]
    ring
  calc
    (∑ s ∈ S, ∑ r ∈ R,
      (chenPrimeDivisorCount N s + chenPrimeDivisorCount N r) *
        (Nat.totient ((b * s) * r) : ℝ)⁻¹) =
      (Nat.totient b : ℝ)⁻¹ *
        (∑ s ∈ S, ∑ r ∈ R,
          (chenPrimeDivisorCount N s *
            (Nat.totient s : ℝ)⁻¹) * (Nat.totient r : ℝ)⁻¹ +
          (Nat.totient s : ℝ)⁻¹ *
            (chenPrimeDivisorCount N r * (Nat.totient r : ℝ)⁻¹)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      rw [hphi s hs r hr]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum]

/-- The literal original U6 supports are exactly those of the even
first-exit LOWER producer. Retain each source pair's full physical
modulus and use P5's genuine (b,s), (b,r), (s,r) coprimality. -/
theorem actual_U6_lower_positive_pair_moment_factor
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let S := actualSmallRosserSupport N cap (w t)
    let R := fixedEvenRoughSupport (policy t) N cap (w t) z
    (∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (chenPrimeDivisorCount N x.1 + chenPrimeDivisorCount N x.2) /
        (Nat.totient ((b * x.1) * x.2) : ℝ)) =
    (Nat.totient b : ℝ)⁻¹ *
      ((∑ s ∈ S, chenPrimeDivisorCount N s *
          (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, (Nat.totient r : ℝ)⁻¹) +
       (∑ s ∈ S, (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, chenPrimeDivisorCount N r *
          (Nat.totient r : ℝ)⁻¹)) := by
  dsimp
  let z := P5CausalRhoQuotientBridge.cutoff N
  let cap := Nat.ceil z
  let b := t.1 * t.2
  let S := actualSmallRosserSupport N cap (w t)
  let R := fixedEvenRoughSupport (policy t) N cap (w t) z
  have hblocks (s : ℕ) (hs : s ∈ S) (r : ℕ) (hr : r ∈ R) :
      Nat.Coprime b s ∧ Nat.Coprime b r ∧ Nat.Coprime s r := by
    have hp : (s, r) ∈
        P5CausalRhoFactorization.pairs (policy t) N cap (w t) z := by
      exact Finset.mem_product.mpr ⟨hs, hr⟩
    have h := P5CausalRhoFactorization.original_U6_three_block_data
      ht (policy t) cap (w t) hwz hp
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  rw [P5CausalRhoFactorization.pairs, Finset.sum_product]
  simp only [div_eq_mul_inv]
  exact coprime_threeblock_pair_prime_moment N b S R hblocks

/-- The still-unpaid original signed quotient-prime correction is now
bounded by two separate actual source moments. The small and rough
factor occurrences and the true prefix reciprocal phi(b) are retained;
no rank/prime-counting estimate or absolute logarithmic saving follows. -/
theorem actual_U6_lower_quotient_prime_correction_abs_le_separated
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let S := actualSmallRosserSupport N cap (w t)
    let R := fixedEvenRoughSupport (policy t) N cap (w t) z
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    |∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
    (Nat.totient b : ℝ)⁻¹ *
      ((∑ s ∈ S, chenPrimeDivisorCount N s *
          (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, (Nat.totient r : ℝ)⁻¹) +
       (∑ s ∈ S, (Nat.totient s : ℝ)⁻¹) *
        (∑ r ∈ R, chenPrimeDivisorCount N r *
          (Nat.totient r : ℝ)⁻¹)) := by
  exact (actual_U6_lower_quotient_prime_correction_abs_le_pair_moment
    N t ht policy w L hwz).trans_eq
    (actual_U6_lower_positive_pair_moment_factor N t ht policy w hwz)

end
end ImbalancedChen.P3ActualU6LowerPairMomentFactor
