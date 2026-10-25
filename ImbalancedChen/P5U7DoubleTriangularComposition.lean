import ImbalancedChen.P5U7TriangularDiagonal
import ImbalancedChen.P5U7InteriorDoublePrimeTest
import ImbalancedChen.PowerErrorBudget

/-!
# Original ordered U7 source from the fixed-margin double-prime test

SOURCE ONLY / UNCOMPILED. The two existing interior modules use different
positive-margin walls: `x₀+2*x₁<1-eta` versus `x₀+(2+eta)*x₁<1`.
This module keeps the latter wall exactly, so that the finite ordered source
is literally the labelled double-prime test. The symmetric square is only
an auxiliary identity; it does not identify marked pairs with products.
The diagonal is paid at the original lower-prime power cutoff.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped Classical BigOperators

def p5U7DoubleTriangularPrimes (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun p =>
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p : ℝ)

private def p5U7DoubleTriangularDiagonalTest (N : ℕ) (eta : ℝ) (p : ℕ) : ℝ :=
  let t := Real.log (p : ℝ) / Real.log (N : ℝ)
  if (59 / 250 : ℝ) ≤ t ∧ t + (2 + eta) * t < 1 then
    p5U7InteriorTest ![t, t]
  else 0

/-- The auxiliary diagonal uses squared reciprocal-prime weights, not
`1/phi(p^2)`. It is absent from the original strict ordered source. -/
def p5U7DoubleTriangularDiagonalCorrection (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ p ∈ p5U7DoubleTriangularPrimes N,
    p5U7DoubleTriangularDiagonalTest N eta p / ((p : ℝ) - 1) ^ 2

private def p5U7DoubleTriangularPairTest (N : ℕ) (p q : ℕ) : ℝ :=
  (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) *
    p5U7InteriorTest (actualPrimeTupleLog N ![p, q])

/-- On either off-diagonal orientation the value is the one original
ordered pair coefficient; equality is kept as a separate correction. -/
def p5U7DoubleTriangularSymmetricCoefficient (N : ℕ) (eta : ℝ)
    (p q : ℕ) : ℝ :=
  if p = q then
    p5U7DoubleTriangularDiagonalTest N eta p / ((p : ℝ) - 1) ^ 2
  else if p < q then
    if (p, q) ∈ p5U7InteriorSelector N eta then
      p5U7DoubleTriangularPairTest N p q else 0
  else if (q, p) ∈ p5U7InteriorSelector N eta then
    p5U7DoubleTriangularPairTest N q p else 0

def p5U7DoubleTriangularHalfSquare (N : ℕ) (eta : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (∑ p ∈ p5U7DoubleTriangularPrimes N,
      ∑ q ∈ p5U7DoubleTriangularPrimes N,
        p5U7DoubleTriangularSymmetricCoefficient N eta p q)

private theorem p5U7DoubleTriangularSymmetricCoefficient_comm
    (N : ℕ) (eta : ℝ) (p q : ℕ) :
    p5U7DoubleTriangularSymmetricCoefficient N eta p q =
      p5U7DoubleTriangularSymmetricCoefficient N eta q p := by
  unfold p5U7DoubleTriangularSymmetricCoefficient
  rcases lt_trichotomy p q with h | h | h
  · simp only [ne_of_lt h, Ne.symm (ne_of_lt h), h, not_lt.mpr h.le,
      if_false, if_true]
  · subst q
    simp
  · simp only [ne_of_gt h, Ne.symm (ne_of_gt h), h, not_lt.mpr h.le,
      if_false, if_true]

private theorem p5U7DoubleTriangularSelector_subset_square {N : ℕ} {eta : ℝ}
    {t : ℕ × ℕ} (ht : t ∈ p5U7InteriorSelector N eta) :
    t ∈ (p5U7DoubleTriangularPrimes N ×ˢ
      p5U7DoubleTriangularPrimes N).filter (fun t => t.1 < t.2) := by
  obtain ⟨hsel, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc, hlow, horder, _⟩ := Finset.mem_filter.mp hsel
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, hlow⟩,
    Finset.mem_filter.mpr ⟨hq, hlow.trans (by exact_mod_cast horder.le)⟩⟩,
    horder⟩

private theorem p5U7DoubleTriangular_ordered_square_eq_labelled
    (N : ℕ) (eta : ℝ) :
    (∑ t ∈ (p5U7DoubleTriangularPrimes N ×ˢ
      p5U7DoubleTriangularPrimes N).filter (fun t => t.1 < t.2),
        p5U7DoubleTriangularSymmetricCoefficient N eta t.1 t.2) =
      p5U7InteriorLabelledTestSum N eta := by
  let S := (p5U7DoubleTriangularPrimes N ×ˢ
    p5U7DoubleTriangularPrimes N).filter (fun t => t.1 < t.2)
  have hfilter : S.filter (fun t => t ∈ p5U7InteriorSelector N eta) =
      p5U7InteriorSelector N eta := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro ht
      exact ⟨p5U7DoubleTriangularSelector_subset_square ht, ht⟩
  calc
    _ = ∑ t ∈ S, if t ∈ p5U7InteriorSelector N eta then
        p5U7DoubleTriangularPairTest N t.1 t.2 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hlt := (Finset.mem_filter.mp ht).2
      simp only [p5U7DoubleTriangularSymmetricCoefficient,
        if_neg hlt.ne', if_pos hlt]
    _ = ∑ t ∈ p5U7InteriorSelector N eta,
        p5U7DoubleTriangularPairTest N t.1 t.2 := by
      rw [← Finset.sum_filter, hfilter]
    _ = _ := by rfl

/-- Exact finite ordered-pair formula on the double-test module's own
fixed-eta interior gate. In particular the ORIGINAL labelled source has
coefficient one, with no unearned symmetry factor. -/
theorem p5U7InteriorLabelledTestSum_eq_half_square_sub_diagonal
    (N : ℕ) (eta : ℝ) :
    p5U7InteriorLabelledTestSum N eta =
      (1 / 2 : ℝ) *
        ((∑ p ∈ p5U7DoubleTriangularPrimes N,
          ∑ q ∈ p5U7DoubleTriangularPrimes N,
            p5U7DoubleTriangularSymmetricCoefficient N eta p q) -
          p5U7DoubleTriangularDiagonalCorrection N eta) := by
  have hsym := chen_ordered_half_square (p5U7DoubleTriangularPrimes N)
    (p5U7DoubleTriangularSymmetricCoefficient N eta)
    (fun p _ q _ => p5U7DoubleTriangularSymmetricCoefficient_comm N eta p q)
  rw [p5U7DoubleTriangular_ordered_square_eq_labelled] at hsym
  simpa only [p5U7DoubleTriangularDiagonalCorrection,
    p5U7DoubleTriangularSymmetricCoefficient, if_pos rfl] using hsym

private theorem p5U7DoubleTriangularDiagonalTest_abs_le_five
    {N p : ℕ} {eta : ℝ} (heta : 0 ≤ eta) :
    |p5U7DoubleTriangularDiagonalTest N eta p| ≤ 5 := by
  unfold p5U7DoubleTriangularDiagonalTest
  set t : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)
  split_ifs with ht
  · have ht0 : (0 : ℝ) < t := by linarith only [ht.1]
    have hmul : 0 ≤ eta * t := mul_nonneg heta ht0.le
    have harg : 1 ≤ (1 - t - t) / t := by
      apply (le_div_iff₀ ht0).mpr
      nlinarith only [ht.2, hmul]
    have hw0 := LiLiuPrereqBuchstab.buchstab_nonneg harg
    have hw1 := LiLiuPrereqBuchstab.buchstab_le_one harg
    have hfive : 1 / t ≤ (5 : ℝ) :=
      (div_le_iff₀ ht0).mpr (by nlinarith only [ht.1])
    simp only [p5U7InteriorTest, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_div, abs_of_nonneg hw0, abs_of_pos ht0]
    exact (div_le_div_of_nonneg_right hw1 ht0.le).trans hfive
  · simp

/-- Quantitative payment for the artificial diagonal. The fixed margin
may be zero or positive; the bound uses the actual lower cutoff. -/
theorem p5U7DoubleTriangular_diagonal_abs_le_power {N : ℕ}
    (hcut : (2 : ℝ) ≤ (N : ℝ) ^ (59 / 250 : ℝ))
    (eta : ℝ) (heta : 0 ≤ eta) :
    |p5U7DoubleTriangularDiagonalCorrection N eta| ≤
      40 / (N : ℝ) ^ (59 / 250 : ℝ) := by
  unfold p5U7DoubleTriangularDiagonalCorrection
  have h := chen_pair_diagonal_tail_bound N (p5U7DoubleTriangularPrimes N)
    (p5U7DoubleTriangularDiagonalTest N eta) hcut
    (by norm_num : (0 : ℝ) ≤ 5)
    (by
      intro p hp
      obtain ⟨hcarrier, hlo⟩ := Finset.mem_filter.mp hp
      exact ⟨hlo, (mem_chenAdditivePrimeCarrier.mp hcarrier).1.le⟩)
    (by intro p _; exact p5U7DoubleTriangularDiagonalTest_abs_le_five heta)
  simpa only [show (8 : ℝ) * 5 = 40 by norm_num] using h

/-- The half-square differs from the coefficient-one original ordered
source by at most the explicitly paid diagonal error. -/
theorem p5U7InteriorLabelledTestSum_half_square_error {N : ℕ}
    (hcut : (2 : ℝ) ≤ (N : ℝ) ^ (59 / 250 : ℝ))
    (eta : ℝ) (heta : 0 ≤ eta) :
    |p5U7InteriorLabelledTestSum N eta -
      (1 / 2 : ℝ) *
        (∑ p ∈ p5U7DoubleTriangularPrimes N,
          ∑ q ∈ p5U7DoubleTriangularPrimes N,
            p5U7DoubleTriangularSymmetricCoefficient N eta p q)| ≤
      40 / (N : ℝ) ^ (59 / 250 : ℝ) := by
  rw [p5U7InteriorLabelledTestSum_eq_half_square_sub_diagonal]
  have hdiag := p5U7DoubleTriangular_diagonal_abs_le_power hcut eta heta
  have hnonneg : (0 : ℝ) ≤ 40 / (N : ℝ) ^ (59 / 250 : ℝ) :=
    le_trans (abs_nonneg _) hdiag
  calc
    _ = (1 / 2 : ℝ) *
        |p5U7DoubleTriangularDiagonalCorrection N eta| := by
          have hrewrite :
              (1 / 2 : ℝ) *
                ((∑ p ∈ p5U7DoubleTriangularPrimes N,
                  ∑ q ∈ p5U7DoubleTriangularPrimes N,
                    p5U7DoubleTriangularSymmetricCoefficient N eta p q) -
                  p5U7DoubleTriangularDiagonalCorrection N eta) -
              (1 / 2 : ℝ) *
                (∑ p ∈ p5U7DoubleTriangularPrimes N,
                  ∑ q ∈ p5U7DoubleTriangularPrimes N,
                    p5U7DoubleTriangularSymmetricCoefficient N eta p q) =
                -(1 / 2 : ℝ) *
                  p5U7DoubleTriangularDiagonalCorrection N eta := by ring
          rw [hrewrite, abs_mul, abs_neg,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 40 / (N : ℝ) ^ (59 / 250 : ℝ) := by linarith

/-- The artificial diagonal vanishes at the original lower-prime
power cutoff; no s-to-one boundary argument is used. -/
theorem tendsto_p5U7DoubleTriangularDiagonalCorrection {eta : ℝ}
    (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7DoubleTriangularDiagonalCorrection N eta)
      atTop (𝓝 0) := by
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ (59 / 250 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 59 / 250)).comp
      tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun N : ℕ =>
      40 / (N : ℝ) ^ (59 / 250 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_nat_log_pow_div_rpow 0
      (by norm_num : (0 : ℝ) < 59 / 250)).const_mul (40 : ℝ)
    have hfun : (fun N : ℕ => 40 / (N : ℝ) ^ (59 / 250 : ℝ)) =
        (fun N : ℕ => (40 : ℝ) *
          ((Real.log (N : ℝ)) ^ 0 / (N : ℝ) ^ (59 / 250 : ℝ))) := by
      funext N
      simp only [pow_zero]
      ring
    rw [hfun]
    simpa only [mul_zero] using h
  have hbound : ∀ᶠ N : ℕ in atTop,
      |p5U7DoubleTriangularDiagonalCorrection N eta| ≤
        40 / (N : ℝ) ^ (59 / 250 : ℝ) := by
    filter_upwards [hpower.eventually (eventually_ge_atTop (2 : ℝ))] with N hcut
    exact p5U7DoubleTriangular_diagonal_abs_le_power hcut eta heta
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hmajor.neg) hmajor
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).1
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).2

/-- The auxiliary half-square has the SAME coefficient-one original Omega
integral as the actual ordered pair test. This uses the double-prime
transport and the explicitly paid diagonal; it does not double the U7
source or remove a moving boundary. -/
theorem tendsto_p5U7DoubleTriangularHalfSquare {eta : ℝ}
    (heta : 0 < eta) :
    Tendsto (fun N : ℕ => p5U7DoubleTriangularHalfSquare N eta)
      atTop (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  have hsource := tendsto_p5U7InteriorLabelledTestSum heta
  have hdiag := (tendsto_p5U7DoubleTriangularDiagonalCorrection heta.le).const_mul
    (1 / 2 : ℝ)
  have hsum := hsource.add hdiag
  have heq (N : ℕ) :
      p5U7DoubleTriangularHalfSquare N eta =
        p5U7InteriorLabelledTestSum N eta +
          (1 / 2 : ℝ) * p5U7DoubleTriangularDiagonalCorrection N eta := by
    rw [p5U7InteriorLabelledTestSum_eq_half_square_sub_diagonal]
    unfold p5U7DoubleTriangularHalfSquare
    ring
  have hlim : Tendsto (fun N : ℕ => p5U7DoubleTriangularHalfSquare N eta)
      atTop (𝓝 (p5U7InteriorOmegaIntegral eta + (1 / 2 : ℝ) * 0)) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall (fun N => (heq N).symm)
  simpa only [mul_zero, add_zero] using hlim

end

end ImbalancedChen
