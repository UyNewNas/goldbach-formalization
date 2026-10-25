import ImbalancedChen.P5U7TriangularInteriorTest
import ImbalancedChen.ChenPairHarmonicFinite

/-!
# Exact finite U7 ordered-pair overlap and artificial diagonal

SOURCE ONLY / UNCOMPILED. The symmetric square below is an auxiliary
bookkeeping device. Its ordered half is exactly the original marked U7
pair test. Its diagonal uses the squared reciprocal-prime weight, not
`1/phi(p^2)`, and is paid by the existing finite telescoping tail bound.
The original `p₁<p₂` source therefore keeps coefficient one and every
pair label; no `1/2` is inserted into the actual U7 source.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped Classical BigOperators

private def p5U7TriangularSquarePrimes (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun p =>
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ (p : ℝ)

private def p5U7TriangularPairTest (N : ℕ) (p q : ℕ) : ℝ :=
  (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) *
    p5U7TriangularOmegaTest (actualPrimeTupleLog N ![p, q])

private def p5U7TriangularDiagonalTest (N : ℕ) (eta : ℝ) (p : ℕ) : ℝ :=
  let t := Real.log (p : ℝ) / Real.log (N : ℝ)
  if (59 / 250 : ℝ) ≤ t ∧ 3 * t < 1 - eta then
    p5U7TriangularOmegaTest ![t, t]
  else 0

/-- The diagonal correction is the literal square of the prime test
denominator. The fixed margin still enforces the original moving wall. -/
def p5U7TriangularDiagonalCorrection (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ p ∈ p5U7TriangularSquarePrimes N,
    p5U7TriangularDiagonalTest N eta p / ((p : ℝ) - 1) ^ 2

/-- The auxiliary coefficient is symmetric by construction. On either
off-diagonal orientation it uses exactly the ORIGINAL ordered label;
the value at equality is kept separately. -/
private def p5U7TriangularSymmetricCoefficient (N : ℕ) (eta : ℝ)
    (p q : ℕ) : ℝ :=
  if p = q then p5U7TriangularDiagonalTest N eta p / ((p : ℝ) - 1) ^ 2
  else if p < q then
    if (p, q) ∈ p5U7TriangularInteriorPairs N eta then
      p5U7TriangularPairTest N p q else 0
  else if (q, p) ∈ p5U7TriangularInteriorPairs N eta then
    p5U7TriangularPairTest N q p else 0

private theorem p5U7TriangularSymmetricCoefficient_comm (N : ℕ) (eta : ℝ)
    (p q : ℕ) :
    p5U7TriangularSymmetricCoefficient N eta p q =
      p5U7TriangularSymmetricCoefficient N eta q p := by
  unfold p5U7TriangularSymmetricCoefficient
  rcases lt_trichotomy p q with h | h | h
  · simp only [ne_of_lt h, Ne.symm (ne_of_lt h), h, not_lt.mpr h.le,
      if_false, if_true]
  · subst q
    simp
  · simp only [ne_of_gt h, Ne.symm (ne_of_gt h), h, not_lt.mpr h.le,
      if_false, if_true]

private theorem p5U7TriangularPairs_subset_square {N : ℕ} {eta : ℝ}
    {t : ℕ × ℕ} (ht : t ∈ p5U7TriangularInteriorPairs N eta) :
    t ∈ (p5U7TriangularSquarePrimes N ×ˢ p5U7TriangularSquarePrimes N).filter
      (fun t => t.1 < t.2) := by
  obtain ⟨hsel, _hmargin⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc, hlow, horder, _hcap⟩ := Finset.mem_filter.mp hsel
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, hlow⟩,
    Finset.mem_filter.mpr ⟨hq, hlow.trans (by exact_mod_cast horder.le)⟩⟩, horder⟩

/-- The strict ordered part of the auxiliary square is exactly the
original marked-pair Omega test sum, with no product-fibre collapse. -/
theorem p5U7Triangular_ordered_square_eq_source_test (N : ℕ) (eta : ℝ) :
    (∑ t ∈ (p5U7TriangularSquarePrimes N ×ˢ p5U7TriangularSquarePrimes N).filter
      (fun t => t.1 < t.2),
        p5U7TriangularSymmetricCoefficient N eta t.1 t.2) =
      p5U7TriangularInteriorTestSum N eta p5U7TriangularOmegaTest := by
  let S := (p5U7TriangularSquarePrimes N ×ˢ p5U7TriangularSquarePrimes N).filter
    (fun t => t.1 < t.2)
  have hfilter : S.filter (fun t => t ∈ p5U7TriangularInteriorPairs N eta) =
      p5U7TriangularInteriorPairs N eta := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro ht
      exact ⟨p5U7TriangularPairs_subset_square ht, ht⟩
  calc
    _ = ∑ t ∈ S, if t ∈ p5U7TriangularInteriorPairs N eta then
        p5U7TriangularPairTest N t.1 t.2 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have hlt := (Finset.mem_filter.mp ht).2
      simp only [p5U7TriangularSymmetricCoefficient,
        if_neg hlt.ne', if_pos hlt]
    _ = ∑ t ∈ p5U7TriangularInteriorPairs N eta,
        p5U7TriangularPairTest N t.1 t.2 := by
      rw [← Finset.sum_filter, hfilter]
    _ = _ := by rfl

/-- An exact finite half-square formula. The full square and diagonal
are auxiliary; the left side is still the original strict ordered family. -/
theorem p5U7Triangular_source_test_eq_half_square_sub_diagonal
    (N : ℕ) (eta : ℝ) :
    p5U7TriangularInteriorTestSum N eta p5U7TriangularOmegaTest =
      (1 / 2 : ℝ) *
        ((∑ p ∈ p5U7TriangularSquarePrimes N,
          ∑ q ∈ p5U7TriangularSquarePrimes N,
            p5U7TriangularSymmetricCoefficient N eta p q) -
          p5U7TriangularDiagonalCorrection N eta) := by
  have hsym := chen_ordered_half_square (p5U7TriangularSquarePrimes N)
    (p5U7TriangularSymmetricCoefficient N eta)
    (fun p _ q _ => p5U7TriangularSymmetricCoefficient_comm N eta p q)
  rw [p5U7Triangular_ordered_square_eq_source_test] at hsym
  simpa only [p5U7TriangularDiagonalCorrection,
    p5U7TriangularSymmetricCoefficient, if_pos rfl] using hsym

private theorem p5U7TriangularDiagonalTest_abs_le_five
    {N p : ℕ} {eta : ℝ} (hN : 2 ≤ N)
    (heta : 0 ≤ eta) :
    |p5U7TriangularDiagonalTest N eta p| ≤ 5 := by
  unfold p5U7TriangularDiagonalTest
  set t : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)
  split_ifs with ht
  · have ht0 : (0 : ℝ) < t := by linarith only [ht.1]
    have hcap : t ≤ (1 - t) / 2 := by linarith only [ht.2, heta]
    have hs : p5U7OmegaClosedSupport t t := ⟨ht.1, le_rfl, hcap⟩
    have harg : 1 ≤ p5U7OmegaArgument t t :=
      (p5U7Omega_closed_geometry hs).2.2.2.2.1
    have hw0 := LiLiuPrereqBuchstab.buchstab_nonneg harg
    have hw1 := LiLiuPrereqBuchstab.buchstab_le_one harg
    have heq : p5U7TriangularOmegaTest ![t, t] =
        LiLiuPrereqBuchstab.buchstab (p5U7OmegaArgument t t) / t := by
      simp only [p5U7TriangularOmegaTest, p5U7OmegaKernel,
        Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
      field_simp [ht0.ne'] <;> ring
    rw [heq, abs_div, abs_of_nonneg hw0, abs_of_pos ht0]
    have hfive : 1 / t ≤ (5 : ℝ) :=
      (div_le_iff₀ ht0).mpr (by nlinarith only [ht.1])
    exact (div_le_div_of_nonneg_right hw1 ht0.le).trans hfive
  · simp

/-- A quantitative diagonal payment, valid at every N whose actual
lower prime cutoff is at least two. The existing shifted-square tail
bound is applied to the genuine target-excluding prime carrier. -/
theorem p5U7Triangular_diagonal_abs_le_power {N : ℕ} (hN : 2 ≤ N)
    (hcut : (2 : ℝ) ≤ (N : ℝ) ^ (59 / 250 : ℝ))
    (eta : ℝ) (heta : 0 ≤ eta) :
    |p5U7TriangularDiagonalCorrection N eta| ≤
      40 / (N : ℝ) ^ (59 / 250 : ℝ) := by
  unfold p5U7TriangularDiagonalCorrection
  have h := chen_pair_diagonal_tail_bound N (p5U7TriangularSquarePrimes N)
    (p5U7TriangularDiagonalTest N eta) hcut (by norm_num : (0 : ℝ) ≤ 5)
    (by
      intro p hp
      obtain ⟨hcarrier, hlo⟩ := Finset.mem_filter.mp hp
      exact ⟨hlo, (mem_chenAdditivePrimeCarrier.mp hcarrier).1.le⟩)
    (by intro p _; exact p5U7TriangularDiagonalTest_abs_le_five hN heta)
  simpa only [show (8 : ℝ) * 5 = 40 by norm_num] using h

end

end ImbalancedChen
