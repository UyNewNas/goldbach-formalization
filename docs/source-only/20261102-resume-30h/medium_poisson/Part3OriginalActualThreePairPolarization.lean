import ImbalancedChen.Part3OriginalActualProductBoundDifferences
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The four values below are polarization parameters, not four phase charts.
The identity is ordered: its kernel need not be Hermitian. Normalizing
each diagonal sequence by 2 leaves coefficient mass 4 per pair, hence
64 for the three independent R, S and n pairs in manuscript module 7.
-/

noncomputable section
open Classical Finset
open scoped BigOperators

namespace ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102

def root4 (e : Fin 4) : ℂ := ![1, Complex.I, -1, -Complex.I] e

theorem norm_root4 (e : Fin 4) : ‖root4 e‖ = 1 := by
  fin_cases e <;> norm_num [root4]

/-- A single coefficient function is used at both endpoints. -/
def diagonal (a b : ℕ → ℂ) (e : Fin 4) (n : ℕ) : ℂ :=
  (a n + root4 e * b n) / 2

theorem diagonal_norm_le_one (a b : ℕ → ℂ) (e : Fin 4)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (n : ℕ) :
    ‖diagonal a b e n‖ ≤ 1 := by
  exact OriginalMediumDoubleLambdaColorWindows20261028.diagonalSequence_norm_le_one
    (a n) (b n) (root4 e) (ha n) (hb n) (norm_root4 e)

/-- The reverse cross term is cancelled algebraically, not identified
with the conjugate of the desired ordered cross term. -/
theorem ordered_pair (a b : ℕ → ℂ) (m n : ℕ) :
    a m * star (b n) =
      ∑ e : Fin 4, root4 e *
        (diagonal a b e m * star (diagonal a b e n)) := by
  simp [Fin.sum_univ_succ, diagonal, root4, Complex.star_def] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

def packetWeight (e f g : Fin 4) : ℂ := root4 e * root4 f * root4 g

def diagonalProduct (a b c d u v : ℕ → ℂ)
    (m1 m2 r1 r2 n1 n2 : ℕ) (e f g : Fin 4) : ℂ :=
  (diagonal a b e m1 * star (diagonal a b e m2)) *
    (diagonal c d f r1 * star (diagonal c d f r2)) *
    (diagonal u v g n1 * star (diagonal u v g n2))

theorem norm_packetWeight (e f g : Fin 4) : ‖packetWeight e f g‖ = 1 := by
  simp only [packetWeight, norm_mul, norm_root4, one_mul]

/-- The exact coefficient charge in the original normalization: no
power of x, smooth divisor, spectral level or h multiplicity appears. -/
theorem packetWeight_total_mass :
    (∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
      ‖packetWeight e f g‖) = (64 : ℝ) := by
  norm_num [norm_packetWeight]

theorem diagonalProduct_norm_le_one (a b c d u v : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hd : ∀ n, ‖d n‖ ≤ 1)
    (hu : ∀ n, ‖u n‖ ≤ 1) (hv : ∀ n, ‖v n‖ ≤ 1)
    (m1 m2 r1 r2 n1 n2 : ℕ) (e f g : Fin 4) :
    ‖diagonalProduct a b c d u v m1 m2 r1 r2 n1 n2 e f g‖ ≤ 1 := by
  have hab1 := diagonal_norm_le_one a b e ha hb m1
  have hab2 := diagonal_norm_le_one a b e ha hb m2
  have hcd1 := diagonal_norm_le_one c d f hc hd r1
  have hcd2 := diagonal_norm_le_one c d f hc hd r2
  have huv1 := diagonal_norm_le_one u v g hu hv n1
  have huv2 := diagonal_norm_le_one u v g hu hv n2
  unfold diagonalProduct
  simp only [norm_mul, norm_star]
  have h1 : ‖diagonal a b e m1‖ * ‖diagonal a b e m2‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hab1 hab2 (norm_nonneg _) zero_le_one
  have h2 : ‖diagonal c d f r1‖ * ‖diagonal c d f r2‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hcd1 hcd2 (norm_nonneg _) zero_le_one
  have h3 : ‖diagonal u v g n1‖ * ‖diagonal u v g n2‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul huv1 huv2 (norm_nonneg _) zero_le_one
  have h12 := mul_le_mul h1 h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using mul_le_mul h12 h3
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1 * 1)

/-- A freely chosen complex kernel Z is carried through unchanged.
In particular neither Hermitian symmetry nor positivity is a premise. -/
theorem three_pairs (a b c d u v : ℕ → ℂ)
    (m1 m2 r1 r2 n1 n2 : ℕ) (Z : ℂ) :
    (a m1 * star (b m2)) * (c r1 * star (d r2)) *
        (u n1 * star (v n2)) * Z =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        packetWeight e f g *
          (diagonalProduct a b c d u v m1 m2 r1 r2 n1 n2 e f g * Z) := by
  rw [ordered_pair a b m1 m2, ordered_pair c d r1 r2,
    ordered_pair u v n1 n2]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  unfold packetWeight diagonalProduct
  ring

/-- Finite source version of the cost. The right side contains the
actual 64 diagonal sums; it is not an assumed spectral estimate. -/
theorem norm_sum_packets_le {ι : Type*} (S : Finset ι)
    (P : ι → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    ‖∑ i ∈ S, ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
      packetWeight e f g * P i e f g‖ ≤
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        ‖∑ i ∈ S, P i e f g‖ := by
  have he : (∑ i ∈ S, ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
      packetWeight e f g * P i e f g) =
      ∑ e : Fin 4, ∑ f : Fin 4, ∑ g : Fin 4,
        packetWeight e f g * (∑ i ∈ S, P i e f g) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e he
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro f hf
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g hg
  simp only [norm_mul, norm_packetWeight, one_mul, le_refl]

theorem norm_double_sum_le_card_mul {ι ν : Type*} (S : Finset ι) (T : Finset ν)
    (P : ι → ν → ℂ) (Z : ℂ)
    (hP : ∀ i ∈ S, ∀ j ∈ T, ‖P i j‖ ≤ 1) :
    ‖∑ i ∈ S, ∑ j ∈ T, P i j * Z‖ ≤
      (S.card : ℝ) * (T.card : ℝ) * ‖Z‖ := by
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, ‖Z‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hP i hi j hj) (norm_nonneg Z)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
