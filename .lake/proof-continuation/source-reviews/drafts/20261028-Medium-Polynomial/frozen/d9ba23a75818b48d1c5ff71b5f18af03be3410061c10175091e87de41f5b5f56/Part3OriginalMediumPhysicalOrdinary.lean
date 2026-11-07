import Mathlib.Tactic

-- Original module distribution-medium-completion-20261010.txt,
-- equations (23), (25), (26), lines 341--403.
-- Pure physical-coefficient algebra; no spectral estimate is an input.

namespace ImbalancedChen.Part3OriginalMediumPhysicalOrdinary

noncomputable section

def C (N R S : ℝ) : ℝ := N * R * S
def D (N R : ℝ) : ℝ := N * R
def Z (S : ℝ) : ℝ := S ^ 2
def U (N R S M : ℝ) : ℝ := N * R ^ 2 * S ^ 3 / M
def H (Q R S M : ℝ) : ℝ := Q * R ^ 2 * S ^ 2 / M
def F (N Q : ℝ) : ℝ := N / Q
def outerFourth (N Q R S : ℝ) : ℝ := N ^ 4 / (Q ^ 4 * R ^ 4 * S ^ 6)
def D0 (N R S M : ℝ) : ℝ := N * R ^ 2 * S / M
def D1 (aθ N Q R S M : ℝ) : ℝ := aθ * N * Q * R ^ 2 * S ^ 5 / (N * M) ^ 2

theorem physical_product (N R S M : ℝ) (hM : M ≠ 0) :
    C N R S * D N R * Z S = (N * M) * U N R S M := by
  dsimp [C, D, Z, U]
  field_simp [hM]
  <;> ring

theorem physical_U_over_Z (N R S M : ℝ) (hM : M ≠ 0) (hS : S ≠ 0) :
    U N R S M / Z S = D0 N R S M := by
  dsimp [U, Z, D0]
  field_simp [hM, hS]
  <;> ring

-- The norm factor 1+H/S is bounded before replacing it by a constant.
-- Here H/S=(Q/N)D0, and the original Q<N strict margin supplies Q≤N.
theorem norm_inflation_le_two {N Q R S M : ℝ}
    (hN : 0 < N) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hS : 0 < S) (hM : 0 < M)
    (hQN : Q ≤ N) (hsmall : D0 N R S M ≤ 1) :
    1 + H Q R S M / S ≤ 2 := by
  have hratio : H Q R S M / S = Q * R ^ 2 * S / M := by
    dsimp [H]
    field_simp [hM.ne', hS.ne']
    <;> ring
  have hc : 0 ≤ R ^ 2 * S / M := by positivity
  have hm := mul_le_mul_of_nonneg_right hQN hc
  rw [hratio]
  dsimp [D0] at hsmall
  nlinarith only [hm, hsmall]

theorem original_norm_le_two_base {N Q R S M : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hR : 0 ≤ R) (hS : 0 < S) (hM : 0 < M)
    (hQN : Q ≤ N) (hsmall : D0 N R S M ≤ 1) :
    (1 + H Q R S M / S) * (H Q R S M * S) ^ 2 * F N Q ≤
      2 * (H Q R S M * S) ^ 2 * F N Q := by
  have hb : 0 ≤ (H Q R S M * S) ^ 2 * F N Q := by
    dsimp [F]
    positivity
  have hm := mul_le_mul_of_nonneg_right
    (norm_inflation_le_two hN hQ.le hR hS hM hQN hsmall) hb
  nlinarith only [hm]

-- This is the physical coefficient calculation behind the ordinary part
-- of (26). Both the constant 4 and the retained |a|/x are explicit.
theorem ordinary_normalized_coefficient (A aθ N Q R S M : ℝ)
    (hN : N ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0) (hS : S ≠ 0) (hM : M ≠ 0) :
    outerFourth N Q R S * (H Q R S M * S) ^ 2 * F N Q * aθ *
        (4 * C N R S * D N R * Z S ^ 2 + A * U N R S M * Z S) =
      (N ^ 2 / Q) ^ 4 * ((4 + A / (N * M)) * D1 aθ N Q R S M) := by
  dsimp [outerFourth, H, F, C, D, Z, U, D1]
  field_simp [hN, hQ, hR, hS, hM]
  <;> ring

-- Before physical substitution, U/ν≤Z and C≤DZ give this bound for
-- each ordinary polynomial coefficient, with no discarded ν weights.
theorem ordinary_coefficient_le {A U C D Z L : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hC : 0 ≤ C) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hL : 0 ≤ L) (hLZ : L ≤ Z) (hCDZ : C ≤ D * Z) :
    C * (L + Z) * (C + D * Z) + A * U * Z ≤
      4 * C * D * Z ^ 2 + A * U * Z := by
  have h1 := mul_le_mul_of_nonneg_left (show L + Z ≤ 2 * Z by linarith) hC
  have h2 : C + D * Z ≤ 2 * D * Z := by linarith
  have hm := mul_le_mul h1 h2 (show 0 ≤ C + D * Z by positivity)
    (show 0 ≤ C * (2 * Z) by positivity)
  nlinarith only [hm]

end
end ImbalancedChen.Part3OriginalMediumPhysicalOrdinary
