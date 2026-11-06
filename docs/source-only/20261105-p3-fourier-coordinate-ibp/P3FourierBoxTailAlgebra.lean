import ImbalancedChen.P3FourierCauchyTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
P3.6 SOURCE_ONLY UNCOMPILED. Finite separated Fourier H-box mass algebra.
The physical frequency is xi=2*pi*eta. These are actual scalar power
inequalities, NOT yet the multidimensional product measure or Fubini
integrals of the original geometric W_T. No PP discrepancy is assumed.
Includes the zero-dimensional edge case and exact 2*pi normalization.
-/

namespace ImbalancedChen.P3FourierBoxTailAlgebra
noncomputable section
open P3FourierCauchyAxis P3FourierCauchyTail

private theorem unit_pow_le_one (a : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : a ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a ^ (n + 1) = a ^ n * a := by rw [pow_succ]
        _ ≤ 1 * a := mul_le_mul_of_nonneg_right ih ha
        _ ≤ 1 := by simpa using ha1

/-- Full minus inside product mass, without an exponential loss. -/
theorem pow_gap_le_linear (a b : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ n - b ^ n ≤ (n : ℝ) * (a - b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hbpow : b ^ n ≤ 1 :=
        unit_pow_le_one b n hb (hba.trans ha1)
      have hgap : 0 ≤ a - b := sub_nonneg.mpr hba
      have hco : 0 ≤ (n : ℝ) * (a - b) :=
        mul_nonneg (Nat.cast_nonneg n) hgap
      have hco' : a * ((n : ℝ) * (a - b)) ≤ (n : ℝ) * (a - b) := by
        calc
          a * ((n : ℝ) * (a - b)) ≤
              1 * ((n : ℝ) * (a - b)) :=
            mul_le_mul_of_nonneg_right ha1 hco
          _ = (n : ℝ) * (a - b) := one_mul _
      calc
        a ^ (n + 1) - b ^ (n + 1) =
            a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
        _ ≤ a * ((n : ℝ) * (a - b)) + (a - b) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ih ha)
            (mul_le_mul_of_nonneg_left hbpow hgap)
        _ ≤ (n : ℝ) * (a - b) + (a - b) := by nlinarith [hco']
        _ = ((n + 1 : ℕ) : ℝ) * (a - b) := by push_cast; ring

/-- Scalar eta-normalized outside mass; identification with a genuine
half-space integral remains a separate measure-theoretic task. -/
def normalizedAxisRemoved (H : ℝ) : ℝ :=
  axisPairTail H / (2 * Real.pi)

def normalizedAxisInside (H : ℝ) : ℝ :=
  (1 / 2 : ℝ) - normalizedAxisRemoved H

theorem normalizedAxisRemoved_bounds {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ normalizedAxisRemoved H ∧
      normalizedAxisRemoved H ≤ (1 / 2 : ℝ) := by
  have htail : 0 ≤ axisPairTail H := axisPairTail_nonneg H
  have htail_pi : axisPairTail H ≤ Real.pi := by
    rw [axisPairTail_exact]
    have ha : 0 ≤ Real.arctan H := Real.arctan_nonneg.mpr hH
    linarith
  have hden : 0 < (2 * Real.pi : ℝ) := by positivity
  constructor
  · exact div_nonneg htail hden.le
  · unfold normalizedAxisRemoved
    apply (div_le_iff₀ hden).2
    nlinarith

theorem normalizedAxisRemoved_le_inv {H : ℝ} (hH : 0 < H) :
    normalizedAxisRemoved H ≤ 1 / H := by
  have htail_mul : axisPairTail H * H ≤ 2 :=
    (le_div_iff₀ hH).mp (axisPairTail_le_two_div H hH)
  have hpi : 1 ≤ Real.pi := by
    have hp := Real.pi_gt_three
    linarith
  have hden : 0 < (2 * Real.pi : ℝ) := by positivity
  unfold normalizedAxisRemoved
  apply (le_div_iff₀ hH).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Separated scalar mass loss; NOT yet the Euclidean H-box integral. -/
def separatedBoxMassLoss (d : ℕ) (H : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ d - (normalizedAxisInside H) ^ d

theorem separatedBoxMassLoss_le_dim_div (d : ℕ) {H : ℝ}
    (hH : 0 < H) :
    separatedBoxMassLoss d H ≤ (d : ℝ) / H := by
  obtain ⟨ht0, ht1⟩ := normalizedAxisRemoved_bounds hH.le
  have hb0 : 0 ≤ normalizedAxisInside H := by
    unfold normalizedAxisInside
    linarith
  have hb1 : normalizedAxisInside H ≤ (1 / 2 : ℝ) := by
    unfold normalizedAxisInside
    linarith
  have hp := pow_gap_le_linear (1 / 2 : ℝ)
    (normalizedAxisInside H) d (by norm_num) (by norm_num) hb0 hb1
  have hgap : (1 / 2 : ℝ) - normalizedAxisInside H =
      normalizedAxisRemoved H := by
    unfold normalizedAxisInside
    ring
  have hpow : separatedBoxMassLoss d H ≤
      (d : ℝ) * normalizedAxisRemoved H := by
    simpa only [separatedBoxMassLoss, hgap] using hp
  calc
    separatedBoxMassLoss d H ≤ (d : ℝ) * normalizedAxisRemoved H := hpow
    _ ≤ (d : ℝ) * (1 / H) :=
      mul_le_mul_of_nonneg_left
        (normalizedAxisRemoved_le_inv hH) (Nat.cast_nonneg d)
    _ = (d : ℝ) / H := by ring

theorem separatedBoxMassLoss_budget (d : ℕ) {H D : ℝ}
    (hH : 0 < H) (hD : 0 ≤ D) :
    D * separatedBoxMassLoss d H ≤ (d : ℝ) * D / H := by
  calc
    D * separatedBoxMassLoss d H ≤ D * ((d : ℝ) / H) :=
      mul_le_mul_of_nonneg_left (separatedBoxMassLoss_le_dim_div d hH) hD
    _ = (d : ℝ) * D / H := by ring

theorem separatedBoxMassLoss_spend (d : ℕ) {H D eps : ℝ}
    (hH : 0 < H) (hD : 0 ≤ D)
    (hcut : (d : ℝ) * D ≤ eps * H) :
    D * separatedBoxMassLoss d H ≤ eps := by
  exact (separatedBoxMassLoss_budget d hH hD).trans
    ((div_le_iff₀ hH).mpr hcut)

end
end ImbalancedChen.P3FourierBoxTailAlgebra
