import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Order-three Heath--Brown identity on the original group scale

The cutoff may be real. Convolution multiplies the vanishing thresholds,
so the cubic remainder vanishes up to the cube of the actual cutoff.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset
open scoped ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- The truncated Möbius factor in the original order-three identity. -/
def heathBrownTruncatedMoebius (z : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ z then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

@[simp]
theorem heathBrownTruncatedMoebius_apply (z : ℝ) (n : ℕ) :
    heathBrownTruncatedMoebius z n = if (n : ℝ) ≤ z then (ArithmeticFunction.moebius n : ℝ) else 0 :=
  rfl

/-- The remainder between the Dirichlet identity and the truncated inverse. -/
def heathBrownRemainder (z : ℝ) : ArithmeticFunction ℝ :=
  1 - (ζ : ArithmeticFunction ℝ) * heathBrownTruncatedMoebius z

/-- A divisor of an integer below the cutoff lies below the same cutoff,
so truncation does not affect the Dirichlet inverse there. -/
theorem heathBrownRemainder_apply_eq_zero {z : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ z) :
    heathBrownRemainder z n = 0 := by
  change (1 : ArithmeticFunction ℝ) n - ((ζ : ArithmeticFunction ℝ) *
    heathBrownTruncatedMoebius z) n = 0
  apply sub_eq_zero.mpr
  have hinv := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
  rw [← hinv, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
  have hdle : (d : ℝ) ≤ z := (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)).trans hn
  simp only [heathBrownTruncatedMoebius_apply, if_pos hdle, ArithmeticFunction.intCoe_apply]

private theorem dirichlet_mul_apply_eq_zero_of_cutoffs
    {f g : ArithmeticFunction ℝ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hf : ∀ i : ℕ, (i : ℝ) ≤ u → f i = 0)
    (hg : ∀ j : ℕ, (j : ℝ) ≤ v → g j = 0)
    {n : ℕ} (hn : (n : ℝ) ≤ u * v) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases htu : (t.1 : ℝ) ≤ u
  · rw [hf _ htu, zero_mul]
  by_cases htv : (t.2 : ℝ) ≤ v
  · rw [hg _ htv, mul_zero]
  have ht2 : 0 < (t.2 : ℝ) := hv.trans_lt (lt_of_not_ge htv)
  have htprod : (t.1 : ℝ) * (t.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp ht).1
  have hlt : u * v < (n : ℝ) := calc
    _ ≤ u * (t.2 : ℝ) := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge htv)) hu
    _ < (t.1 : ℝ) * (t.2 : ℝ) := mul_lt_mul_of_pos_right (lt_of_not_ge htu) ht2
    _ = _ := htprod
  exact (hn.not_gt hlt).elim

/-- The third convolution power of the remainder vanishes through z cubed. -/
theorem heathBrownRemainder_cube_apply_eq_zero {z : ℝ} (hz : 0 ≤ z) {n : ℕ}
    (hn : (n : ℝ) ≤ z ^ 3) : (heathBrownRemainder z ^ 3) n = 0 := by
  have hsq (m : ℕ) (hm : (m : ℝ) ≤ z ^ 2) : (heathBrownRemainder z ^ 2) m = 0 := by
    rw [pow_two]
    exact dirichlet_mul_apply_eq_zero_of_cutoffs hz hz
      (fun _ h => heathBrownRemainder_apply_eq_zero h)
      (fun _ h => heathBrownRemainder_apply_eq_zero h) (by simpa only [pow_two] using hm)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
  exact dirichlet_mul_apply_eq_zero_of_cutoffs (pow_nonneg hz _) hz hsq
    (fun _ h => heathBrownRemainder_apply_eq_zero h) (by simpa only [pow_succ z 2] using hn)

/-- The exact three-term signed expression in the truncated factors. -/
def heathBrownThree (z : ℝ) (n : ℕ) : ℝ :=
  let M := heathBrownTruncatedMoebius z
  3 * (M * ArithmeticFunction.log) n -
    3 * (M ^ 2 * (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.log) n +
      (M ^ 3 * (ζ : ArithmeticFunction ℝ) ^ 2 * ArithmeticFunction.log) n

private theorem heathBrown_three_ring (z : ℝ) :
    Λ - Λ * heathBrownRemainder z ^ 3 =
      (3 : ArithmeticFunction ℝ) * (heathBrownTruncatedMoebius z * ArithmeticFunction.log) -
      (3 : ArithmeticFunction ℝ) * (heathBrownTruncatedMoebius z ^ 2 *
        (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.log) +
      heathBrownTruncatedMoebius z ^ 3 * (ζ : ArithmeticFunction ℝ) ^ 2 * ArithmeticFunction.log := by
  rw [heathBrownRemainder, ← ArithmeticFunction.vonMangoldt_mul_zeta]
  ring

private theorem arithThreeMul_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    ((3 : ArithmeticFunction ℝ) * f) n = 3 * f n := by
  rw [show (3 : ArithmeticFunction ℝ) = 1 + 1 + 1 by norm_num, add_mul, add_mul]
  simp only [one_mul, ArithmeticFunction.add_apply]
  ring

/-- The exact order-three Heath--Brown identity below the cutoff cube. -/
theorem heathBrown_three_exact {z : ℝ} (hz : 0 ≤ z) {n : ℕ} (hn : (n : ℝ) ≤ z ^ 3) :
    Λ n = heathBrownThree z n := by
  have hΛ (i : ℕ) (hi : (i : ℝ) ≤ 1) : Λ i = 0 := by
    have hle : i ≤ 1 := by exact_mod_cast hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp
  have hvanish : (Λ * heathBrownRemainder z ^ 3) n = 0 :=
    dirichlet_mul_apply_eq_zero_of_cutoffs zero_le_one (pow_nonneg hz _) hΛ
      (fun _ h => heathBrownRemainder_cube_apply_eq_zero hz h) (by simpa only [one_mul] using hn)
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (heathBrown_three_ring z)
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
    arithThreeMul_apply, hvanish, neg_zero, add_zero, heathBrownThree] using h

/-- The original chart uses the real cutoff (2R)^(1/3). The identity at
that cutoff covers every positive integer through its physical upper endpoint. -/
theorem heathBrown_three_at_original_scale {R : ℝ} (hR : 0 ≤ R)
    {n : ℕ} (hn : (n : ℝ) ≤ 2 * R) :
    Λ n = heathBrownThree ((2 * R) ^ (1 / 3 : ℝ)) n := by
  have h2R : 0 ≤ 2 * R := by positivity
  apply heathBrown_three_exact (Real.rpow_nonneg h2R _)
  rw [← Real.rpow_ofNat, ← Real.rpow_mul h2R,
    show (1 / 3 : ℝ) * 3 = 1 by norm_num, Real.rpow_one]
  exact hn

/-- Inserting the original smooth group window extends the identity
pointwise to every integer, because the window vanishes beyond 2R. -/
theorem heathBrown_three_windowed {R : ℝ} (hR : 0 ≤ R)
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, w n ≠ 0 → (n : ℝ) ≤ 2 * R) (n : ℕ) :
    w n * Λ n = w n * heathBrownThree ((2 * R) ^ (1 / 3 : ℝ)) n := by
  by_cases hn : w n = 0
  · simp only [hn, zero_mul]
  · rw [heathBrown_three_at_original_scale hR (hw n hn)]

end

end ImbalancedChen.Part3
