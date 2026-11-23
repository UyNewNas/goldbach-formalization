import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
REAL-cutoff truncated Mobius support for the original order-three
Heath--Brown identity. The convention is EXACTLY n <= y, not n < y and
not an integer cube cutoff. Consequently each nonzero remainder factor
has n > y, and its third Dirichlet power vanishes on CLOSED n <= y^3.
-/
namespace ImbalancedChen.P5Z.RealTruncatedMobiusSupport
noncomputable section
open Classical
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

def muTrunc (y : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ y then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

def remainder (y : ℝ) : ArithmeticFunction ℝ :=
  1 - (ζ : ArithmeticFunction ℝ) * muTrunc y

def VanishesUpTo (f : ArithmeticFunction ℝ) (Y : ℝ) : Prop :=
  ∀ n : ℕ, (n : ℝ) ≤ Y → f n = 0

theorem muTrunc_of_le {y : ℝ} {n : ℕ} (h : (n : ℝ) ≤ y) :
    muTrunc y n = (ArithmeticFunction.moebius n : ℝ) := by simp [muTrunc, h]

theorem muTrunc_of_gt {y : ℝ} {n : ℕ} (h : y < (n : ℝ)) :
    muTrunc y n = 0 := by simp [muTrunc, not_le.mpr h]

private theorem second_le_of_antidiagonal {n : ℕ} (hn : n ≠ 0)
    {d : ℕ × ℕ} (hd : d ∈ n.divisorsAntidiagonal) : d.2 ≤ n := by
  have hm := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hdiv : d.2 ∣ n := ⟨d.1, by simpa [mul_comm] using hm.symm⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv

theorem zeta_muTrunc_small {y : ℝ} {n : ℕ} (hny : (n : ℝ) ≤ y) :
    ((ζ : ArithmeticFunction ℝ) * muTrunc y) n = (1 : ArithmeticFunction ℝ) n := by
  by_cases hn : n = 0
  · subst n; simp
  have hsame : ((ζ : ArithmeticFunction ℝ) * muTrunc y) n =
      ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n := by
    simp only [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have hdle : (d.2 : ℝ) ≤ y :=
      (by exact_mod_cast second_le_of_antidiagonal hn hd : (d.2 : ℝ) ≤ n).trans hny
    simp only [muTrunc_of_le hdle, ArithmeticFunction.intCoe_apply]
  rw [hsame, ArithmeticFunction.coe_zeta_mul_coe_moebius]

theorem remainder_vanishes (y : ℝ) : VanishesUpTo (remainder y) y := by
  intro n hn
  change (1 : ArithmeticFunction ℝ) n - ((ζ : ArithmeticFunction ℝ)*muTrunc y) n = 0
  rw [zeta_muTrunc_small hn]
  exact sub_self _

/-- Strict product support, paying the REAL thresholds before any
natural-number rounding. No coefficient support conclusion is assumed. -/
theorem mul_vanishes {f g : ArithmeticFunction ℝ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : VanishesUpTo f A) (hg : VanishesUpTo g B) :
    VanishesUpTo (f*g) (A*B) := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hfa : (d.1 : ℝ) ≤ A
  · rw [hf d.1 hfa, zero_mul]
  by_cases hgb : (d.2 : ℝ) ≤ B
  · rw [hg d.2 hgb, mul_zero]
  have ha : A < (d.1 : ℝ) := lt_of_not_ge hfa
  have hb : B < (d.2 : ℝ) := lt_of_not_ge hgb
  have hp : A*B < (d.1 : ℝ)*(d.2 : ℝ) :=
    (mul_le_mul_of_nonneg_right ha.le hB).trans_lt
      (mul_lt_mul_of_pos_left hb (hA.trans_lt ha))
  have hprod : (d.1 : ℝ)*(d.2 : ℝ) = n := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hd).1
  rw [hprod] at hp
  exact False.elim ((not_lt_of_ge hn) hp)

/-- Left convolution by ANY arithmetic function preserves a right
vanishing interval, since every displayed right divisor is <= n. -/
theorem left_mul_vanishes (f : ArithmeticFunction ℝ) {g : ArithmeticFunction ℝ} {Y : ℝ}
    (hg : VanishesUpTo g Y) : VanishesUpTo (f*g) Y := by
  intro n hn
  by_cases hz : n = 0
  · subst n; simp
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdY : (d.2 : ℝ) ≤ Y :=
    (by exact_mod_cast second_le_of_antidiagonal hz hd : (d.2 : ℝ) ≤ n).trans hn
  rw [hg d.2 hdY, mul_zero]

theorem remainder_cube_vanishes {y : ℝ} (hy : 0 ≤ y) :
    VanishesUpTo (remainder y ^ 3) (y^3) := by
  have h2 := mul_vanishes hy hy (remainder_vanishes y) (remainder_vanishes y)
  have h3 := mul_vanishes (mul_nonneg hy hy) hy h2 (remainder_vanishes y)
  simpa only [pow_three] using h3

/-- Literal original annihilation, including n=0 and n=1 whenever
they belong to the stated REAL cube range. -/
theorem vonMangoldt_remainder_cube_zero {y : ℝ} (hy : 0 ≤ y) {n : ℕ}
    (hn : (n : ℝ) ≤ y^3) :
    (ArithmeticFunction.vonMangoldt * remainder y^3) n = 0 :=
  left_mul_vanishes ArithmeticFunction.vonMangoldt (remainder_cube_vanishes hy) n hn

end
end ImbalancedChen.P5Z.RealTruncatedMobiusSupport
