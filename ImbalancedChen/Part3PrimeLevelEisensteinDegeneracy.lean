import ImbalancedChen.Part3PrimeLevelRowDegeneracy
import ImbalancedChen.Part3LevelPrimitiveComplexEisensteinRegularity

/-!
Actual prime-level degeneracy of the absolutely convergent primitive series.
The two row bijections and the positive-base complex powers determine every
factor. No degeneracy recurrence or finite-oldform identity is an input.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open Set Filter Complex
open scoped Topology UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.PrimeLevelRowDegeneracy20261025a

namespace ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a

/-- Positive real dilation of the native upper half plane. -/
def dilate (a : ℝ) (ha : 0 < a) (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(a : ℂ) * (z : ℂ), by simpa using mul_pos ha z.im_pos⟩

@[simp] theorem dilate_coe (a : ℝ) (ha : 0 < a) (z : UpperHalfPlane) :
    (dilate a ha z : ℂ) = (a : ℂ) * (z : ℂ) := rfl

@[simp] theorem dilate_im (a : ℝ) (ha : 0 < a) (z : UpperHalfPlane) :
    (dilate a ha z).im = a * z.im := by simp [dilate]

theorem prime_real_pos {p : ℕ} (hp : p.Prime) : 0 < (p : ℝ) := by
  exact_mod_cast hp.pos

theorem good_positiveBase {p : ℕ} (hp : p.Prime) (M : ℕ)
    (z : UpperHalfPlane) (v : GoodRows p M) :
    positiveBase (dilate p (prime_real_pos hp) z) (toPrimitiveRow M v.1) =
      (p : ℝ) * positiveBase z (toPrimitiveRow (p * M) (raiseFirst hp M v)) := by
  change (dilate p (prime_real_pos hp) z).im /
      ‖(v.1.1 0 : ℂ) * (dilate p (prime_real_pos hp) z : ℂ) + (v.1.1 1 : ℂ)‖ ^ 2 =
    (p : ℝ) * (z.im / ‖(((p : ℤ) * v.1.1 0 : ℤ) : ℂ) * (z : ℂ) + (v.1.1 1 : ℂ)‖ ^ 2)
  rw [dilate_im, dilate_coe]
  have hlin : (v.1.1 0 : ℂ) * ((p : ℂ) * (z : ℂ)) + (v.1.1 1 : ℂ) =
      (((p : ℤ) * v.1.1 0 : ℤ) : ℂ) * (z : ℂ) + (v.1.1 1 : ℂ) := by
    push_cast
    ring
  simp only [Complex.ofReal_natCast]
  rw [hlin]
  ring

theorem bad_positiveBase {p : ℕ} (hp : p.Prime) (M : ℕ)
    (z : UpperHalfPlane) (v : ExcludedRows p M) :
    positiveBase (dilate p (prime_real_pos hp) z) (toPrimitiveRow M (raiseSecond hp M v).1) =
      positiveBase z (toPrimitiveRow M v.1) / (p : ℝ) := by
  have hpR := prime_real_pos hp
  have hn : ‖(v.1.1 0 : ℂ) * (z : ℂ) + (v.1.1 1 : ℂ)‖ ≠ 0 := by
    intro h
    have hb := positiveBase_pos z (toPrimitiveRow M v.1)
    simp only [positiveBase, toPrimitiveRow, h, zero_pow (by omega : 2 ≠ 0), div_zero] at hb
    exact lt_irrefl _ hb
  change (dilate p hpR z).im /
      ‖(v.1.1 0 : ℂ) * (dilate p hpR z : ℂ) + (((p : ℤ) * v.1.1 1 : ℤ) : ℂ)‖ ^ 2 =
    (z.im / ‖(v.1.1 0 : ℂ) * (z : ℂ) + (v.1.1 1 : ℂ)‖ ^ 2) / (p : ℝ)
  rw [dilate_im, dilate_coe]
  have hlin : (v.1.1 0 : ℂ) * ((p : ℂ) * (z : ℂ)) +
      (((p : ℤ) * v.1.1 1 : ℤ) : ℂ) =
      (p : ℂ) * ((v.1.1 0 : ℂ) * (z : ℂ) + (v.1.1 1 : ℂ)) := by
    push_cast
    ring
  simp only [Complex.ofReal_natCast]
  rw [hlin, norm_mul]
  simp only [Complex.norm_natCast, mul_pow]
  field_simp [hpR.ne', hn]
  <;> ring

private theorem exp_log_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    Complex.exp (s * (Real.log (a * b) : ℂ)) =
      (a : ℂ) ^ s * Complex.exp (s * (Real.log b : ℂ)) := by
  rw [Real.log_mul ha.ne' hb.ne', Complex.ofReal_add, mul_add, Complex.exp_add,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_log ha.le]
  congr 1
  ring

private theorem exp_log_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    Complex.exp (s * (Real.log (b / a) : ℂ)) =
      (a : ℂ) ^ (-s) * Complex.exp (s * (Real.log b : ℂ)) := by
  rw [Real.log_div hb.ne' ha.ne', Complex.ofReal_sub,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_log ha.le,
    ← Complex.exp_add]
  congr 1
  ring

theorem good_seed_scale {p : ℕ} (hp : p.Prime) (M : ℕ)
    (z : UpperHalfPlane) (s : ℂ) (v : GoodRows p M) :
    levelComplexSeed M (dilate p (prime_real_pos hp) z) v.1 s =
      (p : ℂ) ^ s * levelComplexSeed (p * M) z (raiseFirst hp M v) s := by
  unfold levelComplexSeed complexSeed
  rw [good_positiveBase hp M z v]
  simpa only [Complex.ofReal_natCast] using exp_log_mul p _ (prime_real_pos hp)
    (positiveBase_pos z (toPrimitiveRow (p * M) (raiseFirst hp M v))) s

theorem bad_seed_scale {p : ℕ} (hp : p.Prime) (M : ℕ)
    (z : UpperHalfPlane) (s : ℂ) (v : ExcludedRows p M) :
    levelComplexSeed M (dilate p (prime_real_pos hp) z) (raiseSecond hp M v).1 s =
      (p : ℂ) ^ (-s) * levelComplexSeed M z v.1 s := by
  unfold levelComplexSeed complexSeed
  rw [bad_positiveBase hp M z v]
  simpa only [Complex.ofReal_natCast] using exp_log_div p _ (prime_real_pos hp)
    (positiveBase_pos z (toPrimitiveRow M v.1)) s

/-- The exact master decomposition, before deciding whether p divides M. -/
theorem prime_degeneracy_master {p : ℕ} (hp : p.Prime) (M : ℕ)
    (z : UpperHalfPlane) (s : ℂ) (hs : 1 < s.re) :
    levelPrimitiveComplexEisenstein M s (dilate p (prime_real_pos hp) z) =
      (p : ℂ) ^ s * levelPrimitiveComplexEisenstein (p * M) s z +
      (p : ℂ) ^ (-s) * ((1 / 2 : ℂ) *
        ∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s) := by
  classical
  have hsum := levelComplexSeed_summable M (dilate p (prime_real_pos hp) z) s hs
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl
    {v : LevelPrimitiveRow M | ¬ (p : ℤ) ∣ v.1 1}
  have hgood : (∑' v : GoodRows p M,
      levelComplexSeed M (dilate p (prime_real_pos hp) z) v.1 s) =
      (p : ℂ) ^ s * ∑' v : LevelPrimitiveRow (p * M), levelComplexSeed (p * M) z v s := by
    simp_rw [good_seed_scale hp M z s]
    rw [tsum_mul_left, (goodRowsEquiv hp M).tsum_eq]
  have hbad : (∑' v : BadRows p M,
      levelComplexSeed M (dilate p (prime_real_pos hp) z) v.1 s) =
      (p : ℂ) ^ (-s) * ∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s := by
    calc
      _ = ∑' v : ExcludedRows p M,
          levelComplexSeed M (dilate p (prime_real_pos hp) z) (raiseSecond hp M v).1 s :=
        ((badRowsEquiv hp M).tsum_eq
          (fun v => levelComplexSeed M (dilate p (prime_real_pos hp) z) v.1 s)).symm
      _ = _ := by simp_rw [bad_seed_scale hp M z s]; rw [tsum_mul_left]
  have hfull : (∑' v : LevelPrimitiveRow M,
      levelComplexSeed M (dilate p (prime_real_pos hp) z) v s) =
      (p : ℂ) ^ s * (∑' v : LevelPrimitiveRow (p * M), levelComplexSeed (p * M) z v s) +
      (p : ℂ) ^ (-s) * (∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s) := by
    simpa only [Set.mem_setOf_eq, not_not, hgood, hbad] using hsplit.symm
  unfold levelPrimitiveComplexEisenstein
  rw [hfull]
  ring

theorem excluded_sum_eq_level_difference {p : ℕ} (hp : p.Prime) (M : ℕ)
    (hpM : ¬ p ∣ M) (z : UpperHalfPlane) (s : ℂ) (hs : 1 < s.re) :
    (1 / 2 : ℂ) * (∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s) =
      levelPrimitiveComplexEisenstein M s z - levelPrimitiveComplexEisenstein (p * M) s z := by
  classical
  have hsplit := (levelComplexSeed_summable M z s hs).tsum_subtype_add_tsum_subtype_compl
    {v : LevelPrimitiveRow M | (p : ℤ) ∣ v.1 0}
  have hin : (∑' v : IncludedRows p M, levelComplexSeed M z v.1 s) =
      ∑' v : LevelPrimitiveRow (p * M), levelComplexSeed (p * M) z v s := by
    exact (includedRowsEquiv hp M hpM).tsum_eq (fun v => levelComplexSeed (p * M) z v s)
  have hadd : (∑' v : LevelPrimitiveRow (p * M), levelComplexSeed (p * M) z v s) +
      (∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s) =
        ∑' v : LevelPrimitiveRow M, levelComplexSeed M z v s := by
    simpa only [Set.mem_setOf_eq, hin] using hsplit
  unfold levelPrimitiveComplexEisenstein
  linear_combination (1 / 2 : ℂ) * hadd

/-- New-prime recurrence with the original primitive normalization. -/
theorem prime_degeneracy_of_not_dvd {p : ℕ} (hp : p.Prime) (M : ℕ) (hpM : ¬ p ∣ M)
    (z : UpperHalfPlane) (s : ℂ) (hs : 1 < s.re) :
    levelPrimitiveComplexEisenstein M s (dilate p (prime_real_pos hp) z) =
      ((p : ℂ) ^ s - (p : ℂ) ^ (-s)) * levelPrimitiveComplexEisenstein (p * M) s z +
        (p : ℂ) ^ (-s) * levelPrimitiveComplexEisenstein M s z := by
  rw [prime_degeneracy_master hp M z s hs,
    excluded_sum_eq_level_difference hp M hpM z s hs]
  ring

/-- Repeated-prime recurrence; the exceptional primitive branch is genuinely empty. -/
theorem prime_degeneracy_of_dvd {p : ℕ} (hp : p.Prime) (M : ℕ) (hpM : p ∣ M)
    (z : UpperHalfPlane) (s : ℂ) (hs : 1 < s.re) :
    levelPrimitiveComplexEisenstein M s (dilate p (prime_real_pos hp) z) =
      (p : ℂ) ^ s * levelPrimitiveComplexEisenstein (p * M) s z := by
  have he : (∑' v : ExcludedRows p M, levelComplexSeed M z v.1 s) = 0 :=
    tsum_eq_zero (fun v => (excludedRows_empty_of_dvd hpM v).elim)
  rw [prime_degeneracy_master hp M z s hs, he]
  ring

end ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
