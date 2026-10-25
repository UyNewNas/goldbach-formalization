import ImbalancedChen.Part3ActualReciprocalSquarePoisson
import ImbalancedChen.Part3ActualCommonIntervalCompletionParseval

/-!
Source-only candidate. This module specializes conjugation to the literal
complete Kloosterman sum used by the physical reciprocal-square Poisson source.
It makes no analytic cancellation claim. Uncompiled under CODE_ONLY.
-/

namespace ImbalancedChen.Part3.KloostermanConjugation

open OriginalSmoothPoissonTail

variable {c : ℕ} [NeZero c]

private theorem star_stdAddChar (x : ZMod c) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have hneg : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hstar : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left hstar).trans
    (eq_inv_of_mul_eq_one_left hneg).symm

/-- Conjugating the actual finite sum negates both integer frequencies. -/
theorem star_kloosterman (m n : ℤ) :
    star (kloosterman c m n) = kloosterman c (-m) (-n) := by
  rw [OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod (c := c),
    OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod (c := c)]
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : IsUnit u
  · simp only [if_pos hu, star_stdAddChar, Int.cast_neg]
    congr 1
    ring
  · simp only [if_neg hu, star_zero]

/-- The actual positive-sign classical Kloosterman sum is real. -/
theorem star_kloosterman_eq (m n : ℤ) :
    star (kloosterman c m n) = kloosterman c m n := by
  rw [star_kloosterman]
  exact ActualReciprocalSquarePoissonSourceOnly.kloosterman_both_negative m n

end ImbalancedChen.Part3.KloostermanConjugation
