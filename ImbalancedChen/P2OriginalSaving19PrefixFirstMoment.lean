import ImbalancedChen.P2OriginalSaving19PrefixMoments
import ImbalancedChen.P2OriginalSaving19NonnegativeRationalEncoding
import Mathlib.Tactic

/-! Closed degree-zero/one formulas for the existing prefix evaluator.
No replacement evaluator or archive moment field is introduced. -/
namespace ImbalancedChen.P2OriginalSaving19PrefixFirstMoment
open scoped BigOperators
open P2Winner9HomogeneousRecurrence P2OriginalSaving19PrefixMoments

theorem coefficient_zero {n bound : ℕ} (z : Fin n → ℕ) :
    boundedHomogeneous z bound 0 = 1 := by
  induction n with
  | zero => simp [boundedHomogeneous]
  | succ n ih =>
    rw [split_coefficient z (Nat.zero_le _)]
    simpa using ih (fun i => z i.succ)

theorem coefficient_one {n bound : ℕ} (z : Fin n → ℕ) (hb : 1 ≤ bound) :
    boundedHomogeneous z bound 1 = ∑ i, z i := by
  induction n with
  | zero => simp [boundedHomogeneous]
  | succ n ih =>
    rw [coefficient_succ (k := 0) z hb, coefficient_zero, ih, Nat.mul_one,
      Fin.sum_univ_succ]
    exact Nat.add_comm _ _

theorem prefix_zero (z : Fin 9 → ℕ) :
    (prefixCoefficients 6 9 z)[0]?.getD 0 = 1 := by
  rw [prefixCoefficients_correct 6 9 z 0 (by decide), coefficient_zero]

theorem prefix_one (z : Fin 9 → ℕ) :
    (prefixCoefficients 6 9 z)[1]?.getD 0 = ∑ i, z i := by
  rw [prefixCoefficients_correct 6 9 z 1 (by decide), coefficient_one z (by decide)]

theorem weighted_zero (g z : Fin 9 → ℕ) : weightedNumerator g z 0 = ∑ i, g i := by
  simp [weightedNumerator, prefix_zero]

theorem weighted_one (g z : Fin 9 → ℕ) :
    weightedNumerator g z 1 = (∑ i, z i) * (∑ i, g i) + ∑ i, g i * z i := by
  simp only [weightedNumerator, Fin.sum_univ_succ, Fin.val_zero, Nat.sub_zero,
    pow_zero, Nat.mul_one, Fin.val_succ, Fin.sum_univ_zero, Nat.add_zero,
    Nat.zero_add, Nat.sub_self, prefix_zero, prefix_one, pow_one, one_mul]

theorem normalized_zero (g z : Fin 9 → ℕ) (d : ℕ) (hg : (∑ i, g i) ≠ 0) :
    normalizedMoment g z d 0 = 1 := by
  have h : (∑ i, (g i : ℚ)) ≠ 0 := by exact_mod_cast hg
  simp [normalizedMoment, weighted_zero, h]

theorem normalized_one (g z : Fin 9 → ℕ) (d : ℕ)
    (hg : (∑ i, g i) ≠ 0) (hd : d ≠ 0) :
    normalizedMoment g z d 1 =
      ((∑ i, (z i : ℚ)) + (∑ i, (g i : ℚ) * (z i : ℚ)) / (∑ i, (g i : ℚ))) /
        (10 * (d : ℚ)) := by
  have hs : (∑ i, (g i : ℚ)) ≠ 0 := by exact_mod_cast hg
  have hdc : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [normalizedMoment, weighted_one]
  norm_num only [Nat.choose_one_right, Nat.cast_mul, Nat.cast_add, Nat.cast_sum,
    Nat.cast_pow, pow_one, Nat.cast_ofNat]
  field_simp

#print axioms coefficient_zero
#print axioms coefficient_one
#print axioms normalized_zero
#print axioms normalized_one

open P2OriginalSaving19NonnegativeRationalEncoding

/-- The existing prefix algorithm on explicit encodings of the actual rationals. -/
def encodedMoment (g y : Fin 9 → ℚ) (k : ℕ) : ℚ :=
  normalizedMoment (numerator g) (numerator y) (denominator y) k

theorem encoded_zero (g y : Fin 9 → ℚ) (hg : ∀ i, 0 ≤ g i)
    (hpos : 0 < ∑ i, g i) : encodedMoment g y 0 = 1 :=
  normalized_zero _ _ _ (ne_of_gt (numerator_sum_pos g hg hpos))

theorem encoded_one (g y : Fin 9 → ℚ) (hg : ∀ i, 0 ≤ g i)
    (hy : ∀ i, 0 ≤ y i) (hpos : 0 < ∑ i, g i) :
    encodedMoment g y 1 = ((∑ i, y i) + (∑ i, g i * y i) / (∑ i, g i)) / 10 := by
  have hgs : (∑ i, (numerator g i : ℚ)) = (∑ i, g i) * (denominator g : ℚ) := by
    simp only [numerator_cast g hg, Finset.sum_mul]
  have hys : (∑ i, (numerator y i : ℚ)) = (∑ i, y i) * (denominator y : ℚ) := by
    simp only [numerator_cast y hy, Finset.sum_mul]
  have hgys : (∑ i, (numerator g i : ℚ) * (numerator y i : ℚ)) =
      (∑ i, g i * y i) * (denominator g : ℚ) * (denominator y : ℚ) := by
    simp only [numerator_cast g hg, numerator_cast y hy]
    simp_rw [show ∀ i, (g i * (denominator g : ℚ)) * (y i * (denominator y : ℚ)) =
      (g i * y i) * (denominator g : ℚ) * (denominator y : ℚ) by intro i; ring]
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [encodedMoment, normalized_one _ _ _
    (ne_of_gt (numerator_sum_pos g hg hpos)) (denominator_pos y).ne', hgs, hys, hgys]
  have hs : (∑ i, g i) ≠ 0 := hpos.ne'
  have hgd : (denominator g : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos g).ne'
  have hyd : (denominator y : ℚ) ≠ 0 := by exact_mod_cast (denominator_pos y).ne'
  field_simp [hs, hgd, hyd]

#print axioms encoded_zero
#print axioms encoded_one
end ImbalancedChen.P2OriginalSaving19PrefixFirstMoment
