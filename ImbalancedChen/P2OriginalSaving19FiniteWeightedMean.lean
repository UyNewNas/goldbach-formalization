import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Bounds for the exact nine-vertex, gap-weighted first-moment formula. -/
namespace ImbalancedChen.P2OriginalSaving19FiniteWeightedMean
open scoped BigOperators

theorem bounds (g f : Fin 9 → ℚ) {a b : ℚ}
    (hg : ∀ i, 0 ≤ g i) (hpos : 0 < ∑ i, g i)
    (hf : ∀ i, a ≤ f i ∧ f i ≤ b) :
    a ≤ ((∑ i, f i) + (∑ i, g i * f i) / (∑ i, g i)) / 10 ∧
    ((∑ i, f i) + (∑ i, g i * f i) / (∑ i, g i)) / 10 ≤ b := by
  have hslo : 9 * a ≤ ∑ i, f i := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hf i).1)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  have hshi : (∑ i, f i) ≤ 9 * b := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hf i).2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using h
  have hwlo : a ≤ (∑ i, g i * f i) / (∑ i, g i) := by
    apply (le_div_iff₀ hpos).2
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hf i).1 (hg i))
    calc
      a * (∑ i, g i) = (∑ i, g i) * a := mul_comm _ _
      _ = ∑ i, g i * a := Finset.sum_mul _ _ _
      _ ≤ ∑ i, g i * f i := h
  have hwhi : (∑ i, g i * f i) / (∑ i, g i) ≤ b := by
    apply (div_le_iff₀ hpos).2
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => mul_le_mul_of_nonneg_left (hf i).2 (hg i))
    calc
      (∑ i, g i * f i) ≤ ∑ i, g i * b := h
      _ = (∑ i, g i) * b := (Finset.sum_mul _ _ _).symm
      _ = b * (∑ i, g i) := mul_comm _ _
  constructor <;> linarith

#print axioms bounds

/-- The degree-one nine-vertex gap-weighted deviation formula. -/
theorem deviation_first (g f : Fin 9 → ℚ) (top : ℚ)
    (hg : (∑ i, g i) ≠ 0) (htop : top ≠ 0) :
    ((∑ i, (1 - f i / top)) +
      (∑ i, g i * (1 - f i / top)) / (∑ i, g i)) / 10 =
    1 - (((∑ i, f i) + (∑ i, g i * f i) / (∑ i, g i)) / 10) / top := by
  have hy : (∑ i, (1 - f i / top)) = 9 - (∑ i, f i) / top := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Finset.sum_div]
  have hgy : (∑ i, g i * (1 - f i / top)) =
      (∑ i, g i) - (∑ i, g i * f i) / top := by
    simp_rw [mul_sub, mul_one, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [hy, hgy]
  field_simp [hg, htop]
  ring

#print axioms deviation_first
end ImbalancedChen.P2OriginalSaving19FiniteWeightedMean
