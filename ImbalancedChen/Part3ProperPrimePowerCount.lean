import ImbalancedChen.Part3PrimeProductVonMangoldt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-!
# Counting proper prime powers in a finite range
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset

/-- A proper prime power at most `Y` has base at most `√Y` and exponent at most
`log₂ Y`. -/
theorem exists_properPrimePower_bounded {Y n : ℕ} (hn : properPrimePower n) (hnY : n ≤ Y) :
    ∃ p j : ℕ, p.Prime ∧ p ≤ Nat.sqrt Y ∧ 2 ≤ j ∧ j ≤ Nat.log 2 Y ∧ p ^ j = n := by
  obtain ⟨p, j, hp, hj, rfl⟩ := (properPrimePower_iff_exists n).mp hn
  exact ⟨p, j, hp,
    Nat.le_sqrt'.mpr ((Nat.pow_le_pow_right hp.pos hj).trans hnY), hj,
    Nat.le_log_of_pow_le Nat.one_lt_two ((Nat.pow_le_pow_left hp.two_le j).trans hnY), rfl⟩

/-- The proper prime powers at most `Y` are precisely the image of the bounded
prime-base and exponent pairs whose powers are at most `Y`. -/
theorem properPrimePowers_range_eq_image (Y : ℕ) :
    (Finset.range (Y + 1)).filter properPrimePower =
      (((Finset.Icc 1 (Nat.sqrt Y)) ×ˢ (Finset.Icc 2 (Nat.log 2 Y))).filter
        (fun a : ℕ × ℕ => a.1.Prime ∧ a.1 ^ a.2 ≤ Y)).image (fun a => a.1 ^ a.2) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnY, hn⟩ := Finset.mem_filter.mp hn
    have hnY' := Nat.le_of_lt_succ (Finset.mem_range.mp hnY)
    obtain ⟨p, j, hp, hpY, hj, hjY, heq⟩ := exists_properPrimePower_bounded hn hnY'
    exact Finset.mem_image.mpr ⟨(p, j), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le, hpY⟩,
        Finset.mem_Icc.mpr ⟨hj, hjY⟩⟩, hp, heq ▸ hnY'⟩, heq⟩
  · intro hn
    obtain ⟨⟨p, j⟩, ha, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hab, hp, hpY⟩ := Finset.mem_filter.mp ha
    have hj := (Finset.mem_Icc.mp (Finset.mem_product.mp hab).2).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpY),
      (properPrimePower_iff_exists (p ^ j)).mpr ⟨p, j, hp, hj, rfl⟩⟩

/-- The number of proper prime powers at most `Y` is at most `√Y log₂ Y`. -/
theorem card_properPrimePowers_range_le (Y : ℕ) :
    ((Finset.range (Y + 1)).filter properPrimePower).card ≤ Nat.sqrt Y * Nat.log 2 Y := by
  rw [properPrimePowers_range_eq_image]
  refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  rw [Finset.card_product, Nat.card_Icc, Nat.card_Icc, Nat.add_sub_cancel]
  exact Nat.mul_le_mul_left _ (by omega)

/-- The same count applies in any finite window contained in `[0,Y]`. -/
theorem card_properPrimePowers_window_le (Y : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ≤ Y) :
    (s.filter properPrimePower).card ≤ Nat.sqrt Y * Nat.log 2 Y := by
  refine (Finset.card_le_card ?_).trans (card_properPrimePowers_range_le Y)
  intro n hn
  obtain ⟨hns, hnp⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hs n hns)), hnp⟩

end

end ImbalancedChen.Part3
