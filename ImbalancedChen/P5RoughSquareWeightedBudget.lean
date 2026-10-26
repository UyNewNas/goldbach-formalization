import ImbalancedChen.RoughSquareException
import ImbalancedChen.TotientReciprocalBudget

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Weighted COMPLETE-PRODUCT rough-square exceptions. The primary exact
positive-multiple count is retained without a floor-loss term. Harmonic
and reciprocal-totient costs keep the full physical modulus in their
 denominators; no separate beta l1 mass is introduced.
-/
namespace ImbalancedChen.P5Z.RoughSquareWeightedBudget
noncomputable section
open scoped Classical BigOperators

def logBudget (Q : ℕ) : ℝ := 1 + Real.log (max 1 (Q : ℝ))

theorem logBudget_nonneg (Q : ℕ) : 0 ≤ logBudget Q := by
  have h := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
  dsimp [logBudget]
  linarith

theorem harmonic_Icc_le_logBudget (Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 Q, 1 / (m : ℝ)) ≤ logBudget Q := by
  have hH : (∑ m ∈ Finset.Icc 1 Q, 1 / (m : ℝ)) = (harmonic Q : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [hH]
  by_cases hQ : Q = 0
  · subst Q
    simp [logBudget]
  · have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
    simpa only [logBudget,max_eq_right hQ1] using harmonic_le_one_add_log Q

/-- Divisor reciprocals retain the actual physical integer n. -/
theorem reciprocal_totient_le_logBudget {n Q : ℕ} (hn : 0 < n) (hnQ : n ≤ Q) :
    1 / (Nat.totient n : ℝ) ≤ 2 * ((1 / (n : ℝ)) * logBudget Q) := by
  have hsub : n.divisors ⊆ Finset.Icc 1 Q := by
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,(Nat.le_of_dvd hn hdiv).trans hnQ⟩
  have hs : (∑ d ∈ n.divisors, 1 / (d : ℝ)) ≤ logBudget Q :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (harmonic_Icc_le_logBudget Q)
  exact (reciprocal_totient_le_divisor_sum hn).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (by positivity)) (by norm_num))

/-- Weighted positive multiples inject by n/d; the factor 1/d is retained
BEFORE summing, with no additive one per divisor. -/
theorem positive_multiples_reciprocal_le (Q : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ positiveMultiplesUpTo Q d, 1 / (n : ℝ)) ≤ (1 / (d : ℝ)) * logBudget Q := by
  let S := positiveMultiplesUpTo Q d
  have hquot (n : ℕ) (hn : n ∈ S) : 1 ≤ n / d ∧ n / d ≤ Q := by
    obtain ⟨hn1,hnQ,hdn⟩ := mem_positiveMultiplesUpTo.mp hn
    refine ⟨(Nat.le_div_iff_mul_le hd).mpr ?_,(Nat.div_le_self n d).trans hnQ⟩
    simpa only [one_mul] using Nat.le_of_dvd (by omega : 0 < n) hdn
  have hinj : Set.InjOn (fun n : ℕ => n / d) (S : Set ℕ) := by
    intro a ha b hb hab
    have had := (mem_positiveMultiplesUpTo.mp ha).2.2
    have hbd := (mem_positiveMultiplesUpTo.mp hb).2.2
    calc
      a = (a / d) * d := (Nat.div_mul_cancel had).symm
      _ = (b / d) * d := by rw [hab]
      _ = b := Nat.div_mul_cancel hbd
  have hsub : S.image (fun n => n / d) ⊆ Finset.Icc 1 Q := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Icc.mpr (hquot n hn)
  calc
    _ = (1 / (d : ℝ)) * ∑ m ∈ S.image (fun n => n / d), 1 / (m : ℝ) := by
      rw [Finset.mul_sum,Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro n hn
      have hncast : (n : ℝ) = (n / d : ℕ) * (d : ℝ) := by
        exact_mod_cast (Nat.div_mul_cancel (mem_positiveMultiplesUpTo.mp hn).2.2).symm
      rw [hncast]
      simp only [one_div,mul_inv_rev,mul_comm]
    _ ≤ (1 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 Q, 1 / (m : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_Icc_le_logBudget Q) (by positivity)

/-- Complete physical rough-square harmonic mass, exact natural cutoff. -/
theorem rough_square_reciprocal_nat_le (Q : ℕ) {L : ℕ} (hL : 2 ≤ L) :
    (∑ n ∈ roughSquareExceptionsNat Q L, 1 / (n : ℝ)) ≤ logBudget Q / ((L : ℝ) - 1) := by
  let P := roughSquarePrimeCarrier Q L
  have hpoint (n : ℕ) (hn : n ∈ roughSquareExceptionsNat Q L) :
      1 / (n : ℝ) ≤ ∑ p ∈ P, if p ^ 2 ∣ n then 1 / (n : ℝ) else 0 := by
    rw [roughSquareExceptionsNat_eq_biUnion] at hn
    obtain ⟨p,hp,hnp⟩ := Finset.mem_biUnion.mp hn
    have hdiv := (mem_positiveMultiplesUpTo.mp hnp).2.2
    have hsingle := Finset.single_le_sum
      (fun q (_hq : q ∈ P) => show 0 ≤ (if q ^ 2 ∣ n then 1 / (n : ℝ) else 0) by positivity) hp
    simpa only [if_pos hdiv] using hsingle
  have hsub : roughSquareExceptionsNat Q L ⊆ Finset.Icc 1 Q := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(mem_roughSquareExceptionsNat.mp hn).1,(mem_roughSquareExceptionsNat.mp hn).2.1⟩
  have htail : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 / ((L : ℝ) - 1) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)).trans (reciprocalSquare_Icc_tail_le Q hL)
  calc
    _ ≤ ∑ n ∈ roughSquareExceptionsNat Q L, ∑ p ∈ P,
        if p ^ 2 ∣ n then 1 / (n : ℝ) else 0 := Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ Finset.Icc 1 Q, ∑ p ∈ P,
        if p ^ 2 ∣ n then 1 / (n : ℝ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ p ∈ P, ∑ n ∈ positiveMultiplesUpTo Q (p ^ 2), 1 / (n : ℝ) := by
      rw [Finset.sum_comm]
      simp only [positiveMultiplesUpTo,Finset.sum_filter]
    _ ≤ ∑ p ∈ P, (1 / (p : ℝ) ^ 2) * logBudget Q := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      simpa only [Nat.cast_pow] using positive_multiples_reciprocal_le Q (pow_pos hprime.pos 2)
    _ = logBudget Q * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ logBudget Q * (1 / ((L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left htail (logBudget_nonneg Q)
    _ = _ := by ring

theorem rough_square_reciprocal_le (Q : ℕ) {w : ℝ} (hw : 1 < w) :
    (∑ n ∈ roughSquareExceptions Q w, 1 / (n : ℝ)) ≤ logBudget Q / (w - 1) := by
  have hceil : 2 ≤ Nat.ceil w := Nat.add_one_le_ceil_iff.mpr (by simpa using hw)
  rw [roughSquareExceptions_eq_nat_ceil]
  exact (rough_square_reciprocal_nat_le Q hceil).trans
    (div_le_div_of_nonneg_left (logBudget_nonneg Q) (by linarith)
      (sub_le_sub_right (Nat.le_ceil w) 1))

/-- REAL weighted deletion budget with complete-product denominator n.
The actual AP/count/centre kernel has precisely these three costs. -/
theorem rough_square_kernel_budget (Q : ℕ) {w T : ℝ} (hw : 1 < w) (hT : 0 ≤ T) :
    (∑ n ∈ roughSquareExceptions Q w,
      (T / (n : ℝ) + 1 + T / (Nat.totient n : ℝ))) ≤
      ((Q : ℝ) + T * logBudget Q * (1 + 2 * logBudget Q)) / (w - 1) := by
  let C := T * (1 + 2 * logBudget Q)
  have hH := logBudget_nonneg Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (n : ℕ) (hn : n ∈ roughSquareExceptions Q w) :
      T / (n : ℝ) + 1 + T / (Nat.totient n : ℝ) ≤ C * (1 / (n : ℝ)) + 1 := by
    have hn1 := (mem_roughSquareExceptions.mp hn).1
    have hnQ := (mem_roughSquareExceptions.mp hn).2.1
    have hp := mul_le_mul_of_nonneg_left (reciprocal_totient_le_logBudget (by omega) hnQ) hT
    calc
      _ = T * (1 / (n : ℝ)) + 1 + T * (1 / (Nat.totient n : ℝ)) := by ring
      _ ≤ T * (1 / (n : ℝ)) + 1 + T * (2 * ((1 / (n : ℝ)) * logBudget Q)) := add_le_add_left hp _
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ ∑ n ∈ roughSquareExceptions Q w, (C * (1 / (n : ℝ)) + 1) := Finset.sum_le_sum hpoint
    _ = C * (∑ n ∈ roughSquareExceptions Q w, 1 / (n : ℝ)) +
        ((roughSquareExceptions Q w).card : ℝ) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp
    _ ≤ C * (logBudget Q / (w - 1)) + (Q : ℝ) / (w - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left (rough_square_reciprocal_le Q hw) hC)
        (roughSquareExceptions_card_le Q hw)
    _ = _ := by dsimp [C]; ring

end
end ImbalancedChen.P5Z.RoughSquareWeightedBudget

