import ImbalancedChen.Part3LongSlotDistribution

/-!
# A signed divisor expansion on the long integer slot

The same finite divisor expansion weights the progression and its exact
primitive mean. Each divisor changes only the long interval endpoints and
the short factor in the congruence. The resulting error is uniform in both
endpoints and every primitive residue.
-/

namespace ImbalancedChen

noncomputable section

open Classical Finset
open scoped BigOperators

/-- A finite signed sum of divisor indicators. -/
def part3DivisorExpansion {R : Type*} [AddCommMonoid R]
    (D : Finset ℕ) (coeff : ℕ → R) (n : ℕ) : R :=
  ∑ d ∈ D, if d ∣ n then coeff d else 0

/-- The integral endpoints `L < n ≤ U` and the exact weighted coprime mean. -/
def part3LongSlotDivisorExpansionRemainder (L U q a m : ℕ) (D : Finset ℕ)
    (coeff : ℕ → ℂ) : ℂ :=
  (∑ n ∈ (Ioc L U).filter (fun n => m * n ≡ a [MOD q]), part3DivisorExpansion D coeff n) -
    (∑ n ∈ (Ioc L U).filter (fun n => (m * n).Coprime q),
      part3DivisorExpansion D coeff n) / (q.totient : ℂ)

private theorem part3_divisor_filter_card_eq (L U d : ℕ) (hd : 0 < d)
    (P : ℕ → Prop) [DecidablePred P] :
    (((Ioc L U).filter P).filter (fun n => d ∣ n)).card =
      ((Ico (L / d + 1) (U / d + 1)).filter (fun k => P (d * k))).card := by
  have hinterval (k : ℕ) :
      k ∈ Ico (L / d + 1) (U / d + 1) ↔ d * k ∈ Ioc L U := by
    simp only [mem_Ico, mem_Ioc, Nat.succ_le_iff, Nat.lt_succ_iff,
      Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, Nat.mul_comm k d]
  symm
  refine card_bij (fun k _ => d * k) ?_ ?_ ?_
  · intro k hk
    obtain ⟨hi, hp⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨(hinterval k).mp hi, hp⟩, dvd_mul_right d k⟩
  · intro k _ j _ h
    exact Nat.mul_left_cancel hd h
  · intro n hn
    obtain ⟨hn, k, rfl⟩ := mem_filter.mp hn
    obtain ⟨hi, hp⟩ := mem_filter.mp hn
    exact ⟨k, mem_filter.mpr ⟨(hinterval k).mpr hi, hp⟩, rfl⟩

/-- The weighted sum over any filtered interval is the divisor-by-divisor
sum of exact quotient-interval counts. -/
theorem part3_sum_divisorExpansion_filter_eq {R : Type*} [CommSemiring R]
    (L U : ℕ) (D : Finset ℕ) (coeff : ℕ → R) (P : ℕ → Prop) [DecidablePred P]
    (hD : ∀ d ∈ D, 0 < d) :
    (∑ n ∈ (Ioc L U).filter P, part3DivisorExpansion D coeff n) =
      ∑ d ∈ D, coeff d *
        (((Ico (L / d + 1) (U / d + 1)).filter (fun k => P (d * k))).card : R) := by
  unfold part3DivisorExpansion
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, part3_divisor_filter_card_eq L U d (hD d hd) P,
    mul_comm]

/-- Expanding the divisibility conditions gives the original unweighted
remainder for `m*d` on each quotient interval. -/
theorem part3LongSlotDivisorExpansionRemainder_eq_sum (L U q a m : ℕ)
    (D : Finset ℕ) (coeff : ℕ → ℂ) (hD : ∀ d ∈ D, 0 < d) :
    part3LongSlotDivisorExpansionRemainder L U q a m D coeff =
      ∑ d ∈ D, coeff d * (part3LongSlotRemainder (L / d + 1) (U / d + 1) q a (m * d) : ℂ) := by
  unfold part3LongSlotDivisorExpansionRemainder
  rw [part3_sum_divisorExpansion_filter_eq L U D coeff (fun n => m * n ≡ a [MOD q]) hD,
    part3_sum_divisorExpansion_filter_eq L U D coeff (fun n => (m * n).Coprime q) hD,
    sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  rw [mul_div_assoc, ← mul_sub]
  simp only [part3LongSlotRemainder, part3LongSlotAPCount, part3LongSlotCoprimeCount,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast, mul_assoc]

/-- Each divisor costs at most two times its coefficient norm, regardless of
the interval, the modulus or the short factor. -/
theorem part3LongSlotDivisorExpansionRemainder_norm_le (L U q a m : ℕ)
    (D : Finset ℕ) (coeff : ℕ → ℂ) (hD : ∀ d ∈ D, 0 < d)
    (hq : 0 < q) (ha : a.Coprime q) :
    ‖part3LongSlotDivisorExpansionRemainder L U q a m D coeff‖ ≤ 2 * ∑ d ∈ D, ‖coeff d‖ := by
  rw [part3LongSlotDivisorExpansionRemainder_eq_sum L U q a m D coeff hD]
  calc
    _ ≤ ∑ d ∈ D, ‖coeff d * (part3LongSlotRemainder (L / d + 1) (U / d + 1) q a (m * d) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ D, ‖coeff d‖ * 2 := by
      apply sum_le_sum
      intro d _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (part3LongSlotRemainder_abs_le_two (L / d + 1) (U / d + 1) q a (m * d) hq ha)
        (norm_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

/-- The weighted long-slot discrepancy with the original signed short and
physical-modulus coefficients. -/
def part3LongSlotDivisorExpansionSignedError (S Q D : Finset ℕ)
    (alpha rho coeff : ℕ → ℂ) (L U a : ℕ) : ℂ :=
  ∑ q ∈ Q, rho q * ∑ m ∈ S, alpha m * part3LongSlotDivisorExpansionRemainder L U q a m D coeff

theorem part3LongSlotDivisorExpansionSignedError_norm_le (S Q D : Finset ℕ)
    (alpha rho coeff : ℕ → ℂ) (L U a : ℕ) (hD : ∀ d ∈ D, 0 < d)
    (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotDivisorExpansionSignedError S Q D alpha rho coeff L U a‖ ≤
      2 * (∑ d ∈ D, ‖coeff d‖) * (∑ m ∈ S, ‖alpha m‖) * (∑ q ∈ Q, ‖rho q‖) := by
  have hshort (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ S, alpha m * part3LongSlotDivisorExpansionRemainder L U q a m D coeff‖ ≤
        (∑ m ∈ S, ‖alpha m‖) * (2 * ∑ d ∈ D, ‖coeff d‖) := by
    calc
      _ ≤ ∑ m ∈ S, ‖alpha m * part3LongSlotDivisorExpansionRemainder L U q a m D coeff‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ S, ‖alpha m‖ * (2 * ∑ d ∈ D, ‖coeff d‖) := by
        apply sum_le_sum
        intro m _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (part3LongSlotDivisorExpansionRemainder_norm_le L U q a m D coeff hD (hq q hqQ) (ha q hqQ))
          (norm_nonneg _)
      _ = _ := by rw [sum_mul]
  unfold part3LongSlotDivisorExpansionSignedError
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ m ∈ S, alpha m *
        part3LongSlotDivisorExpansionRemainder L U q a m D coeff‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ((∑ m ∈ S, ‖alpha m‖) * (2 * ∑ d ∈ D, ‖coeff d‖)) := by
      apply sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hshort q hqQ) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

end

end ImbalancedChen
