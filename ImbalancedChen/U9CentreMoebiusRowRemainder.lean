import ImbalancedChen.U9IntegerCRTDiscrepancy
import ImbalancedChen.Part3SmoothCoprimeError

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL centre mask is expanded over the actual divisors of N.
Each compatible CRT interval comparison costs at most two; all Mobius
coefficients have absolute value at most one. Hence the actual ordinary
row remainder is at most 2*tau(N), with no analytical hypothesis.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def maskedIntervalCount (A B d a N e : ℕ) : ℝ :=
  (((Finset.Ico A B).filter
    (fun r => Nat.Coprime r N ∧ Nat.ModEq d r a ∧ e ∣ r)).card : ℝ)

theorem maskedInterval_moebius (A B d a N e : ℕ) (hN : N ≠ 0)
    (heN : Nat.Coprime e N) :
    maskedIntervalCount A B d a N e =
      ∑ c ∈ N.divisors, (ArithmeticFunction.moebius c : ℝ) *
        divisorAPCount A B d a (c * e) := by
  have hleft : (∑ r ∈ Finset.Ico A B, if Nat.Coprime r N then
      (if Nat.ModEq d r a ∧ e ∣ r then (1 : ℝ) else 0) else 0) =
      maskedIntervalCount A B d a N e := by
    simp only [← ite_and, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one, maskedIntervalCount]
  rw [← hleft, ImbalancedChen.Part3.CommonSmoothCutoff.coprime_weight_eq_moebius
    (Finset.Ico A B) (fun r => if Nat.ModEq d r a ∧ e ∣ r then (1 : ℝ) else 0) hN]
  apply Finset.sum_congr rfl
  intro c hc
  have hce : Nat.Coprime c e := (heN.of_dvd_right (Nat.dvd_of_mem_divisors hc)).symm
  have hset : (Finset.Ico A B).filter (fun r => c ∣ r ∧ (Nat.ModEq d r a ∧ e ∣ r)) =
      (Finset.Ico A B).filter (fun r => Nat.ModEq d r a ∧ c * e ∣ r) := by
    ext r
    simp only [Finset.mem_filter]
    have hdiv : c ∣ r ∧ e ∣ r ↔ c * e ∣ r := by
      constructor
      · rintro ⟨hcr, her⟩
        exact hce.mul_dvd_of_dvd_of_dvd hcr her
      · intro h
        exact ⟨(dvd_mul_right c e).trans h, (dvd_mul_left e c).trans h⟩
    tauto
  rw [← ite_and, ← Finset.sum_filter, hset]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, divisorAPCount]

theorem maskedInterval_dilution_le (A B d a N e : ℕ)
    (hN : N ≠ 0) (hd : 0 < d) (he : 0 < e)
    (hdN : Nat.Coprime d N) (heDN : Nat.Coprime e (d * N)) :
    |maskedIntervalCount A B d a N e - maskedIntervalCount A B d a N 1 / (e : ℝ)| ≤
      2 * (N.divisors.card : ℝ) := by
  have heN := (Nat.coprime_mul_iff_right.mp heDN).2
  have heD := (Nat.coprime_mul_iff_right.mp heDN).1
  have hsum : maskedIntervalCount A B d a N e -
      maskedIntervalCount A B d a N 1 / (e : ℝ) =
      ∑ c ∈ N.divisors, (ArithmeticFunction.moebius c : ℝ) *
        (divisorAPCount A B d a (c * e) - divisorAPCount A B d a c / (e : ℝ)) := by
    rw [maskedInterval_moebius A B d a N e hN heN,
      maskedInterval_moebius A B d a N 1 hN (Nat.coprime_one_left N),
      Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    simp only [Nat.mul_one]
    ring
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ N.divisors, |(ArithmeticFunction.moebius c : ℝ) *
        (divisorAPCount A B d a (c * e) - divisorAPCount A B d a c / (e : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ N.divisors, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      have hcN := Nat.dvd_of_mem_divisors hc
      have hdc : Nat.Coprime d c := hdN.of_dvd_right hcN
      have hedc : Nat.Coprime e (d * c) := Nat.coprime_mul_iff_right.mpr
        ⟨heD, heN.of_dvd_right hcN⟩
      have hlocal := divisorAPCount_dilution_le_two A B d a c e hd
        (Nat.pos_of_mem_divisors hc) he hdc hedc
      have hmu : |(ArithmeticFunction.moebius c : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := c))
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hmu hlocal (abs_nonneg _) zero_le_one
    _ = _ := by simp [mul_comm]

theorem rowAPDiv_eq_maskedInterval {N p q d e : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d)
    (hNd : Nat.Coprime N d) (hm : Nat.Coprime (p * q) d) :
    ((rowAPDiv N X p q d e).card : ℝ) =
      maskedIntervalCount (rowLower N X p q) (rowUpper N p q)
        d (residue N (p * q) d) N e := by
  unfold rowAPDiv maskedIntervalCount
  rw [preprimeRow_eq_interval_coprime hf hX]
  congr 1
  ext r
  have hprod : p * r * q = (p * q) * r := by ring
  simp only [Finset.mem_filter, hprod, product_AP_iff hd hNd, hm, true_and, and_assoc]

/-- The actual source's allowed squarefree divisor e has a deterministic
finite remainder bound. No final row counting target occurs as a premise. -/
theorem ordinaryRow_abs_remainder_le_divisorCost
    {N p q d e z : ℕ} {X : ℝ} (hf : factorAllowed N p q) (hX : 0 ≤ X)
    (hd : 0 < d) (hNd : Nat.Coprime N d) (he : e ∣ sieveProduct (d * N) z) :
    |(ordinaryRowSieve N d z X p q).rem e| ≤ 2 * (N.divisors.card : ℝ) := by
  have hNpos : 0 < N := (mem_chenAdditivePrimeCarrier.mp hf.1).2.1.pos.trans
    (mem_chenAdditivePrimeCarrier.mp hf.1).1
  have hepos : 0 < e := Nat.pos_of_mem_divisors
    (Nat.mem_divisors.mpr ⟨he, (sieveProduct_squarefree (d * N) z).ne_zero⟩)
  have heDN := coprime_of_dvd_sieveProduct he
  rw [ordinaryRow_remainder_raw]
  by_cases hm : Nat.Coprime (p * q) d
  · rw [rowAPDiv_eq_maskedInterval hf hX hd hNd hm,
      rowAPDiv_eq_maskedInterval hf hX hd hNd hm]
    exact maskedInterval_dilution_le _ _ _ _ _ _ hNpos.ne' hd hepos hNd.symm heDN
  · have hzero (t : ℕ) : rowAPDiv N X p q d t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hAP := (Finset.mem_filter.mp hr).2.1
      have hprod : Nat.ModEq d ((p * q) * r) N := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hAP
      exact hm ((product_AP_iff hd hNd).mp hprod).1
    simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_div, sub_self, abs_zero]
    positivity

end
end ImbalancedChen.U9SemiprimeSwitch
