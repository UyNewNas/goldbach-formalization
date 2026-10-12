import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Part 3: a uniform distribution estimate for an unrough long integer slot

This is the one-long elementary core of the frozen manuscript's
`distribution-prime-product-completion-20261010.txt`, section 7.  The long
variable ranges over one literal half-open interval.  The main term is the
exact coprime source mass divided by Euler's totient; it is not replaced
by the interval length or an Euler-product approximation.

The short sequence and the modulus weights can be complex and depend on
all external parameters.  The bound is simultaneous in those sequences,
the interval endpoints, and every primitive moving residue.  No threshold
depending on an individual residue or coefficient sequence is used.

This module does not assert that the long slot is prime or rough.  Passing
to the chart-rough slot still needs the manuscript's Brun comparison.
The medium convolution and the actual finite policy insertion remain
separate distribution obligations.
-/

namespace ImbalancedChen

noncomputable section

open Classical Finset
open scoped BigOperators

/-- A literal unweighted progression count on the common long interval. -/
def part3IntervalAPCount (L U q a : ℕ) : ℕ :=
  ((Ico L U).filter (fun n => n ≡ a [MOD q])).card

/-- The same interval with the primitive-source filter. -/
def part3IntervalCoprimeCount (L U q : ℕ) : ℕ :=
  ((Ico L U).filter (fun n => q.Coprime n)).card

private theorem part3_prefix_count_le_add_one (U q a b : ℕ) (hq : 0 < q) :
    U.count (fun n => n ≡ a [MOD q]) ≤
      U.count (fun n => n ≡ b [MOD q]) + 1 := by
  rw [Nat.count_modEq_card U hq a, Nat.count_modEq_card U hq b]
  split_ifs <;> omega

private theorem part3_Ico_filter_card_sub (L U : ℕ) (hLU : L ≤ U)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Ico L U).filter P).card = U.count P - L.count P := by
  have hs : (range L).filter P ⊆ (range U).filter P :=
    filter_subset_filter _ (range_mono hLU)
  have he : (Ico L U).filter P = (range U).filter P \ (range L).filter P := by
    ext n
    simp only [mem_filter, mem_Ico, mem_sdiff, mem_range]
    by_cases hn : P n <;> simp only [hn, and_true, and_false, not_false_eq_true]
    omega
  rw [he, card_sdiff_of_subset hs, ← Nat.count_eq_card_filter_range,
    ← Nat.count_eq_card_filter_range]

/-- Any two residue classes have counts within two on the same interval.
The deliberately closed constant includes both endpoint errors. -/
theorem part3IntervalAPCount_le_add_two (L U q a b : ℕ) (hq : 0 < q) :
    part3IntervalAPCount L U q a ≤ part3IntervalAPCount L U q b + 2 := by
  by_cases hLU : L ≤ U
  · unfold part3IntervalAPCount
    rw [part3_Ico_filter_card_sub L U hLU, part3_Ico_filter_card_sub L U hLU]
    have hU := part3_prefix_count_le_add_one U q a b hq
    have hL := part3_prefix_count_le_add_one L q b a hq
    have ha := Nat.count_monotone (p := (fun n => n ≡ a [MOD q])) hLU
    have hb := Nat.count_monotone (p := (fun n => n ≡ b [MOD q])) hLU
    omega
  · simp [part3IntervalAPCount, Ico_eq_empty_of_le (by omega : U ≤ L)]

theorem part3IntervalAPCount_abs_sub_le_two (L U q a b : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) - part3IntervalAPCount L U q b| ≤ 2 := by
  have h₁ : (part3IntervalAPCount L U q a : ℝ) ≤
      part3IntervalAPCount L U q b + 2 := by
    exact_mod_cast part3IntervalAPCount_le_add_two L U q a b hq
  have h₂ : (part3IntervalAPCount L U q b : ℝ) ≤
      part3IntervalAPCount L U q a + 2 := by
    exact_mod_cast part3IntervalAPCount_le_add_two L U q b a hq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact partition of the coprime source by its canonical primitive residues. -/
theorem part3IntervalCoprimeCount_eq_sum (L U q : ℕ) (hq : 0 < q) :
    part3IntervalCoprimeCount L U q =
      ∑ a ∈ (range q).filter (fun a => q.Coprime a), part3IntervalAPCount L U q a := by
  unfold part3IntervalCoprimeCount
  rw [card_eq_sum_card_fiberwise (f := fun n : ℕ => n % q)
    (t := (range q).filter (fun a => q.Coprime a)) (fun n hn => by
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hq), ?_⟩
      exact ((ZMod.coprime_mod_iff_coprime n q).mpr (mem_filter.mp hn).2.symm).symm)]
  apply sum_congr rfl
  intro a ha
  obtain ⟨haq, hqa⟩ := mem_filter.mp ha
  have haqlt := mem_range.mp haq
  unfold part3IntervalAPCount
  congr 1
  ext n
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hn, _⟩, he⟩
    exact ⟨hn, by simpa only [Nat.ModEq, Nat.mod_eq_of_lt haqlt] using he⟩
  · rintro ⟨hn, he⟩
    have hmod : n % q = a := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt haqlt] using he
    refine ⟨⟨hn, ?_⟩, hmod⟩
    apply Nat.Coprime.symm
    apply (ZMod.coprime_mod_iff_coprime n q).mp
    rw [hmod]
    exact hqa.symm

/-- A genuine distribution bound, uniformly over all interval endpoints and
all residues.  Its center is the exact primitive mass. -/
theorem part3IntervalAPCount_coprimeMean_error (L U q a : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) -
      (part3IntervalCoprimeCount L U q : ℝ) / q.totient| ≤ 2 := by
  let R := (range q).filter (fun r => q.Coprime r)
  have hcard : R.card = q.totient := rfl
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hsum : (∑ r ∈ R, ((part3IntervalAPCount L U q a : ℝ) -
        part3IntervalAPCount L U q r)) =
      (q.totient : ℝ) * part3IntervalAPCount L U q a - part3IntervalCoprimeCount L U q := by
    have hsumNat : (∑ r ∈ R, part3IntervalAPCount L U q r) =
        part3IntervalCoprimeCount L U q :=
      (part3IntervalCoprimeCount_eq_sum L U q hq).symm
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard, ← Nat.cast_sum, hsumNat]
  have he : (part3IntervalAPCount L U q a : ℝ) -
        (part3IntervalCoprimeCount L U q : ℝ) / q.totient =
      (∑ r ∈ R, ((part3IntervalAPCount L U q a : ℝ) -
        part3IntervalAPCount L U q r)) / q.totient := by
    rw [hsum, sub_div, mul_div_cancel_left₀ _ hpos.ne']
  rw [he, abs_div, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  calc
    _ ≤ ∑ r ∈ R, |(part3IntervalAPCount L U q a : ℝ) -
        part3IntervalAPCount L U q r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (2 : ℝ) := sum_le_sum fun r _ =>
      part3IntervalAPCount_abs_sub_le_two L U q a r hq
    _ = 2 * (q.totient : ℝ) := by simp [hcard, mul_comm]

/-- The congruence acts on the actual short-times-long integer product. -/
def part3LongSlotAPCount (L U q a m : ℕ) : ℕ :=
  ((Ico L U).filter (fun n => m * n ≡ a [MOD q])).card

/-- The primitive-source filter also acts on that actual product. -/
def part3LongSlotCoprimeCount (L U q m : ℕ) : ℕ :=
  ((Ico L U).filter (fun n => (m * n).Coprime q)).card

def part3LongSlotRemainder (L U q a m : ℕ) : ℝ :=
  (part3LongSlotAPCount L U q a m : ℝ) -
    (part3LongSlotCoprimeCount L U q m : ℝ) / q.totient

/-- Nonprimitive short factors contribute zero to both sides of a primitive
progression discrepancy.  No inverse is used for those factors. -/
theorem part3LongSlotRemainder_eq_zero_of_not_coprime (L U q a m : ℕ)
    (ha : a.Coprime q) (hm : ¬m.Coprime q) :
    part3LongSlotRemainder L U q a m = 0 := by
  have hc (n : ℕ) : ¬(m * n).Coprime q := by
    intro h
    exact hm (Nat.coprime_mul_iff_left.mp h).1
  have hAP (n : ℕ) : ¬m * n ≡ a [MOD q] := by
    intro h
    apply hc n
    change Nat.gcd (m * n) q = 1
    rw [h.gcd_eq]
    exact ha.gcd_eq_one
  simp [part3LongSlotRemainder, part3LongSlotAPCount, part3LongSlotCoprimeCount,
    hAP, hc]

/-- Uniform scalar error for every short factor, including nonunits. -/
theorem part3LongSlotRemainder_abs_le_two (L U q a m : ℕ)
    (hq : 0 < q) (ha : a.Coprime q) :
    |part3LongSlotRemainder L U q a m| ≤ 2 := by
  by_cases hm : m.Coprime q
  · letI : NeZero q := ⟨hq.ne'⟩
    let b := ((m : ZMod q)⁻¹ * (a : ZMod q)).val
    have hmb : m * b ≡ a [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul]
      change (m : ZMod q) * (((m : ZMod q)⁻¹ * (a : ZMod q)).val : ZMod q) = a
      rw [ZMod.natCast_zmod_val, ← mul_assoc, ZMod.coe_mul_inv_eq_one m hm, one_mul]
    have hpred (n : ℕ) : m * n ≡ a [MOD q] ↔ n ≡ b [MOD q] := by
      constructor
      · intro h
        exact Nat.ModEq.cancel_left_of_coprime hm.symm.gcd_eq_one (h.trans hmb.symm)
      · intro h
        exact (h.mul_left m).trans hmb
    have hcpred (n : ℕ) : (m * n).Coprime q ↔ q.Coprime n := by
      simp only [Nat.coprime_mul_iff_left, hm, true_and, Nat.coprime_comm]
    simpa only [part3LongSlotRemainder, part3LongSlotAPCount, part3LongSlotCoprimeCount,
      hpred, hcpred, part3IntervalAPCount, part3IntervalCoprimeCount] using
      part3IntervalAPCount_coprimeMean_error L U q b hq
  · rw [part3LongSlotRemainder_eq_zero_of_not_coprime L U q a m ha hm, abs_zero]
    norm_num

/-- The entire signed modulus sum is retained as the estimated expression.
Only the proved elementary long-slot bound licenses the subsequent triangle
inequality; it supplies no medium-range signed cancellation. -/
def part3LongSlotSignedError (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) : ℂ :=
  ∑ q ∈ Q, ρ q * ∑ m ∈ S, α m * (part3LongSlotRemainder L U q a m : ℂ)

/-- One constant works before the moving residue, both endpoints, and both
coefficient families vary.  The right side uses their exact finite L1 masses. -/
theorem part3LongSlotSignedError_norm_le (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (∑ m ∈ S, ‖α m‖) * (∑ q ∈ Q, ‖ρ q‖) := by
  have hi (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ S, α m * (part3LongSlotRemainder L U q a m : ℂ)‖ ≤
        2 * ∑ m ∈ S, ‖α m‖ := by
    calc
      _ ≤ ∑ m ∈ S, ‖α m * (part3LongSlotRemainder L U q a m : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ S, ‖α m‖ * 2 := by
        apply sum_le_sum
        intro m _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (part3LongSlotRemainder_abs_le_two L U q a m (hq q hqQ) (ha q hqQ))
          (norm_nonneg _)
      _ = _ := by rw [← sum_mul]; ring
  unfold part3LongSlotSignedError
  calc
    _ ≤ ∑ q ∈ Q, ‖ρ q * ∑ m ∈ S, α m * (part3LongSlotRemainder L U q a m : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖ρ q‖ * (2 * ∑ m ∈ S, ‖α m‖) := by
      apply sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hi q hqQ) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- The short-mass/modulus-mass form used by the one-long power budget. -/
theorem part3LongSlotSignedError_norm_le_of_mass (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (M D : ℝ) (hq : ∀ q ∈ Q, 0 < q)
    (ha : ∀ q ∈ Q, a.Coprime q)
    (hM : (∑ m ∈ S, ‖α m‖) ≤ M) (hD : (∑ q ∈ Q, ‖ρ q‖) ≤ D) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤ 2 * M * D := by
  have hM0 : 0 ≤ M := (sum_nonneg (fun _ _ => norm_nonneg _)).trans hM
  exact (part3LongSlotSignedError_norm_le S Q α ρ L U a hq ha).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) hD
      (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity))

/-- No mass estimate needs to be supplied for one-bounded coefficients. -/
theorem part3LongSlotSignedError_norm_le_card (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q)
    (hα : ∀ m ∈ S, ‖α m‖ ≤ 1) (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (S.card : ℝ) * (Q.card : ℝ) := by
  apply part3LongSlotSignedError_norm_le_of_mass S Q α ρ L U a S.card Q.card hq ha
  · simpa using sum_le_sum (fun m hm => hα m hm)
  · simpa using sum_le_sum (fun q hqQ => hρ q hqQ)

/-- A physical modulus bound on `q` itself.  All primitive moduli up to `D`
are allowed in this elementary long-slot core.  In the manuscript the
one-long alternative has short length times `D` strictly below the complete
scale; no factorization of individual moduli is needed for this branch. -/
theorem part3LongSlotSignedError_norm_le_box (M D L U a : ℕ) (α ρ : ℕ → ℂ)
    (hα : ∀ m ∈ Icc 1 M, ‖α m‖ ≤ 1)
    (hρ : ∀ q ∈ (Icc 1 D).filter (fun q => a.Coprime q), ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError (Icc 1 M)
      ((Icc 1 D).filter (fun q => a.Coprime q)) α ρ L U a‖ ≤
      2 * (M : ℝ) * (D : ℝ) := by
  have hq (q : ℕ) (hqQ : q ∈ (Icc 1 D).filter (fun q => a.Coprime q)) : 0 < q :=
    (mem_Icc.mp (mem_filter.mp hqQ).1).1
  have ha (q : ℕ) (hqQ : q ∈ (Icc 1 D).filter (fun q => a.Coprime q)) : a.Coprime q :=
    (mem_filter.mp hqQ).2
  have hcardNat : ((Icc 1 D).filter (fun q => a.Coprime q)).card ≤ D := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      card_filter_le (Icc 1 D) (fun q => a.Coprime q)
  have hcard : (((Icc 1 D).filter (fun q => a.Coprime q)).card : ℝ) ≤ D := by
    exact_mod_cast hcardNat
  have h := part3LongSlotSignedError_norm_le_card (Icc 1 M)
    ((Icc 1 D).filter (fun q => a.Coprime q)) α ρ L U a hq ha hα hρ
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
  exact h.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

end

end ImbalancedChen
