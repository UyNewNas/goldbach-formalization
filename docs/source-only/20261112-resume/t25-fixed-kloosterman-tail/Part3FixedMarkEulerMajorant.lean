import ImbalancedChen.Part3FixedMarkPrimeMoment
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic

noncomputable section
namespace ImbalancedChen.Part3.FixedMarkTail
open Classical Finset OriginalSmoothPoissonTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def localCost (m : ℤ) (p k : ℕ) : ℝ :=
  if k = 1 ∧ ¬(p : ℤ) ∣ m then 2 * (p : ℝ) ^ (3/4 : ℝ) else (p : ℝ)^k

def majorant (m : ℤ) (d : ℕ) : ℝ :=
  d.factorization.prod (localCost m)

theorem majorant_nonneg (m : ℤ) (d : ℕ) : 0 ≤ majorant m d := by
  unfold majorant Finsupp.prod
  exact Finset.prod_nonneg (by intros; unfold localCost; split_ifs <;> positivity)

theorem majorant_coprime (m : ℤ) {q r : ℕ} (h : q.Coprime r) :
    majorant m (q*r) = majorant m q * majorant m r := by
  unfold majorant
  rw [Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors (localCost m)]

theorem majorant_prime_pow (m : ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    majorant m (p^k) = localCost m p k := by
  rw [majorant, hp.factorization_pow, Finsupp.prod_single_index (by simp [localCost])]

theorem prime_physical_le {p : ℕ} (hp : p.Prime) (m n : ℤ)
    (hm : ¬(p : ℤ) ∣ m) :
    ‖kloosterman p m n‖ ≤ 2*(p : ℝ)^(3/4:ℝ) := by
  have h := prime_physical_fourth_le hp m n (mt (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp hm)
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hf : ((p : ℝ)^(3/4:ℝ))^4 = (p : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hp0]
    norm_num
  by_contra! hh
  have hh' := pow_lt_pow_left₀ hh (by positivity : 0 ≤ 2 * (p : ℝ)^(3/4:ℝ)) (by decide : (4:ℕ) ≠ 0)
  rw [mul_pow, hf] at hh'
  nlinarith [pow_nonneg hp0 3]

theorem physical_le_majorant (m : ℤ) (d : ℕ) :
    ∀ n : ℤ, ‖kloosterman d m n‖ ≤ majorant m d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro n
    rw [majorant_prime_pow m hp, localCost]
    split_ifs with h
    · rcases h with ⟨rfl,hm⟩
      simpa using prime_physical_le hp m n hm
    · exact_mod_cast kloosterman_norm_le (p^k) m n
  | zero =>
    intro n
    exact (kloosterman_norm_le 0 m n).trans (by simp [majorant])
  | one =>
    intro n
    exact (kloosterman_norm_le 1 m n).trans (by simp [majorant])
  | coprime q r hq hr hc ihq ihr =>
    intro n
    letI : NeZero q := ⟨by omega⟩
    letI : NeZero r := ⟨by omega⟩
    let u := Nat.gcdB q r
    let v := Nat.gcdA q r
    have hu : IsUnit (u : ZMod q) :=
      .of_mul_eq_one _ (CoprimeCRTSourceOnly.canonical_crt_twist_left hc)
    have hv : IsUnit (v : ZMod r) :=
      .of_mul_eq_one _ (CoprimeCRTSourceOnly.canonical_crt_twist_right hc)
    rw [majorant_coprime m hc, CoprimeCRTSourceOnly.kloosterman_coprime_crt hc, norm_mul]
    change ‖kloosterman q (u*m) (u*n)‖ * ‖kloosterman r (v*m) (v*n)‖ ≤ _
    rw [mul_comm u m, mul_comm v m, kloosterman_unit_scaling m (u*n) u hu,
      kloosterman_unit_scaling m (v*n) v hv]
    exact mul_le_mul (ihq _) (ihr _) (norm_nonneg _) (majorant_nonneg _ _)

/-- Both integer arguments may depend on the modulus, provided the first
is a unit multiple of a single fixed integer. -/
theorem physical_unit_le_majorant (m n u : ℤ) {d : ℕ} [NeZero d]
    (hu : IsUnit (u : ZMod d)) :
    ‖kloosterman d (m*u) n‖ ≤ majorant m d := by
  rw [kloosterman_unit_scaling m n u hu]
  exact physical_le_majorant _ _ _

def price (m : ℤ) (δ : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0 else majorant m d * (d : ℝ) ^ (-2+δ)

theorem price_nonneg (m : ℤ) (δ : ℝ) (d : ℕ) : 0 ≤ price m δ d := by
  unfold price
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (majorant_nonneg _ _) (Real.rpow_nonneg (by positivity) _)

theorem price_coprime (m : ℤ) (δ : ℝ) {q r : ℕ} (hc : q.Coprime r) :
    price m δ (q*r) = price m δ q * price m δ r := by
  by_cases hq : q = 0
  · simp [hq, price]
  by_cases hr : r = 0
  · simp [hr, price]
  simp only [price, if_neg hq, if_neg hr, if_neg (mul_ne_zero hq hr), majorant_coprime m hc,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg r)]
  ring

theorem price_zero (m : ℤ) (δ : ℝ) : price m δ 0 = 0 := by simp [price]
theorem price_one (m : ℤ) (δ : ℝ) : price m δ 1 = 1 := by simp [price, majorant]

theorem price_prime (m : ℤ) (δ : ℝ) {p : ℕ} (hp : p.Prime) :
    price m δ p = if (p:ℤ) ∣ m then (p:ℝ)^(-1+δ) else 2*(p:ℝ)^(-5/4+δ) := by
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hc := majorant_prime_pow m hp 1
  rw [pow_one] at hc
  simp only [price, if_neg hp.ne_zero, hc, localCost, true_and, pow_one]
  by_cases h : (p:ℤ) ∣ m
  · simp only [h, not_true_eq_false, if_false, if_true]
    conv_lhs => lhs; rw [← Real.rpow_one (p:ℝ)]
    rw [← Real.rpow_add hpR]
    congr 1 <;> ring
  · simp only [h, not_false_eq_true, if_true, if_false]
    rw [mul_assoc, ← Real.rpow_add hpR]
    congr 2 <;> ring

theorem price_higher (m : ℤ) (δ : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    price m δ (p^(k+2)) = ((p:ℝ)^(-1+δ))^(k+2) := by
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  simp only [price, if_neg (pow_ne_zero _ hp.ne_zero), majorant_prime_pow m hp, localCost,
    if_neg (show ¬(k+2=1 ∧ ¬(p:ℤ)∣m) by rintro ⟨h,_⟩; omega), Nat.cast_pow]
  rw [← Real.rpow_natCast_mul hpR.le, ← Real.rpow_mul_natCast hpR.le,
    ← Real.rpow_natCast (p:ℝ) (k+2), ← Real.rpow_add hpR]
  congr 1
  ring

end ImbalancedChen.Part3.FixedMarkTail
