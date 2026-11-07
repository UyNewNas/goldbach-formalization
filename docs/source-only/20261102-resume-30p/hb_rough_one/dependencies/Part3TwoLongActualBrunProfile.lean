import Mathlib
import ImbalancedChen.Part3TwoLongBrunComplexGap

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original manuscript (B1), (E2), (E3), (I). The finite set P represents
exactly the chart primes p <= z. Its filter by p | n counts the distinct
small prime factors of n. The polynomial below is the actual coefficient
sum after grouping squarefree divisors d | gcd(n,P) by omega(d). The
even order is h = 2*j; the odd lower order is h+1.

The analytic B2 Bernoulli estimate, one-variable progression formula E1,
and primitive double-Poisson/Weil bound P1--P3 are separate boundaries.
This source makes no rough-product estimate an input.
-/

namespace ImbalancedChen.Part3.TwoLongActualBrunProfile

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongBrunComplexGap

noncomputable section

/-- Number of distinct chart primes dividing n. The parameter P is the
actual finite prime alphabet up to the chart threshold. -/
def smallDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter (fun p => p ∣ n)).card

/-- The alternating divisor polynomial grouped by cardinality. Its kth
term counts the k-element squarefree divisors from P that divide n. -/
def brunPolynomial (P : Finset ℕ) (n order : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (order + 1),
    (-1 : ℤ) ^ k * ((smallDivisorCount P n).choose k : ℤ)

def brunUpper (j : ℕ) (P : Finset ℕ) (n : ℕ) : ℤ :=
  brunPolynomial P n (2 * j)

def brunLower (j : ℕ) (P : Finset ℕ) (n : ℕ) : ℤ :=
  brunPolynomial P n (2 * j + 1)

def roughIndicator (P : Finset ℕ) (n : ℕ) : ℤ :=
  if smallDivisorCount P n = 0 then 1 else 0

/-- The even Brun polynomial is the nonnegative binomial coefficient
when n has at least one chart prime divisor. -/
theorem brunUpper_eval (j : ℕ) (P : Finset ℕ) (n : ℕ) :
    brunUpper j P n =
      if smallDivisorCount P n = 0 then 1
      else (((smallDivisorCount P n - 1).choose (2 * j) : ℕ) : ℤ) := by
  unfold brunUpper brunPolynomial
  cases hs : smallDivisorCount P n with
  | zero =>
      simp [hs]
  | succ t =>
      simp only [hs, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [Int.alternating_sum_range_choose_eq_choose]
      simp [pow_mul]

/-- The odd Brun polynomial can be negative, and its exact value is a
negative binomial coefficient on integers with a small prime divisor. -/
theorem brunLower_eval (j : ℕ) (P : Finset ℕ) (n : ℕ) :
    brunLower j P n =
      if smallDivisorCount P n = 0 then 1
      else -(((smallDivisorCount P n - 1).choose (2 * j + 1) : ℕ) : ℤ) := by
  unfold brunLower brunPolynomial
  cases hs : smallDivisorCount P n with
  | zero =>
      simp [hs]
  | succ t =>
      simp only [hs, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [Int.alternating_sum_range_choose_eq_choose]
      simp [pow_add, pow_mul]

/-- The exact B1 gap is choose(s,h+1), including s=0. -/
theorem brunGap_eq_choose (j : ℕ) (P : Finset ℕ) (n : ℕ) :
    brunUpper j P n - brunLower j P n =
      ((smallDivisorCount P n).choose (2 * j + 1) : ℤ) := by
  rw [brunUpper_eval, brunLower_eval]
  cases hs : smallDivisorCount P n with
  | zero =>
      simp [hs]
  | succ t =>
      simp only [hs, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      rw [Nat.choose_succ_succ]
      push_cast
      ring

/-- The literal even/odd evaluations satisfy the Bonferroni pointwise
sandwich required by E2. No sign is imposed on the odd polynomial. -/
theorem brunPointwiseSandwich (j : ℕ) (P : Finset ℕ) (n : ℕ) :
    brunLower j P n ≤ roughIndicator P n ∧
      roughIndicator P n ≤ brunUpper j P n ∧
      0 ≤ brunUpper j P n := by
  rw [brunUpper_eval, brunLower_eval]
  cases hs : smallDivisorCount P n with
  | zero =>
      simp [roughIndicator, hs]
  | succ t =>
      simp [roughIndicator, hs]

/-- The actual two-long product gap at two integers, with the chart
polynomials and their exact gap substituted into the phase-one lemma. -/
theorem actualTwoLongSandwich (j : ℕ) (P : Finset ℕ) (n₁ n₂ : ℕ) :
    0 ≤ (brunUpper j P n₁ : ℝ) * (brunUpper j P n₂ : ℝ) -
      (roughIndicator P n₁ : ℝ) * (roughIndicator P n₂ : ℝ) ∧
    (brunUpper j P n₁ : ℝ) * (brunUpper j P n₂ : ℝ) -
      (roughIndicator P n₁ : ℝ) * (roughIndicator P n₂ : ℝ)
      ≤ ((smallDivisorCount P n₁).choose (2 * j + 1) : ℝ) *
          (brunUpper j P n₂ : ℝ) +
        (brunUpper j P n₁ : ℝ) *
          ((smallDivisorCount P n₂).choose (2 * j + 1) : ℝ) := by
  obtain ⟨hl₁, hu₁, _⟩ := brunPointwiseSandwich j P n₁
  obtain ⟨hl₂, hu₂, _⟩ := brunPointwiseSandwich j P n₂
  have hr₁ : 0 ≤ (roughIndicator P n₁ : ℝ) := by
    unfold roughIndicator
    split_ifs <;> norm_num
  have hr₂ : 0 ≤ (roughIndicator P n₂ : ℝ) := by
    unfold roughIndicator
    split_ifs <;> norm_num
  have h := twoLongSandwichFromLower
    (roughIndicator P n₁ : ℝ) (roughIndicator P n₂ : ℝ)
    (brunUpper j P n₁ : ℝ) (brunUpper j P n₂ : ℝ)
    (brunLower j P n₁ : ℝ) (brunLower j P n₂ : ℝ)
    hr₁ hr₂ (by exact_mod_cast hl₁) (by exact_mod_cast hl₂)
    (by exact_mod_cast hu₁) (by exact_mod_cast hu₂)
  simpa only [← Int.cast_sub, brunGap_eq_choose, Int.cast_natCast] using h

/-- Real-valued data passed to the complex discrepancy reduction. -/
theorem brunRealBounds (j : ℕ) (P : Finset ℕ) (n : ℕ) :
    0 ≤ (roughIndicator P n : ℝ) ∧
      (roughIndicator P n : ℝ) ≤ (brunUpper j P n : ℝ) ∧
      (brunUpper j P n : ℝ) - (roughIndicator P n : ℝ) ≤
        ((smallDivisorCount P n).choose (2 * j + 1) : ℝ) := by
  obtain ⟨hl, hu, _⟩ := brunPointwiseSandwich j P n
  have hr : 0 ≤ (roughIndicator P n : ℝ) := by
    unfold roughIndicator
    split_ifs <;> norm_num
  have hgap : brunUpper j P n - roughIndicator P n ≤
      ((smallDivisorCount P n).choose (2 * j + 1) : ℤ) := by
    rw [← brunGap_eq_choose]
    linarith
  exact ⟨hr, by exact_mod_cast hu, by exact_mod_cast hgap⟩

/-- The literal complex separated profiles and short coefficient enter
only through their product. The right side uses positive Brun gaps;
the counting and exact-mean functionals are applied after this pointwise
bound, as in manuscript E3. -/
theorem actualComplexProfileGap
    {ι : Type*} (S : Finset ι) (j : ℕ) (P : Finset ℕ)
    (n₁ n₂ : ι → ℕ) (short : ι → ℂ) (f g : ℕ → ℂ) :
    ‖∑ i ∈ S, (short i * f (n₁ i) * g (n₂ i)) *
        (((brunUpper j P (n₁ i) : ℝ) *
            (brunUpper j P (n₂ i) : ℝ) -
          (roughIndicator P (n₁ i) : ℝ) *
            (roughIndicator P (n₂ i) : ℝ) : ℝ) : ℂ)‖
      ≤ ∑ i ∈ S, ‖short i * f (n₁ i) * g (n₂ i)‖ *
        (((smallDivisorCount P (n₁ i)).choose (2 * j + 1) : ℝ) *
          (brunUpper j P (n₂ i) : ℝ) +
         (brunUpper j P (n₁ i) : ℝ) *
          ((smallDivisorCount P (n₂ i)).choose (2 * j + 1) : ℝ)) := by
  apply complexWeightedTwoLongGap S
    (fun i => short i * f (n₁ i) * g (n₂ i))
    (fun i => (roughIndicator P (n₁ i) : ℝ))
    (fun i => (roughIndicator P (n₂ i) : ℝ))
    (fun i => (brunUpper j P (n₁ i) : ℝ))
    (fun i => (brunUpper j P (n₂ i) : ℝ))
    (fun i => ((smallDivisorCount P (n₁ i)).choose (2 * j + 1) : ℝ))
    (fun i => ((smallDivisorCount P (n₂ i)).choose (2 * j + 1) : ℝ))
  · intro i hi
    exact (brunRealBounds j P (n₁ i)).1
  · intro i hi
    exact (brunRealBounds j P (n₂ i)).1
  · intro i hi
    exact (brunRealBounds j P (n₁ i)).2.1
  · intro i hi
    exact (brunRealBounds j P (n₂ i)).2.1
  · intro i hi
    exact (brunRealBounds j P (n₁ i)).2.2
  · intro i hi
    exact (brunRealBounds j P (n₂ i)).2.2

/-- The endpoint-strip bound at two actual integers. Each sharp interval
is handled separately; the rough product is bounded by the explicit
upper Brun product. For a tiny interval, choose the smooth profile zero
and let its one positive strip cover the interval. -/
theorem actualSharpIndividualStrip
    (j : ℕ) (P I₁ I₂ : Finset ℕ) (n₁ n₂ : ℕ)
    (h₁ h₂ k₁ k₂ : ℕ → ℝ)
    (hh₁ : 0 ≤ h₁ n₁) (hh₁' : h₁ n₁ ≤ 1)
    (hh₂ : 0 ≤ h₂ n₂) (hh₂' : h₂ n₂ ≤ 1)
    (hk₁ : |(if n₁ ∈ I₁ then (1 : ℝ) else 0) - h₁ n₁| ≤ k₁ n₁)
    (hk₂ : |(if n₂ ∈ I₂ then (1 : ℝ) else 0) - h₂ n₂| ≤ k₂ n₂) :
    |(if n₁ ∈ I₁ then (1 : ℝ) else 0) *
        (if n₂ ∈ I₂ then (1 : ℝ) else 0) - h₁ n₁ * h₂ n₂| *
      ((roughIndicator P n₁ : ℝ) * (roughIndicator P n₂ : ℝ))
      ≤ (k₁ n₁ + k₂ n₂) *
        ((brunUpper j P n₁ : ℝ) * (brunUpper j P n₂ : ℝ)) := by
  have hi₁ : 0 ≤ (if n₁ ∈ I₁ then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hi₁' : (if n₁ ∈ I₁ then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hi₂ : 0 ≤ (if n₂ ∈ I₂ then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hi₂' : (if n₂ ∈ I₂ then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hstrip := individualIntervalProductStrip
    (if n₁ ∈ I₁ then (1 : ℝ) else 0)
    (if n₂ ∈ I₂ then (1 : ℝ) else 0)
    (h₁ n₁) (h₂ n₂) (k₁ n₁) (k₂ n₂)
    hi₁ hi₁' hi₂ hi₂' hh₁ hh₁' hh₂ hh₂' hk₁ hk₂
  have hrough₁ := (brunRealBounds j P n₁).1
  have hrough₂ := (brunRealBounds j P n₂).1
  have hrough : 0 ≤ (roughIndicator P n₁ : ℝ) *
      (roughIndicator P n₂ : ℝ) := mul_nonneg hrough₁ hrough₂
  have hru := (actualTwoLongSandwich j P n₁ n₂).1
  have hstripsNonneg : 0 ≤ k₁ n₁ + k₂ n₂ :=
    le_trans (abs_nonneg _) hstrip
  calc
    _ ≤ (k₁ n₁ + k₂ n₂) *
        ((roughIndicator P n₁ : ℝ) * (roughIndicator P n₂ : ℝ)) :=
      mul_le_mul_of_nonneg_right hstrip hrough
    _ ≤ (k₁ n₁ + k₂ n₂) *
        ((brunUpper j P n₁ : ℝ) * (brunUpper j P n₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left (sub_nonneg.mp hru) hstripsNonneg

/-- The actual exact coprime mean in a fixed pair of individual intervals.
The short coefficient is deliberately outside: for a fixed short m coprime
to q it multiplies this expression, while for nonunit m both discrepancy
terms vanish. -/
def exactCoprimePairMean (q : ℕ) (I₁ I₂ : Finset ℕ)
    (F G : ℕ → ℝ) (w₁ w₂ : ℕ → ℝ) : ℝ :=
  (Nat.totient q : ℝ)⁻¹ *
    (∑ n ∈ I₁.filter (fun n => Nat.Coprime n q), F n * w₁ n) *
    (∑ n ∈ I₂.filter (fun n => Nat.Coprime n q), G n * w₂ n)

/-- The B1 product gap under the exact mean, including its 1/phi(q)
normalization and separate coprimality filters. B2 and E1 are applied
only to the one-variable sums on the right, not to an unrestricted mean. -/
theorem actualExactCoprimeMeanGap
    (j q : ℕ) (P I₁ I₂ : Finset ℕ)
    (F G : ℕ → ℝ) (hq : 0 < q)
    (hF : ∀ n ∈ I₁, 0 ≤ F n)
    (hG : ∀ n ∈ I₂, 0 ≤ G n) :
    exactCoprimePairMean q I₁ I₂ F G
      (fun n => (brunUpper j P n : ℝ))
      (fun n => (brunUpper j P n : ℝ)) -
    exactCoprimePairMean q I₁ I₂ F G
      (fun n => (roughIndicator P n : ℝ))
      (fun n => (roughIndicator P n : ℝ))
    ≤ (Nat.totient q : ℝ)⁻¹ *
      ((∑ n ∈ I₁.filter (fun n => Nat.Coprime n q),
          F n * ((smallDivisorCount P n).choose (2 * j + 1) : ℝ)) *
        (∑ n ∈ I₂.filter (fun n => Nat.Coprime n q),
          G n * (brunUpper j P n : ℝ)) +
       (∑ n ∈ I₁.filter (fun n => Nat.Coprime n q),
          F n * (brunUpper j P n : ℝ)) *
        (∑ n ∈ I₂.filter (fun n => Nat.Coprime n q),
          G n * ((smallDivisorCount P n).choose (2 * j + 1) : ℝ))) := by
  let S := I₁.filter (fun n => Nat.Coprime n q)
  let T := I₂.filter (fun n => Nat.Coprime n q)
  have hF' : ∀ n ∈ S, 0 ≤ F n := by
    intro n hn
    exact hF n (Finset.mem_filter.mp hn).1
  have hG' : ∀ n ∈ T, 0 ≤ G n := by
    intro n hn
    exact hG n (Finset.mem_filter.mp hn).1
  have hmean := exactCoprimeMeanGap S T F G
    (fun n => (roughIndicator P n : ℝ))
    (fun n => (brunUpper j P n : ℝ))
    (fun n => ((smallDivisorCount P n).choose (2 * j + 1) : ℝ))
    (fun n => (roughIndicator P n : ℝ))
    (fun n => (brunUpper j P n : ℝ))
    (fun n => ((smallDivisorCount P n).choose (2 * j + 1) : ℝ))
    hF' hG'
    (by intro n hn; exact (brunRealBounds j P n).1)
    (by intro n hn; exact (brunRealBounds j P n).1)
    (by intro n hn; exact (brunRealBounds j P n).2.1)
    (by intro n hn; exact (brunRealBounds j P n).2.1)
    (by intro n hn; exact (brunRealBounds j P n).2.2)
    (by intro n hn; exact (brunRealBounds j P n).2.2)
  have hphi : 0 ≤ (Nat.totient q : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold exactCoprimePairMean
  dsimp [S, T] at hmean
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [Finset.sum_mul_sum, ← Finset.sum_sub_distrib] using hmean) hphi

end

end ImbalancedChen.Part3.TwoLongActualBrunProfile
