import ImbalancedChen.ChenQuotientPrimeSource
import ImbalancedChen.RoughSquareException
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact finite geometry for the fifth and sixth Chen harmonic main sums

These are identities for the harmonic main sums over the existing literal
selectors, not identities replacing the original sifted Upsilon counts.
All endpoints and the varying-centre coprimality masks remain unchanged.

The sixth selector is a disjoint-band rectangle. The fifth selector is the
strict ordered half of a square. Multiplicativity of the prime totient is
used only off the diagonal. The artificial tensor diagonal has denominator
(p-1)^2, and its total absolute weight is at most 8 M / A for A >= 2.

This owned finite module has no analytic prime-sum premise or conclusion.
Held source candidate: no Lean or Lake execution was performed here.
-/

namespace ImbalancedChen

noncomputable section
open scoped BigOperators
open Classical

/-- The two original half-open bands form exactly the sixth selector.
In particular equality at the common endpoint belongs to the second band. -/
theorem chenY6PrimeSelector_eq_single_product (N : ℕ) (A H D : ℝ) :
    chenY6PrimeSelector N A H D =
      chenSinglePrimeSelector N A H ×ˢ chenSinglePrimeSelector N H D := by
  ext t
  simp only [chenY6PrimeSelector, chenSinglePrimeSelector,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp, hq⟩, hpA, hpH, hqH, hqD⟩
    exact ⟨⟨hp, hpA, hpH⟩, ⟨hq, hqH, hqD⟩⟩
  · rintro ⟨⟨hp, hpA, hpH⟩, ⟨hq, hqH, hqD⟩⟩
    exact ⟨⟨hp, hq⟩, hpA, hpH, hqH, hqD⟩

/-- The fifth selector is exactly the ordered part of the masked square. -/
theorem chenY5PrimeSelector_eq_single_square_filter (N : ℕ) (A H : ℝ) :
    chenY5PrimeSelector N A H =
      (chenSinglePrimeSelector N A H ×ˢ chenSinglePrimeSelector N A H).filter
        (fun t => t.1 < t.2) := by
  ext t
  rcases t with ⟨p, q⟩
  simp only [chenY5PrimeSelector, chenSinglePrimeSelector,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp, hq⟩, hpA, hpq, hqH⟩
    have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
    exact ⟨⟨⟨hp, hpA, hpqR.trans hqH⟩,
      ⟨hq, hpA.trans hpqR.le, hqH⟩⟩, hpq⟩
  · rintro ⟨⟨⟨hp, hpA, _⟩, ⟨hq, _, hqH⟩⟩, hpq⟩
    exact ⟨⟨hp, hq⟩, hpA, hpq, hqH⟩

/-- Disjointness of the sixth bands supplies the strict prime order. -/
theorem chenY6_single_product_lt {N p q : ℕ} {A H D : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N A H)
    (hq : q ∈ chenSinglePrimeSelector N H D) : p < q := by
  have hpH := (Finset.mem_filter.mp hp).2.2
  have hHq := (Finset.mem_filter.mp hq).2.1
  exact_mod_cast hpH.trans_le hHq

/-- The exact prime totient product formula needs distinct prime labels. -/
theorem chen_prime_pair_totient_cast {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (Nat.totient (p * q) : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq), Nat.cast_mul,
    Nat.totient_prime hp, Nat.totient_prime hq,
    Nat.cast_sub hp.one_lt.le, Nat.cast_sub hq.one_lt.le, Nat.cast_one]

/-- An elementary finite symmetry identity, with the entire diagonal paid.
The kernel may have either sign; positivity is not required for equality. -/
theorem chen_ordered_half_square (S : Finset ℕ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ p ∈ S, ∀ q ∈ S, K p q = K q p) :
    (∑ t ∈ (S ×ˢ S).filter (fun t => t.1 < t.2), K t.1 t.2) =
      (1 / 2 : ℝ) * ((∑ p ∈ S, ∑ q ∈ S, K p q) - ∑ p ∈ S, K p p) := by
  let U := ∑ p ∈ S, ∑ q ∈ S, if p < q then K p q else 0
  let L := ∑ p ∈ S, ∑ q ∈ S, if q < p then K p q else 0
  have hswap : L = U := by
    dsimp [L, U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hpq : p < q
    · simp only [if_pos hpq]
      exact hK q hq p hp
    · simp only [if_neg hpq]
  have hdiag :
      (∑ p ∈ S, ∑ q ∈ S, if p = q then K p p else 0) = ∑ p ∈ S, K p p := by
    apply Finset.sum_congr rfl
    intro p hp
    calc
      _ = if p = p then K p p else 0 :=
        Finset.sum_eq_single_of_mem
          (f := fun q : ℕ => if p = q then K p p else 0) p hp
          (fun q (_hq : q ∈ S) (hqp : q ≠ p) => if_neg (Ne.symm hqp))
      _ = K p p := if_pos rfl
  have hsplit : (∑ p ∈ S, ∑ q ∈ S, K p q) =
      U + L + ∑ p ∈ S, K p p := by
    have hterm (p q : ℕ) : K p q =
        (if p < q then K p q else 0) +
          (if q < p then K p q else 0) + (if p = q then K p p else 0) := by
      rcases lt_trichotomy p q with h | h | h
      · simp [h, not_lt.mpr h.le, h.ne]
      · subst q
        simp
      · simp [h, not_lt.mpr h.le, h.ne']
    calc
      _ = ∑ p ∈ S, ∑ q ∈ S,
          ((if p < q then K p q else 0) +
            (if q < p then K p q else 0) + (if p = q then K p p else 0)) := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_congr rfl (fun q _ => hterm p q)
      _ = U + L + ∑ p ∈ S, ∑ q ∈ S, if p = q then K p p else 0 := by
        simp only [Finset.sum_add_distrib, U, L]
      _ = _ := by rw [hdiag]
  have hupper :
      (∑ t ∈ (S ×ˢ S).filter (fun t => t.1 < t.2), K t.1 t.2) = U := by
    simp only [Finset.sum_filter, Finset.sum_product, U]
  rw [hupper]
  rw [hswap] at hsplit
  linarith

/-- The actual sixth harmonic sum is exactly a tensor of masked bands.
No diagonal term exists, because the first band is strict below H and the
second is inclusive above H. -/
theorem chenY6_totient_sum_eq_tensor (N : ℕ) (A H D : ℝ) (f : ℕ → ℝ) :
    (∑ t ∈ chenY6PrimeSelector N A H D,
      f (t.1 * t.2) / (Nat.totient (t.1 * t.2) : ℝ)) =
      ∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N H D,
        f (p * q) / (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  rw [chenY6PrimeSelector_eq_single_product, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  have hqprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1
  rw [chen_prime_pair_totient_cast hpprime hqprime (chenY6_single_product_lt hp hq).ne]

/-- The fifth harmonic sum is half the full masked tensor square minus
half its artificial diagonal. That diagonal uses (p-1)^2, not phi(p^2). -/
theorem chenY5_totient_sum_eq_half_square_sub_diagonal
    (N : ℕ) (A H : ℝ) (f : ℕ → ℝ) :
    (∑ t ∈ chenY5PrimeSelector N A H,
      f (t.1 * t.2) / (Nat.totient (t.1 * t.2) : ℝ)) =
      (1 / 2 : ℝ) *
        ((∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N A H,
          f (p * q) / (((p : ℝ) - 1) * ((q : ℝ) - 1))) -
          ∑ p ∈ chenSinglePrimeSelector N A H, f (p * p) / ((p : ℝ) - 1) ^ 2) := by
  rw [chenY5PrimeSelector_eq_single_square_filter]
  have hterms :
      (∑ t ∈ (chenSinglePrimeSelector N A H ×ˢ
          chenSinglePrimeSelector N A H).filter (fun t => t.1 < t.2),
        f (t.1 * t.2) / (Nat.totient (t.1 * t.2) : ℝ)) =
      ∑ t ∈ (chenSinglePrimeSelector N A H ×ˢ
          chenSinglePrimeSelector N A H).filter (fun t => t.1 < t.2),
        f (t.1 * t.2) / (((t.1 : ℝ) - 1) * ((t.2 : ℝ) - 1)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨htS, hlt⟩ := Finset.mem_filter.mp ht
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp htS
    have hpprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    have hqprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1
    rw [chen_prime_pair_totient_cast hpprime hqprime hlt.ne]
  rw [hterms]
  simpa only [pow_two] using
    chen_ordered_half_square (chenSinglePrimeSelector N A H)
      (fun p q => f (p * q) / (((p : ℝ) - 1) * ((q : ℝ) - 1)))
      (fun p _ q _ => by rw [Nat.mul_comm p q, mul_comm ((p : ℝ) - 1)])

/-- Separated tensor tests factor into the actual one-prime sums, with
both centre masks retained. This is a finite identity, not a limit input. -/
theorem chen_prime_tensor_separated (N : ℕ) (A B C D : ℝ) (f g : ℕ → ℝ) :
    (∑ p ∈ chenSinglePrimeSelector N A B, ∑ q ∈ chenSinglePrimeSelector N C D,
      (f p * g q) / (((p : ℝ) - 1) * ((q : ℝ) - 1))) =
      (∑ p ∈ chenSinglePrimeSelector N A B, f p / ((p : ℝ) - 1)) *
        (∑ q ∈ chenSinglePrimeSelector N C D, g q / ((q : ℝ) - 1)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem chen_pair_shifted_square_atom {x M v : ℝ}
    (hx : 2 ≤ x) (hM : 0 ≤ M) (hv : |v| ≤ M) :
    |v / (x - 1) ^ 2| ≤ 4 * M / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hrec : 1 / (x - 1) ^ 2 ≤ 4 / x ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hx1 2) (pow_pos hx0 2)).mpr
    nlinarith [sq_nonneg (x - 2)]
  rw [abs_div, abs_of_pos (pow_pos hx1 2)]
  calc
    _ ≤ M / (x - 1) ^ 2 := div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ = M * (1 / (x - 1) ^ 2) := by ring
    _ ≤ M * (4 / x ^ 2) := mul_le_mul_of_nonneg_left hrec hM
    _ = _ := by ring

/-- Finite shifted-square tail with a real inclusive lower endpoint.
It reuses the owned telescoping integer square tail; no prime counting or
infinite-series theorem enters. The finite upper cap can be arbitrary. -/
theorem chen_pair_diagonal_tail_bound (N : ℕ) (T : Finset ℕ) (g : ℕ → ℝ)
    {A M : ℝ} (hA : 2 ≤ A) (hM : 0 ≤ M)
    (hT : ∀ p ∈ T, A ≤ (p : ℝ) ∧ p ≤ N)
    (hg : ∀ p ∈ T, |g p| ≤ M) :
    |∑ p ∈ T, g p / ((p : ℝ) - 1) ^ 2| ≤ 8 * M / A := by
  have hceil : 2 ≤ Nat.ceil A :=
    Nat.add_one_le_ceil_iff.mpr (by simpa using (show 1 < A by linarith))
  have hsub : T ⊆ Finset.Icc (Nat.ceil A) N := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (hT p hp).1, (hT p hp).2⟩
  have htail : (∑ p ∈ T, 1 / (p : ℝ) ^ 2) ≤ 2 / A := by
    have hs : (∑ p ∈ T, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ Finset.Icc (Nat.ceil A) N, 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hrec : 1 / (A - 1) ≤ 2 / A := by
      apply (div_le_div_iff₀ (by linarith : 0 < A - 1) (by linarith : 0 < A)).mpr
      linarith
    exact hs.trans ((reciprocalSquare_Icc_tail_le N hceil).trans
      ((div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : 0 < A - 1) (sub_le_sub_right (Nat.le_ceil A) 1)).trans hrec))
  calc
    _ ≤ ∑ p ∈ T, |g p / ((p : ℝ) - 1) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ T, 4 * M / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact chen_pair_shifted_square_atom (hA.trans (hT p hp).1) hM (hg p hp)
    _ = (4 * M) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (4 * M) * (2 / A) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- The exact artificial diagonal in the fifth-term tensor identity has
size at most 8 M / A, uniformly in the centre and the strict upper cap. -/
theorem chenY5_tensor_diagonal_bound (N : ℕ) (H : ℝ) (f : ℕ → ℝ)
    {A M : ℝ} (hA : 2 ≤ A) (hM : 0 ≤ M)
    (hf : ∀ p ∈ chenSinglePrimeSelector N A H, |f (p * p)| ≤ M) :
    |∑ p ∈ chenSinglePrimeSelector N A H, f (p * p) / ((p : ℝ) - 1) ^ 2| ≤
      8 * M / A := by
  apply chen_pair_diagonal_tail_bound N (chenSinglePrimeSelector N A H)
    (fun p => f (p * p)) hA hM _ hf
  intro p hp
  obtain ⟨hpN, hpA, _⟩ := Finset.mem_filter.mp hp
  exact ⟨hpA, (mem_chenAdditivePrimeCarrier.mp hpN).1.le⟩

/-- Consequently, replacing the ordered fifth harmonic sum by half its
full tensor square costs at most 4 M / A. -/
theorem chenY5_half_square_error_bound (N : ℕ) (H : ℝ) (f : ℕ → ℝ)
    {A M : ℝ} (hA : 2 ≤ A) (hM : 0 ≤ M)
    (hf : ∀ p ∈ chenSinglePrimeSelector N A H, |f (p * p)| ≤ M) :
    |(∑ t ∈ chenY5PrimeSelector N A H,
        f (t.1 * t.2) / (Nat.totient (t.1 * t.2) : ℝ)) -
      (1 / 2 : ℝ) *
        (∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N A H,
          f (p * q) / (((p : ℝ) - 1) * ((q : ℝ) - 1)))| ≤ 4 * M / A := by
  rw [chenY5_totient_sum_eq_half_square_sub_diagonal]
  have hid (s d : ℝ) : (1 / 2 : ℝ) * (s - d) - (1 / 2 : ℝ) * s =
      -((1 / 2 : ℝ) * d) := by ring
  rw [hid, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (8 * M / A) :=
      mul_le_mul_of_nonneg_left (chenY5_tensor_diagonal_bound N H f hA hM hf)
        (by norm_num)
    _ = _ := by ring

/-- The logarithmic product coordinate equals the sum of the two prime
coordinates. No assumption on N is necessary for this finite identity. -/
theorem chen_prime_log_product_coordinate (N : ℕ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Real.log ((p * q : ℕ) : ℝ) / Real.log (N : ℝ) =
      Real.log (p : ℝ) / Real.log (N : ℝ) +
        Real.log (q : ℝ) / Real.log (N : ℝ) := by
  rw [Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero),
    add_div]

/-- The literal sixth logarithmic main sum, ready for a continuous-test
rectangle theorem. This is only the exact finite bridge. -/
theorem chenY6_log_totient_sum_eq_tensor (N : ℕ) (A H D : ℝ) (F : ℝ → ℝ) :
    (∑ t ∈ chenY6PrimeSelector N A H D,
      F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
        (Nat.totient (t.1 * t.2) : ℝ)) =
      ∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N H D,
        F (Real.log (p : ℝ) / Real.log (N : ℝ) +
          Real.log (q : ℝ) / Real.log (N : ℝ)) /
            (((p : ℝ) - 1) * ((q : ℝ) - 1)) := by
  rw [chenY6_totient_sum_eq_tensor N A H D
    (fun n : ℕ => F (Real.log (n : ℝ) / Real.log (N : ℝ)))]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [chen_prime_log_product_coordinate N
    (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1]

/-- The literal fifth logarithmic main sum retains the factor one half
and the correct artificial diagonal F(2 log p / log N)/(p-1)^2. -/
theorem chenY5_log_totient_sum_eq_half_square_sub_diagonal
    (N : ℕ) (A H : ℝ) (F : ℝ → ℝ) :
    (∑ t ∈ chenY5PrimeSelector N A H,
      F (Real.log ((t.1 * t.2 : ℕ) : ℝ) / Real.log (N : ℝ)) /
        (Nat.totient (t.1 * t.2) : ℝ)) =
      (1 / 2 : ℝ) *
        ((∑ p ∈ chenSinglePrimeSelector N A H, ∑ q ∈ chenSinglePrimeSelector N A H,
          F (Real.log (p : ℝ) / Real.log (N : ℝ) +
            Real.log (q : ℝ) / Real.log (N : ℝ)) /
              (((p : ℝ) - 1) * ((q : ℝ) - 1))) -
          ∑ p ∈ chenSinglePrimeSelector N A H,
            F (2 * (Real.log (p : ℝ) / Real.log (N : ℝ))) / ((p : ℝ) - 1) ^ 2) := by
  rw [chenY5_totient_sum_eq_half_square_sub_diagonal N A H
    (fun n : ℕ => F (Real.log (n : ℝ) / Real.log (N : ℝ)))]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [chen_prime_log_product_coordinate N
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
      (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hq).1).2.1]
  · apply Finset.sum_congr rfl
    intro p hp
    have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
    rw [chen_prime_log_product_coordinate N hprime hprime, ← two_mul]

end

end ImbalancedChen
