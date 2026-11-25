import ImbalancedChen.Part3CommonPoisson

/-!
# Uniform progression error for the actual common cutoff

The telescoping Fourier majorant below is a namespace-local extraction of
LiLiuPrereqFouvryPoisson.lean from fixed goldbach commit
09b97db5764ade1246bfb77206baa1b124760958. It is applied to the local
Schwartz cutoff and the already proved local Poisson identity. Thus the
normalization is exactly CommonSmoothCutoff.cutoffMass throughout.

The constant precedes every positive scale, every positive modulus, every
integer residue and every finite support-containing carrier. In particular
no comparison between the modulus and the smoothing scale is required.
There is no imported integral mass or unproved normalization conversion.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical
open scoped BigOperators SchwartzMap FourierTransform

namespace CommonSmoothCutoff

theorem poisson_decay_step {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t / (1 + t * (n + 1)) ^ 2 ≤
      1 / (1 + t * n) - 1 / (1 + t * (n + 1)) := by
  have hA : 0 < 1 + t * (n : ℝ) := by positivity
  have hB : 0 < 1 + t * ((n : ℝ) + 1) := by positivity
  calc
    _ ≤ t / ((1 + t * n) * (1 + t * (n + 1))) := by
      apply div_le_div_of_nonneg_left ht.le (mul_pos hA hB)
      nlinarith
    _ = _ := by field_simp; ring

theorem poisson_decay_sum_range_le {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ Finset.range N, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (1 / (1 + t * (n : ℝ)) - 1 / (1 + t * ((n : ℝ) + 1))) :=
      Finset.sum_le_sum (fun n _ ↦ poisson_decay_step ht n)
    _ = 1 - 1 / (1 + t * (N : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, div_one]
        using Finset.sum_range_sub' (fun n : ℕ ↦ 1 / (1 + t * (n : ℝ))) N
    _ ≤ 1 := sub_le_self _ (by positivity)

theorem poisson_decay_summable_nat {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2) :=
  summable_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

theorem poisson_decay_tsum_nat_le {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, t / (1 + t * ((n : ℝ) + 1)) ^ 2) ≤ 1 :=
  Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) (poisson_decay_sum_range_le ht)

def poissonNonzeroDecay (t : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 0 else t / (1 + |t * h|) ^ 2

theorem poissonNonzeroDecay_summable_tsum_le {t : ℝ} (ht : 0 < t) :
    Summable (poissonNonzeroDecay t) ∧ (∑' h : ℤ, poissonNonzeroDecay t h) ≤ 2 := by
  let a : ℕ → ℝ := fun n ↦ t / (1 + t * ((n : ℝ) + 1)) ^ 2
  have ha : Summable a := poisson_decay_summable_nat ht
  have hbound : (∑' n : ℕ, a n) ≤ 1 := poisson_decay_tsum_nat_le ht
  have hnat (n : ℕ) : poissonNonzeroDecay t ((n : ℤ) + 1) = a n := by
    have hn : (n : ℤ) + 1 ≠ 0 := by omega
    simp [poissonNonzeroDecay, hn, abs_mul, abs_of_pos ht,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), a]
  have hneg (n : ℕ) : poissonNonzeroDecay t (-((n : ℤ) + 1)) = a n := by
    simpa only [poissonNonzeroDecay, neg_eq_zero, Int.cast_neg, mul_neg, abs_neg]
      using hnat n
  have hpos : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (n : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha
  have hminus : Summable (fun n : ℕ ↦ poissonNonzeroDecay t (-((n : ℤ) + 1))) := by
    simpa only [hneg] using ha
  refine ⟨hpos.of_nat_of_neg_add_one hminus, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hminus, tsum_eq_zero_add']
  · simp only [Nat.cast_zero, show poissonNonzeroDecay t 0 = 0 from rfl,
      zero_add, Nat.cast_add, Nat.cast_one, hnat, hneg]
    linarith
  · simpa only [Nat.cast_add, Nat.cast_one, hnat] using ha

/-- The actual local nonzero Fourier series has a uniform absolute bound. -/
theorem poissonNonzeroFrequency_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      ‖∑' h : ℤ, poissonNonzeroFrequency t x h‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) 2
  refine ⟨2 * C, by positivity, fun t ht x ↦ ?_⟩
  obtain ⟨hmajor, hsum⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) :
      ‖poissonNonzeroFrequency t x h‖ ≤ C * poissonNonzeroDecay t h := by
    by_cases hh : h = 0
    · simp [poissonNonzeroFrequency, poissonNonzeroDecay, hh]
    · simp only [poissonNonzeroFrequency, poissonNonzeroDecay, if_neg hh,
        norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        fourier_apply, Circle.norm_coe, mul_one]
      calc
        _ ≤ t * (C / (1 + |t * h|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hdecay (t * h)) ht.le
        _ = _ := by ring
  have hnorm := poissonNonzeroFrequency_summable_norm ht x
  apply (norm_tsum_le_tsum_norm hnorm).trans
  calc
    _ ≤ ∑' h : ℤ, C * poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint (hmajor.mul_left C)
    _ = C * ∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hsum hC.le
    _ = 2 * C := by ring

/-- Universal O(1) error using the local Fourier-zero mass and finite carrier. -/
theorem scaledDyadicCutoff_finset_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, 0 < q → ∀ b : ℤ,
      |(∑ m ∈ S, if Int.ModEq q (m : ℤ) b then scaledDyadicCutoff M m else 0) -
          (M / q) * cutoffMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := poissonNonzeroFrequency_uniform
  refine ⟨C, hC, fun M hM S hS q hq b ↦ ?_⟩
  rw [scaledDyadicCutoff_finset_progression_eq_main_add_fourier hM S hS hq b,
    add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans
    (hbound (M / q) (div_pos hM (by exact_mod_cast hq)) ((b : ℝ) / q))

theorem scaledDyadicCutoff_finset_multiples_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, 0 < q →
      |(∑ m ∈ S, if q ∣ m then scaledDyadicCutoff M m else 0) -
          (M / q) * cutoffMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS q hq ↦ ?_⟩
  simpa only [Int.modEq_zero_iff_dvd, Int.natCast_dvd_natCast]
    using hbound M hM S hS q hq 0

end CommonSmoothCutoff

end

end ImbalancedChen.Part3
